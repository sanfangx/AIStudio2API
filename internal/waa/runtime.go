package waa

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/Mag1cFall/AIStudio2API/internal/waa/prooftime"
	"github.com/Mag1cFall/AIStudio2API/internal/waa/rhythm"
	"github.com/Mag1cFall/goja"
)

// Options 定义一份 BotGuard VM 的解释器、宿主现场与网络依赖
type Options struct {
	Challenge   Challenge
	Interpreter string
	Profile     Profile
	LoadImage   func(string) bool
	// LoadFrame 以浏览器 iframe 导航形状载入地址，返回是否收到文档响应
	LoadFrame func(string) bool
	// Pointer 是页面上可信指针与焦点所在的位置，同一页面先后新建的 VM 共用；为 nil 时按刚载入的页面
	Pointer *Pointer
	// Rhythm 是账户点击与粘贴的事件节奏
	Rhythm rhythm.Rhythm
}

// Pointer 是页面上可信指针与焦点所在的位置
type Pointer struct {
	mu sync.Mutex
	// at 是指针所在的位置（prompt、run、turn、rerun、content、result、submit），指针还没进入页面时为空
	at string
	// focus 是焦点所在的位置（prompt、run、rerun、result、submit），焦点不在页面元素上时为空
	focus string
	// rounds 是最近一次 Rerun 时对话的轮数，决定最后一轮与其 Rerun 按钮的位置
	rounds int
	// edited 表示焦点进入提示词或函数响应输入框后粘贴过内容，焦点移出时 Firefox 派发 change
	edited bool
	// clicked 是最近一次派发可信 click 的时刻
	clicked time.Time
}

// Clicked 返回最近一次点击 Run 或 Rerun 时派发可信 click 的时刻
func (pointer *Pointer) Clicked() time.Time {
	pointer.mu.Lock()
	defer pointer.mu.Unlock()
	return pointer.clicked
}

// NewPointer 返回刚载入的页面上的位置：指针还没进入页面，焦点在提示词输入框
func NewPointer() *Pointer {
	return &Pointer{focus: "prompt"}
}

// Runtime 在纯 Go JavaScript VM 中持有一份与官网页面同形态的 BotGuard 生命周期
type Runtime struct {
	loop        *eventLoop
	vm          *goja.Runtime
	vmRef       atomic.Pointer[goja.Runtime]
	state       *hostState
	snapshot    goja.Callable
	shutdown    goja.Callable
	prompt      goja.Callable
	mouse       goja.Callable
	key         goja.Callable
	mouseInput  goja.Value
	keyInput    goja.Value
	activate    goja.Callable
	metrics     []BotGuardMetric
	operationMu sync.Mutex
	pointer     *Pointer
	rhythm      rhythm.Rhythm
	closeOnce   sync.Once
	// proofCost 是本 VM 读到的取 proof 毫秒耗时
	proofCost float64
}

// promptElements 在页面还没有提示词输入框时建出输入框与 Run 按钮
const promptElements = `
  if (!document.querySelector('ms-prompt-box')) {
    document.body.appendChild(document.createElement('ms-prompt-box')).appendChild(document.createElement('textarea'));
    document.body.appendChild(document.createElement('ms-run-button')).appendChild(document.createElement('button')).appendChild(document.createElement('span'));
  }`

// promptScript 按官网 Worker 的方式向提示词输入框写值并派发 input 与 change，返回输入框的值是否与 prompt 相同
const promptScript = `(prompt => {` + promptElements + `
  const textarea = document.querySelector('ms-prompt-box').querySelector('textarea');
  const setter = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, 'value').set;
  setter.call(textarea, prompt);
  textarea.dispatchEvent(new InputEvent('input', { bubbles: true, inputType: 'insertText', data: prompt }));
  textarea.dispatchEvent(new Event('change', { bubbles: true }));
  return textarea.value === prompt;
})`

// functionElements 在页面还没有函数调用块时建出函数响应输入框与提交按钮
const functionElements = `
  if (!document.querySelector('ms-function-call-chunk')) {
    const form = document.body.appendChild(document.createElement('ms-function-call-chunk')).appendChild(document.createElement('form'));
    form.appendChild(document.createElement('ms-input-field')).appendChild(document.createElement('div')).appendChild(document.createElement('div')).appendChild(document.createElement('input'));
    form.appendChild(document.createElement('button'));
  }`

// settingsElements 在页面还没有运行设置控件时建出模型选择卡片、模型面板中的一行与 All 页签、思考档位下拉框与选项、系统指令卡片与输入框、关闭面板按钮、工具中的开关与编辑按钮、函数声明输入框与保存按钮，settings 为各位置的元素
const settingsElements = `
  const settingsSpots = [['selector', 'button', 'span'], ['row', 'li', 'h3'], ['level', 'mat-select', 'span'], ['option', 'mat-option', 'span'], ['system', 'button', 'span'], ['instructions', 'textarea', ''], ['close', 'button', 'span'], ['grounding', 'button', 'span'], ['functions', 'button', 'span'], ['edit', 'button', 'span'], ['declarations', 'textarea', ''], ['save', 'button', 'span'], ['all', 'button', 'span']];
  let settingsRoot = document.querySelector('ms-run-settings');
  if (!settingsRoot) {
    settingsRoot = document.body.appendChild(document.createElement('ms-run-settings'));
    for (const [, tag, inner] of settingsSpots) {
      const node = settingsRoot.appendChild(document.createElement(tag));
      if (inner) node.appendChild(document.createElement(inner));
    }
  }
  const settings = name => settingsRoot.children[settingsSpots.findIndex(([spot]) => spot === name)];`

// pointerScript 以宿主的 mouseInput 派发一组可信鼠标与焦点事件
const pointerScript = `((input, from, to, blurred, focused, rounds, types) => {` + promptElements + functionElements + settingsElements + `
  const section = innerWidth - 520;
  const box = Math.min(section, 1000);
  const left = 220 + (section - box) / 2;
  let turn = document.querySelector('ms-chat-turn');
  if (!turn) {
    turn = document.body.appendChild(document.createElement('div')).appendChild(document.createElement('ms-chat-turn'));
    turn.appendChild(document.createElement('p'));
    const svg = 'http://www.w3.org/2000/svg';
    turn.appendChild(document.createElement('div')).appendChild(document.createElement('button')).appendChild(document.createElementNS(svg, 'svg')).appendChild(document.createElementNS(svg, 'g')).appendChild(document.createElementNS(svg, 'path'));
  }
  const run = document.querySelector('ms-run-button').querySelector('button');
  const rerun = turn.querySelector('button');
  const textarea = document.querySelector('ms-prompt-box').querySelector('textarea');
  const x = Math.fround(left + box - 126.2);
  const y = innerHeight - 59;
  const button = [x, y, Math.fround(101.2), 32];
  const top = Math.min(197.5 + 212 * (rounds - 1), innerHeight - 307.5);
  const icon = [Math.fround(left + 919 + 25 / 60), Math.fround(top - 10.5 - 5 / 60), Math.fround(15 + 11 / 60), Math.fround(15 + 11 / 60)];
  const rerunPoint = [Math.round(left + 927), Math.round(top - 3)];
  const form = document.querySelector('ms-function-call-chunk').querySelector('form');
  const field = form.querySelector('input');
  const send = form.querySelector('button');
  const fieldRect = [left + 26, top + 231.5, Math.fround(box - 120 - 1 / 3), 32];
  const formRect = [left + 14, top + 193.5, box - 28, 82];
  const spots = {
    prompt: { target: textarea, point: [Math.round(left + box / 2), Math.round(innerHeight - 94.5)], nodes: [textarea, textarea.parentElement], rects: [[left + 25, innerHeight - 105, box - 50, 21], [left + 25, innerHeight - 105, box - 50, 36]] },
    run: { target: run.firstElementChild, point: [Math.round(x + Math.fround(101.2) / 2), y + 16], nodes: [run.firstElementChild, run, run.parentElement], rects: [[Math.fround(x + 45), y + 6, Math.fround(24.2), 20], button, button] },
    turn: { target: turn.firstElementChild, point: [Math.round(left + box / 2), Math.round(top + 62.75)], nodes: [turn], rects: [[left, top, box, 125.5]] },
    rerun: { target: rerun.querySelector('path'), point: rerunPoint, nodes: [rerun.querySelector('path'), rerun.querySelector('g'), rerun.querySelector('svg'), rerun, rerun.parentElement], rects: [icon, icon, [left + 917, top - 13, 20, 20], [left + 911, top - 19, 32, 32], [left + 867, top - 23, 120, 40]] },
    content: { target: turn.parentElement, point: rerunPoint, nodes: [turn.parentElement], rects: [[left, 88, box, top + 81.5]] },
    result: { target: field, point: [Math.round(left + 26 + (box - 120 - 1 / 3) / 2), Math.round(top + 247.5)], nodes: [field, field.parentElement, field.parentElement.parentElement, field.parentElement.parentElement.parentElement, form], rects: [fieldRect, fieldRect, fieldRect, [left + 26, top + 205.5, Math.fround(box - 120 - 1 / 3), 58], formRect] },
    submit: { target: send, point: [Math.round(left + box - 86 - 1 / 3 + (60 + 1 / 3) / 2), Math.round(top + 247.5)], nodes: [send, form], rects: [[Math.fround(left + box - 86 - 1 / 3), top + 231.5, Math.fround(60 + 1 / 3), 32], formRect] },
  };
  const column = innerWidth - 300;
  for (const [name, rect] of [['selector', [column + 16, 92, 268, 36]], ['row', [innerWidth - 553, 256, 540, 50]], ['level', [column + 16, 300, 268, 40]], ['option', [column + 16, 330, 268, 48]], ['system', [column + 16, 184, 268, 48]], ['instructions', [innerWidth - 525, 356, 500, 300]], ['close', [innerWidth - 47, 13, 40, 40]], ['grounding', [innerWidth - 50, 549, 36, 20]], ['functions', [innerWidth - 50, 502, 36, 20]], ['edit', [innerWidth - 93, 497, 28, 28]], ['declarations', [innerWidth / 2 - 300, 110, 600, 320]], ['save', [innerWidth / 2 + 303, 618, 104, 36]], ['all', [innerWidth - 550, 117, 80, 36]]]) {
    const node = settings(name);
    const target = node.firstElementChild ?? node;
    spots[name] = { target, point: [Math.round(rect[0] + rect[2] / 2), Math.round(rect[1] + rect[3] / 2)], nodes: target === node ? [node, settingsRoot] : [target, node, settingsRoot], rects: target === node ? [rect, [column, 0, 300, innerHeight]] : [rect, rect, [column, 0, 300, innerHeight]] };
  }
  const focusable = { prompt: textarea, run, rerun, result: field, submit: send, selector: settings('selector'), row: settings('row'), level: settings('level'), option: settings('option'), system: settings('system'), instructions: settings('instructions'), close: settings('close'), grounding: settings('grounding'), functions: settings('functions'), edit: settings('edit'), declarations: settings('declarations'), save: settings('save'), all: settings('all') };
  const spot = spots[to];
  const movement = from ? [spot.point[0] - spots[from].point[0], spot.point[1] - spots[from].point[1]] : [0, 0];
  input(spot.nodes, spot.rects, spot.target, from ? spots[from].target : null, spot.point, movement, focusable[blurred] ?? null, focusable[focused] ?? null, types);
})`

// keyScript 以宿主的 keyInput 向提示词输入框（target 为 result 时向函数响应输入框）派发一组可信键盘与输入事件，读取输入框的值并返回它是否与 text 相同
const keyScript = `((input, text, types, target) => {` + promptElements + functionElements + settingsElements + `
  const element = target === 'result' ? document.querySelector('ms-function-call-chunk').querySelector('input') : target === 'prompt' ? document.querySelector('ms-prompt-box').querySelector('textarea') : settings(target);
  input(element, text, types);
  return element.value === text;
})`

// clearPromptScript 以原生 setter 清空提示词输入框，与 Camoufox 页面 proof 调用结束时相同，不派发事件
const clearPromptScript = `(() => {
  const box = document.querySelector('ms-prompt-box');
  if (box) Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, 'value').set.call(box.querySelector('textarea'), '');
})()`

// recorderScript 返回官网 BotGuard 包装层传给初始化函数的计时回调与四个记录函数：h、u 事件逐次计数并记录耗时，k 事件按随机计数约每 200 次记录一次
const recorderScript = `(record => {
  let skip = Math.floor(Math.random() * 200);
  return [
    (u, w, B, F) => {
      const name = w ? 'h' : B ? 'u' : 'k';
      if (name !== 'k') {
        if (F !== 0) record('ec', name, 1), record('el', name, u);
      } else if (skip <= 0) {
        record('ec', name, 1), record('el', name, u);
        skip = Math.floor(Math.random() * 200);
      } else skip--;
    },
    (u, w) => record('el', u, w),
    u => record('cec', String(u), 1),
    u => record('od/p', '', u),
    (u, w) => record('od/n', u, w),
  ];
})`

var (
	promptProgram      = goja.MustCompileHost(hostScriptName, promptScript, false)
	pointerProgram     = goja.MustCompileHost(hostScriptName, pointerScript, false)
	keyProgram         = goja.MustCompileHost(hostScriptName, keyScript, false)
	clearPromptProgram = goja.MustCompileHost(hostScriptName, clearPromptScript, false)
	recorderProgram    = goja.MustCompileHost(hostScriptName, recorderScript, false)
)

// BotGuardMetric 是官网 BotGuard 包装层记录的一条 client streamz 指标，Metric 为 ec 或 cec 时 Value 是计数增量，其余为分布取值
type BotGuardMetric struct {
	Metric string
	Label  string
	Value  float64
}

// pointerStep 是一次可信指针操作与它之前的间隔：move 把指针移到 to，press 按下并把焦点移到指针下的按钮，release 抬起并点击，replace 为页面替换了指针下的元素
type pointerStep struct {
	delay  time.Duration
	action string
	to     string
}

// rerunHover 是把指针移到最后一轮中心到 Rerun 按钮出现、指针移到按钮上的间隔
const rerunHover = time.Second

// click 返回以可信指针移到 to、按账户节奏按下再抬起的各步
func (runtime *Runtime) click(to string) []pointerStep {
	return []pointerStep{{0, "move", to}, {rhythm.Duration(runtime.rhythm.Press), "press", ""}, {rhythm.Duration(runtime.rhythm.Hold), "release", ""}}
}

// rerunClick 返回把指针移到最后一轮中心、等 Rerun 按钮出现后以同样方式点击它的各步
func (runtime *Runtime) rerunClick() []pointerStep {
	steps := runtime.click("rerun")
	steps[0].delay = rerunHover
	return append([]pointerStep{{0, "move", "turn"}}, steps...)
}

// keyStep 是一组可信键盘与输入事件与它之前的间隔
type keyStep struct {
	delay time.Duration
	types []string
}

// pasteLead 是焦点进入输入框到按下 Control 的间隔
const pasteLead = 10 * time.Millisecond

// pasteKeys 返回按账户节奏在官网输入框按 Ctrl+V 粘贴的各组事件：按下 Control，再按下 V 并粘贴，抬起 V，抬起 Control
func (runtime *Runtime) pasteKeys() []keyStep {
	return []keyStep{
		{pasteLead, []string{"keydown:Control"}},
		{rhythm.Duration(runtime.rhythm.Control), []string{"keydown:v", "paste", "beforeinput", "input"}},
		{rhythm.Duration(runtime.rhythm.Key), []string{"keyup:v"}},
		{rhythm.Duration(runtime.rhythm.Release), []string{"keyup:Control"}},
	}
}

// events 返回 step 在当前位置上 Firefox 依次派发的事件与事件涉及的位置，并把位置更新为操作之后
func (pointer *Pointer) events(step pointerStep, at time.Time) (from, to, blurred, focused string, rounds int, types []string) {
	pointer.mu.Lock()
	defer pointer.mu.Unlock()
	from, to, blurred, focused, rounds = pointer.at, pointer.at, pointer.focus, pointer.focus, pointer.rounds
	switch step.action {
	case "move":
		to = step.to
		switch from {
		case to:
			types = []string{"pointermove", "mousemove"}
		case "":
			types = []string{"pointerover", "pointermove", "mouseover", "mousemove"}
		default:
			types = []string{"pointerout", "pointerover", "pointermove", "mouseout", "mouseover", "mousemove"}
		}
	case "press":
		types = []string{"pointerdown", "mousedown"}
		if focused = from; focused != blurred {
			if (blurred == "prompt" || blurred == "result" || blurred == "instructions" || blurred == "declarations") && pointer.edited {
				types = append(types, "change")
				pointer.edited = false
			}
			if blurred != "" {
				types = append(types, "focusout")
			}
			types = append(types, "focusin")
		}
	case "release":
		types = []string{"pointerup", "mouseup", "click"}
		pointer.clicked = at
	case "replace":
		switch from {
		case "run":
		case "rerun":
			to = "content"
			if focused == "rerun" {
				focused = ""
			}
		case "submit":
			to = "content"
		default:
			return
		}
		types = []string{"pointerover", "mouseover"}
	}
	pointer.at, pointer.focus = to, focused
	return
}

// NewRuntime 在 Firefox 宿主中加载解释器并初始化 challenge program
func NewRuntime(ctx context.Context, options Options) (*Runtime, error) {
	return newRuntime(ctx, options, "")
}

// newRuntime 创建纯 Go WAA VM，prelude 在顶层宿主安装后、解释器执行前运行
func newRuntime(ctx context.Context, options Options, prelude string) (*Runtime, error) {
	if options.Interpreter == "" {
		return nil, errors.New("WAA 解释器为空")
	}
	if options.Challenge.Program == "" || options.Challenge.GlobalName == "" {
		return nil, errors.New("WAA challenge 缺少 program")
	}
	sourceName := options.Challenge.InterpreterURL
	if sourceName == "" {
		sourceName = "https://www.google.com/js/bg/" + options.Challenge.InterpreterHash + ".js"
	}
	location, zoneName, err := timeZoneOf(options.Profile)
	if err != nil {
		return nil, err
	}
	go loadIntlICU()
	loop := newEventLoop()
	pointer := options.Pointer
	if pointer == nil {
		pointer = NewPointer()
	}
	runtime := &Runtime{
		loop:      loop,
		pointer:   pointer,
		rhythm:    options.Rhythm,
		proofCost: newProofCost(),
	}
	ready := make(chan error, 1)
	var readyOnce sync.Once
	complete := func(err error) { readyOnce.Do(func() { ready <- err }) }
	if !loop.post(func() {
		if err := runtime.start(options, sourceName, prelude, location, zoneName, complete); err != nil {
			complete(err)
		}
	}) {
		loop.close()
		return nil, errors.New("WAA 事件循环未启动")
	}
	select {
	case err := <-ready:
		if err != nil {
			loop.close()
			if vm := runtime.vmRef.Load(); vm != nil {
				vm.Interrupt("WAA runtime init failed")
			}
			<-loop.exited
			return nil, err
		}
		return runtime, nil
	case <-ctx.Done():
		loop.close()
		if vm := runtime.vmRef.Load(); vm != nil {
			vm.Interrupt("WAA runtime aborted")
		}
		<-loop.exited
		return nil, ctx.Err()
	}
}

// start 创建 VM 并安装顶层 Realm、执行解释器与调用 BotGuard 初始化函数
func (runtime *Runtime) start(options Options, sourceName, prelude string, location *time.Location, zoneName func(time.Time) string, complete func(error)) error {
	vm := goja.New()
	runtime.vm = vm
	runtime.vmRef.Store(vm)
	source, err := newFirefoxRandSource()
	if err != nil {
		return fmt.Errorf("初始化 WAA 随机源: %w", err)
	}
	vm.SetRandSource(source)
	vm.SetTimeSource(runtime.loop.wall)
	vm.SetMaxCallStackSize(maxCallStackDepth)
	state := &hostState{
		loop:       runtime.loop,
		registry:   newHostRegistry(),
		rejections: &rejectionQueue{},
		profile:    options.Profile,
		loadImage:  options.LoadImage,
		loadFrame:  options.LoadFrame,
		location:   location,
		zoneName:   zoneName,
	}
	runtime.state = state
	runtime.loop.afterTask = state.rejections.notify
	createIframe := func() *goja.Object {
		window, err := newIframeWindow(vm, state)
		if err != nil {
			panic(vm.NewGoError(err))
		}
		return window
	}
	api, err := state.installRealmHost(vm, "top", createIframe)
	if err != nil {
		return err
	}
	state.topAPI = api
	apiObject := api.ToObject(vm)
	runtime.mouseInput = apiObject.Get("mouseInput")
	runtime.keyInput = apiObject.Get("keyInput")
	runtime.activate, _ = goja.AssertFunction(apiObject.Get("activate"))
	if runtime.prompt, err = compileCallable(vm, promptProgram); err != nil {
		return err
	}
	if runtime.mouse, err = compileCallable(vm, pointerProgram); err != nil {
		return err
	}
	if runtime.key, err = compileCallable(vm, keyProgram); err != nil {
		return err
	}
	vm.SetEvalTransformer(state.registry.evalTransformer(vm, options.Profile.TrustedTypes))
	vm.SetFunctionTransformer(state.registry.functionTransformer(vm, options.Profile.TrustedTypes))
	if prelude != "" {
		if _, err := vm.RunScript("", prelude); err != nil {
			return fmt.Errorf("执行 prelude: %w", err)
		}
	}
	if _, err := vm.RunScript(sourceName, options.Interpreter); err != nil {
		return fmt.Errorf("执行 WAA 解释器: %w", err)
	}
	global := vm.Get(options.Challenge.GlobalName)
	if global == nil || goja.IsUndefined(global) {
		return errors.New("WAA 解释器未定义全局对象")
	}
	object := global.ToObject(vm)
	initialize, ok := goja.AssertFunction(object.Get("a"))
	if !ok {
		return errors.New("WAA 解释器缺少初始化函数")
	}
	signals, state0, err := experimentSignals(vm, options.Challenge.ClientExperimentsStateBlob)
	if err != nil {
		return err
	}
	initStarted := runtime.loop.now()
	runtime.metrics = append(runtime.metrics, BotGuardMetric{Metric: "ec", Label: "t", Value: 1})
	callback := func(call goja.FunctionCall) goja.Value {
		snapshot, snapshotOK := goja.AssertFunction(call.Argument(0))
		if !snapshotOK {
			complete(errors.New("WAA 解释器未返回 snapshot 函数"))
			return goja.Undefined()
		}
		runtime.metrics = append(runtime.metrics, BotGuardMetric{Metric: "el", Label: "t", Value: math.Floor(runtime.loop.now() - initStarted)})
		runtime.snapshot = snapshot
		runtime.shutdown, _ = goja.AssertFunction(call.Argument(1))
		complete(nil)
		return goja.Undefined()
	}
	recorderFn, err := compileCallable(vm, recorderProgram)
	if err != nil {
		return err
	}
	record := func(call goja.FunctionCall) goja.Value {
		runtime.metrics = append(runtime.metrics, BotGuardMetric{
			Metric: call.Argument(0).String(),
			Label:  call.Argument(1).String(),
			Value:  call.Argument(2).ToFloat(),
		})
		return goja.Undefined()
	}
	recorded, err := recorderFn(goja.Undefined(), vm.ToValue(record))
	if err != nil {
		return err
	}
	callbacks := recorded.ToObject(vm)
	loggers := vm.NewArray(callbacks.Get("1"), callbacks.Get("2"), callbacks.Get("3"), callbacks.Get("4"))
	if _, err := initialize(object, vm.ToValue(options.Challenge.Program), vm.ToValue(callback), vm.ToValue(true), goja.Undefined(), callbacks.Get("0"), signals, state0, vm.ToValue(false), loggers); err != nil {
		return fmt.Errorf("初始化 WAA program: %w", err)
	}
	return nil
}

// compileCallable 在 vm 中执行预编译的宿主函数表达式并取出 Callable
func compileCallable(vm *goja.Runtime, program *goja.Program) (goja.Callable, error) {
	value, err := vm.RunProgram(program)
	if err != nil {
		return nil, err
	}
	fn, ok := goja.AssertFunction(value)
	if !ok {
		return nil, errors.New("WAA 宿主函数编译结果不可调用")
	}
	return fn, nil
}

// experimentSignals 按官网规则从 client experiments blob 派生 signal lists 与持久状态
func experimentSignals(vm *goja.Runtime, blob string) (goja.Value, goja.Value, error) {
	values := vm.NewArray()
	kinds := vm.NewArray()
	state := goja.Undefined()
	if blob == "" {
		return vm.NewArray(values, kinds), state, nil
	}
	var fields []json.RawMessage
	if err := json.Unmarshal([]byte(blob), &fields); err != nil {
		return nil, nil, fmt.Errorf("解析 client experiments blob: %w", err)
	}
	var low, high []any
	if len(fields) > 5 {
		var entries [][]json.RawMessage
		_ = json.Unmarshal(fields[5], &entries)
		for _, entry := range entries {
			if len(entry) < 2 {
				continue
			}
			var value, key float64
			if json.Unmarshal(entry[0], &value) != nil || json.Unmarshal(entry[1], &key) != nil {
				continue
			}
			if key <= 53 {
				low = append(low, value)
			} else {
				high = append(high, value)
			}
		}
	}
	if len(fields) > 4 {
		var stored string
		if json.Unmarshal(fields[4], &stored) == nil && stored != "" {
			state = vm.ToValue(stored)
		}
	}
	list := make([]any, 0, len(low)+len(high))
	types := make([]any, 0, len(low)+len(high))
	for _, value := range low {
		list = append(list, value)
		types = append(types, 1)
	}
	for _, value := range high {
		list = append(list, value)
		types = append(types, 2)
	}
	return vm.NewArray(vm.NewArray(list...), vm.NewArray(types...)), state, nil
}

// Settle 等待 VM 发出的页面资源请求完成，请求完成回调中发出的新请求一并等待
func (runtime *Runtime) Settle(ctx context.Context) error {
	done := make(chan struct{})
	if !runtime.loop.post(func() {
		if runtime.state.pending == 0 {
			close(done)
			return
		}
		runtime.state.settled = append(runtime.state.settled, done)
	}) {
		return errors.New("WAA runtime 已关闭")
	}
	select {
	case <-done:
		return nil
	case <-runtime.loop.done:
		return errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return ctx.Err()
	}
}

// action 是一次界面操作中的一步：after 为与上一步的 VM 时钟间隔，run 在事件循环中执行这一步，span 与 ramp 见 timedJob
type action struct {
	after time.Duration
	run   func() error
	span  float64
	ramp  float64
}

// performFitted 把 build 按此前空闲的 VM 时钟毫秒数给出的各步排进空闲区间并等到最后一步执行完
func (runtime *Runtime) performFitted(ctx context.Context, build func(idle float64) []action) error {
	result := make(chan error, 1)
	failed := false
	if !runtime.loop.arrange(func(idle float64) []timedJob {
		actions := build(idle)
		jobs := make([]timedJob, len(actions))
		for index, item := range actions {
			jobs[index] = timedJob{after: item.after, span: item.span, ramp: item.ramp, job: func() {
				if failed {
					return
				}
				err := ctx.Err()
				if err == nil {
					err = item.run()
				}
				if err != nil {
					failed = true
					result <- err
					return
				}
				if index == len(actions)-1 {
					result <- nil
				}
			}}
		}
		return jobs
	}) {
		return errors.New("WAA runtime 已关闭")
	}
	select {
	case err := <-result:
		return err
	case <-runtime.loop.done:
		return errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return ctx.Err()
	}
}

// actionsNeed 返回 actions 排进空闲区间所需的 VM 时钟毫秒数
func actionsNeed(actions []action) float64 {
	var total float64
	for _, item := range actions {
		total += need(item.after, item.span, item.ramp)
	}
	return total
}

// fillPrompt 返回向页面提示词输入框写入文本并派发官网 Worker 相同事件的一步
func (runtime *Runtime) fillPrompt(prompt string) []action {
	prompt = textareaValue(prompt)
	return []action{{run: func() error {
		value, err := runtime.prompt(goja.Undefined(), runtime.vm.ToValue(prompt))
		if err != nil {
			return fmt.Errorf("写入页面提示词: %w", err)
		}
		if !value.ToBoolean() {
			return errors.New("页面提示词状态未同步")
		}
		return nil
	}}}
}

// textareaValue 返回按 Firefox textarea 取值规则把 CRLF 与 CR 规范为 LF 的文本
func textareaValue(value string) string {
	return strings.ReplaceAll(strings.ReplaceAll(value, "\r\n", "\n"), "\r", "\n")
}

// Proof 同步页面提示词后为 SHA-256 digest 生成 snapshot proof，结束后清空输入框
func (runtime *Runtime) Proof(ctx context.Context, digest string, prompt string) (string, error) {
	return runtime.proof(ctx, digest, prompt, func(text string, _ float64) []action { return runtime.fillPrompt(text) }, nil)
}

// RunProof 以可信键盘把文本粘贴进页面提示词输入框（输入框没有焦点时先以可信指针点击它）并点击 Run 后为 SHA-256 digest 生成 fresh proof，返回前清空输入框
func (runtime *Runtime) RunProof(ctx context.Context, digest string, prompt string) (string, error) {
	return runtime.proof(ctx, digest, prompt, func(text string, _ float64) []action { return runtime.paste(text) }, runtime.click("run"))
}

// SettingStep 是点击 Run 之前在运行设置中的一次可信指针点击
type SettingStep struct {
	Wait    time.Duration
	To      string
	Text    string
	Clicked func(at time.Time)
}

// RunProofAfter 先按顺序做 groups 中能排进此前空闲区间的各组运行设置操作，做过运行设置时隔 back 点击提示词输入框，再粘贴文本并点击 Run 后为 SHA-256 digest 生成 fresh proof
func (runtime *Runtime) RunProofAfter(ctx context.Context, digest string, prompt string, groups [][]SettingStep, back time.Duration) (string, error) {
	return runtime.proof(ctx, digest, prompt, func(text string, idle float64) []action {
		click := runtime.click("prompt")
		click[0].delay = back
		resume := append(runtime.pointerActions(click), runtime.pasteInto("prompt", text)...)
		var actions []action
		done := 0
		for ; done < len(groups); done++ {
			group := runtime.settingActions(groups[done])
			if actionsNeed(actions)+actionsNeed(group)+actionsNeed(resume) > idle {
				break
			}
			actions = append(actions, group...)
		}
		skipped := 0
		for _, group := range groups[done:] {
			skipped += len(group)
		}
		prooftime.Skip(ctx, skipped)
		if done == 0 {
			return runtime.paste(text)
		}
		return append(actions, resume...)
	}, runtime.click("run"))
}

// settingActions 返回以可信指针点击 steps 各位置、需要时以可信键盘粘贴的各步，Clicked 在抬起后调用
func (runtime *Runtime) settingActions(steps []SettingStep) []action {
	var actions []action
	for _, step := range steps {
		click := runtime.click(step.To)
		click[0].delay = step.Wait
		pointer := runtime.pointerActions(click)
		if step.Clicked != nil {
			release := pointer[len(pointer)-1].run
			pointer[len(pointer)-1].run = func() error {
				if err := release(); err != nil {
					return err
				}
				step.Clicked(runtime.pointer.Clicked())
				return nil
			}
		}
		actions = append(actions, pointer...)
		if step.Text != "" {
			actions = append(actions, runtime.pasteInto(step.To, step.Text)...)
		}
	}
	return actions
}

// SubmitProof 在 rounds 轮的对话上以可信指针点击最后一轮函数调用块中的函数响应输入框、以可信键盘粘贴 result，再点击提交后为 SHA-256 digest 生成 fresh proof
func (runtime *Runtime) SubmitProof(ctx context.Context, digest string, result string, rounds int) (string, error) {
	runtime.pointer.mu.Lock()
	runtime.pointer.rounds = rounds
	runtime.pointer.mu.Unlock()
	return runtime.proof(ctx, digest, result, func(text string, _ float64) []action {
		return append(runtime.pointerActions(runtime.click("result")), runtime.pasteInto("result", text)...)
	}, runtime.click("submit"))
}

// paste 返回在输入框没有焦点时以可信指针点击输入框、再按 pasteKeys 以可信键盘粘贴提示词的各步
func (runtime *Runtime) paste(prompt string) []action {
	runtime.pointer.mu.Lock()
	focused := runtime.pointer.focus == "prompt"
	runtime.pointer.mu.Unlock()
	var actions []action
	if !focused {
		actions = runtime.pointerActions(runtime.click("prompt"))
	}
	return append(actions, runtime.pasteInto("prompt", prompt)...)
}

// pasteInto 返回按 pasteKeys 以可信键盘把 text 粘贴进有焦点的 target 输入框的各步
func (runtime *Runtime) pasteInto(target string, text string) []action {
	prompt := textareaValue(text)
	keys := runtime.pasteKeys()
	actions := make([]action, len(keys))
	for index, step := range keys {
		pasted := step.types[len(step.types)-1] == "input"
		actions[index] = action{after: step.delay, run: func() error {
			value := ""
			if pasted {
				value = prompt
			}
			same, err := runtime.keyInputAction(target, value, step.types)
			if err != nil {
				return err
			}
			if pasted {
				if !same {
					return errors.New("页面提示词状态未同步")
				}
				runtime.pointer.mu.Lock()
				runtime.pointer.edited = true
				runtime.pointer.mu.Unlock()
			}
			return nil
		}}
	}
	return actions
}

// keyInputAction 在事件循环中以可信键盘向 target 输入框派发 types 中的事件，text 为粘贴与输入事件的正文，返回输入框的值是否与 text 相同
func (runtime *Runtime) keyInputAction(target string, text string, types []string) (bool, error) {
	names := make([]any, len(types))
	for index, name := range types {
		names[index] = name
	}
	list := runtime.vm.NewArray(names...)
	returned, err := runtime.key(goja.Undefined(), runtime.keyInput, runtime.vm.ToValue(text), list, runtime.vm.ToValue(target))
	if err != nil {
		return false, fmt.Errorf("派发键盘事件: %w", err)
	}
	return returned.ToBoolean(), nil
}

// RerunProof 在 rounds 轮的对话上点击最后一轮的 Rerun 后为 SHA-256 digest 生成 fresh proof，与官网 Rerun 一样不写入提示词
func (runtime *Runtime) RerunProof(ctx context.Context, digest string, rounds int) (string, error) {
	runtime.pointer.mu.Lock()
	runtime.pointer.rounds = rounds
	runtime.pointer.mu.Unlock()
	return runtime.proof(ctx, digest, "", nil, runtime.rerunClick())
}

// proof 以 write 返回的各步写入提示词，按 click 以可信鼠标点击，再按账户节奏在 click 后为 digest 生成 proof，返回前清空输入框
func (runtime *Runtime) proof(ctx context.Context, digest string, prompt string, write func(text string, idle float64) []action, click []pointerStep) (string, error) {
	lockStarted := time.Now()
	runtime.operationMu.Lock()
	defer runtime.operationMu.Unlock()
	locked := time.Now()
	prooftime.Observe(ctx, prooftime.Lock, locked.Sub(lockStarted))
	defer runtime.loop.post(func() { _, _ = runtime.vm.RunProgram(clearPromptProgram) })
	var tail []action
	var delay time.Duration
	if click != nil {
		tail = runtime.pointerActions(click)
		delay = rhythm.Duration(runtime.rhythm.Proof)
	}
	result := make(chan snapshotResult, 1)
	var computeStarted time.Time
	tail = append(tail, action{after: delay, span: runtime.proofCost, ramp: proofRamp(), run: func() error {
		computeStarted = time.Now()
		return runtime.startSnapshot(runtime.vm.ToValue(digest), func(value string, err error) { result <- snapshotResult{value, err} })
	}})
	if err := runtime.performFitted(ctx, func(idle float64) []action {
		if write == nil {
			return tail
		}
		return append(write(prompt, idle-actionsNeed(tail)), tail...)
	}); err != nil {
		return "", err
	}
	select {
	case output := <-result:
		prooftime.Observe(ctx, prooftime.Interaction, computeStarted.Sub(locked))
		prooftime.Observe(ctx, prooftime.Compute, time.Since(computeStarted))
		return output.value, output.err
	case <-runtime.loop.done:
		return "", errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return "", ctx.Err()
	}
}

// pointerActions 返回按 steps 的顺序与间隔以可信鼠标操作的各步
func (runtime *Runtime) pointerActions(steps []pointerStep) []action {
	actions := make([]action, len(steps))
	for index, step := range steps {
		actions[index] = action{after: step.delay, run: func() error { return runtime.pointerInput(step) }}
	}
	return actions
}

// Replaced 在页面替换指针下的元素时派发 Firefox 的 pointerover 与 mouseover
func (runtime *Runtime) Replaced(ctx context.Context) error {
	result := make(chan error, 1)
	if !runtime.loop.post(func() { result <- runtime.pointerInput(pointerStep{action: "replace"}) }) {
		return errors.New("WAA runtime 已关闭")
	}
	select {
	case err := <-result:
		return err
	case <-runtime.loop.done:
		return errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return ctx.Err()
	}
}

// pointerInput 在事件循环中按 step 与页面当前的指针和焦点位置派发可信鼠标与焦点事件
func (runtime *Runtime) pointerInput(step pointerStep) error {
	from, to, blurred, focused, rounds, types := runtime.pointer.events(step, runtime.loop.wall())
	if len(types) == 0 {
		return nil
	}
	names := make([]any, len(types))
	for index, name := range types {
		names[index] = name
	}
	list := runtime.vm.NewArray(names...)
	if _, err := runtime.mouse(goja.Undefined(), runtime.mouseInput, runtime.vm.ToValue(from), runtime.vm.ToValue(to), runtime.vm.ToValue(blurred), runtime.vm.ToValue(focused), runtime.vm.ToValue(float64(rounds)), list); err != nil {
		return fmt.Errorf("派发鼠标事件: %w", err)
	}
	return nil
}

// Activate 记录一次用户点击或按键：此后 navigator.userActivation 的 hasBeenActive 为 true，5 秒内 isActive 为 true
func (runtime *Runtime) Activate(ctx context.Context) error {
	result := make(chan error, 1)
	if !runtime.loop.post(func() {
		if runtime.activate == nil {
			result <- errors.New("WAA activate 不可用")
			return
		}
		if _, err := runtime.activate(goja.Undefined()); err != nil {
			result <- fmt.Errorf("记录用户操作: %w", err)
			return
		}
		result <- nil
	}) {
		return errors.New("WAA runtime 已关闭")
	}
	select {
	case err := <-result:
		return err
	case <-runtime.loop.done:
		return errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return ctx.Err()
	}
}

// RefreshSnapshot 生成官网刷新 Waa/Create 时携带的无绑定 snapshot
func (runtime *Runtime) RefreshSnapshot(ctx context.Context) (string, error) {
	runtime.operationMu.Lock()
	defer runtime.operationMu.Unlock()
	return runtime.snapshotWith(ctx, goja.Undefined())
}

// snapshotResult 是一次 snapshot 的输出与错误
type snapshotResult struct {
	value string
	err   error
}

func snapshotOptions(vm *goja.Runtime, digest goja.Value) goja.Value {
	if digest == nil || goja.IsUndefined(digest) {
		return vm.NewArray(goja.Undefined(), goja.Undefined(), goja.Undefined(), goja.Undefined())
	}
	content := vm.NewObject()
	_ = content.Set("content", digest)
	return vm.NewArray(content, goja.Undefined(), goja.Undefined(), goja.Undefined())
}

func (runtime *Runtime) snapshotWith(ctx context.Context, digest goja.Value) (string, error) {
	result := make(chan snapshotResult, 1)
	if !runtime.loop.post(func() {
		if err := ctx.Err(); err != nil {
			result <- snapshotResult{err: err}
			return
		}
		if err := runtime.startSnapshot(digest, func(value string, err error) {
			select {
			case result <- snapshotResult{value, err}:
			default:
			}
		}); err != nil {
			select {
			case result <- snapshotResult{err: err}:
			default:
			}
		}
	}) {
		return "", errors.New("WAA runtime 已关闭")
	}
	select {
	case output := <-result:
		return output.value, output.err
	case <-runtime.loop.done:
		return "", errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return "", ctx.Err()
	}
}

// startSnapshot 在事件循环中为 digest 调用 snapshot，snapshot 交回结果时以结果调用 finish；调用失败时返回错误、不调用 finish
func (runtime *Runtime) startSnapshot(digest goja.Value, finish func(string, error)) error {
	var once sync.Once
	runtime.metrics = append(runtime.metrics, BotGuardMetric{Metric: "ec", Label: "n", Value: 1})
	started, real := runtime.loop.now(), time.Now()
	callback := func(call goja.FunctionCall) goja.Value {
		value := call.Argument(0).String()
		recordSnapshotCost(float64(time.Since(real)) / float64(time.Millisecond))
		runtime.metrics = append(runtime.metrics,
			BotGuardMetric{Metric: "el", Label: "n", Value: math.Floor(runtime.loop.now() - started)},
			BotGuardMetric{Metric: "frs", Value: float64(len(value))},
		)
		once.Do(func() { finish(value, nil) })
		return goja.Undefined()
	}
	if _, err := runtime.snapshot(goja.Undefined(), runtime.vm.ToValue(callback), snapshotOptions(runtime.vm, digest)); err != nil {
		return fmt.Errorf("执行 WAA snapshot: %w", err)
	}
	return nil
}

// TakeMetrics 在事件循环中取出上次以来记录的 BotGuard 指标，排在已排队的任务之后执行
func (runtime *Runtime) TakeMetrics(ctx context.Context) ([]BotGuardMetric, error) {
	result := make(chan []BotGuardMetric, 1)
	if !runtime.loop.postHost(func() {
		taken := runtime.metrics
		runtime.metrics = nil
		result <- taken
	}) {
		return nil, errors.New("WAA runtime 已关闭")
	}
	select {
	case metrics := <-result:
		return metrics, nil
	case <-runtime.loop.done:
		return nil, errors.New("WAA runtime 已关闭")
	case <-ctx.Done():
		return nil, ctx.Err()
	}
}

// Close 结束 VM 生命周期并停止事件循环，关闭超时时中断仍在执行的脚本
func (runtime *Runtime) Close() {
	runtime.closeOnce.Do(func() {
		if runtime.loop == nil {
			return
		}
		done := make(chan struct{})
		if runtime.loop.post(func() {
			if runtime.shutdown != nil {
				_, _ = runtime.shutdown(goja.Undefined())
			}
			close(done)
		}) {
			select {
			case <-done:
			case <-time.After(time.Second):
			}
		}
		runtime.loop.close()
		select {
		case <-runtime.loop.exited:
		case <-time.After(time.Second):
			if vm := runtime.vmRef.Load(); vm != nil {
				vm.Interrupt("WAA runtime closed")
			}
			<-runtime.loop.exited
		}
	})
}
