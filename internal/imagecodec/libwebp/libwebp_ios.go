//go:build ios

// Package libwebp 在 iOS 下回退到纯 Go nativewebp 编码 WebP，避免依赖外部 libwebp 静态库
package libwebp

import (
	"image"
	"io"

	"github.com/HugoSmits86/nativewebp"
)

// Encode 在 iOS 下使用纯 Go 的 nativewebp 编码 WebP 写入 w
func Encode(w io.Writer, m image.Image, _ int) error {
	return nativewebp.Encode(w, m, nil)
}
