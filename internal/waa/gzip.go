package waa

import (
	"bytes"
	"compress/gzip"
)

// Gzip 返回以 gzip 默认级别压缩 data 的字节，gzip 头的操作系统字节取 Windows 写入的 10
func Gzip(data []byte) []byte {
	var buf bytes.Buffer
	writer := gzip.NewWriter(&buf)
	writer.OS = 10
	_, _ = writer.Write(data)
	_ = writer.Close()
	out := buf.Bytes()
	if len(out) > 9 {
		out[9] = 10
	}
	return out
}
