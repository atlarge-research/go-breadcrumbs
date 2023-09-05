package runtime

import "sync/atomic"

var numMarkers int64 = 0

//go:noinline
func DfMark[T any](val T) int64 {
	nextMarker := atomic.AddInt64(&numMarkers, 1)
	prevMarker := nextMarker - 1
	return prevMarker
}

//go:noinline
func DfInspect[T any](val T) int64 {
	return -1
}
