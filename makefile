all: demo

demo: demo.dats
	patscc -O3 -flto -o demo demo.dats -DATS_MEMALLOC_LIBC -latslib

left_pad: left_pad.dats
	patscc -g -O1 -flto -o left_pad left_pad.dats -DATS_MEMALLOC_LIBC -latslib
