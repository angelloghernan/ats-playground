all: demo

demo: demo.dats
	patscc -o demo demo.dats -DATS_MEMALLOC_LIBC
