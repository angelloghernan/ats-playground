all: demo

demo: demo.dats
	patscc -O3 -flto -o demo demo.dats -DATS_MEMALLOC_LIBC -latslib
