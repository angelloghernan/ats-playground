#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

staload "libats/ML/SATS/basis.sats"
staload "libats/ML/SATS/list0.sats"
staload _(*anon*) = "libats/ML/DATS/list0.dats"
staload UN = "prelude/SATS/unsafe.sats"

// The cool thing about ATS is linear resource management.
// You can see here that I have defined a raw file_t which is
// a typedef for FILE* from C's stdlib.
typedef file_t = $extype"FILE*"

// Then, we have this data view type which is a linear version
// of this same file type. This means that variables with this
// type must be "consumed" before falling out of scope.
datavtype File = file_t

// fopen gives us a File
extern fun file_open: (string, string) -> File = "mac#fopen"
// fclose consumes the file and returns an int
extern fun file_close: (File) -> int = "mac#fclose"
// fwrite takes the file as a parameter but does not consume
// it, as denoted by the exclamation mark
extern fun file_write: (string, size_t, size_t, !File) -> size_t = "mac#fwrite"

extern fun file_read1 {m, n: nat | m <= n}{l: agz}
           (b0ytes n @ l | ptr l, size_t 1, size_t m, !File): 
           (b0ytes n @ l | size_t) = 
           "mac#fread"

fun file_read {m, n: nat | m <= n}{l: agz}
    (pf: b0ytes n @ l | p: ptr l, sz: size_t m, f: !File): 
    (b0ytes n @ l | size_t) = 
    file_read1 (pf | p, i2sz(1), sz, f)

dataview OptionV(v:view, bool) =
    | SomeV (v, true) of (v)
    | NoneV (v, false) of ()

// I define another viewtype for a buffer.
dataview Buffer(a: t@ype, addr, int) =
    | {l: addr} 
        BufferNil (a, l, 0)
    | {l: addr}{n: nat}
        BufferCons (a, l, n + 1) of (a @ l, Buffer (a, l + sizeof(a), n))

sortdef agz = {a: addr | a > null}

extern fun raw_malloc {n: nat}(size_t n): [l: agz] (b0ytes n @ l | ptr l) = "mac#malloc"

extern fun raw_free {n: nat}{l: addr}(b0ytes n @ l | ptr l): void = "mac#free"

// This function is templated, taking a generic type a and allocating the
// required space for it. It returns a proof of uninitialized memory at
// a given address (a? @ l), and a pointer to this address.
fun {a:vt0p} ty_malloc (): [l: agz] (a? @ l | ptr l) =
    $extfcall([l: agz] (a? @ l | ptr l), "malloc", sizeof<a>)

extern fun ty_free {a: t@ype} {l: addr} (a @ l | ptr l): void = "mac#free"


// This function takes a 
fun sum_up {n, m: nat | m < n} (A: &(@[int][n]), sz: int n): int =
    let
        fun loop {n, i: nat | i <= n} .<n - i>.
            (A: &(@[int][n]), idx: int i, sz: int n, acc: int): int =
            if idx = sz then acc
            else loop (A, idx + 1, sz, acc + A[idx])
    in
        loop (A, 0, sz, 0)
end


exception FileOpenError of ()

implement main0 () = () where {
    val file = file_open ("output1.txt", "rw")

    val _ = file_write ("Hello, World!", i2sz(1), i2sz(13), file)

    val (pf | p) = raw_malloc (i2sz(10))

    val (pf | res) = file_read (pf | p, i2sz(10), file)

    val () = raw_free (pf | p)

    val result = file_close (file)

    val () = print (result)
}

