#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

staload "libats/ML/SATS/basis.sats"
staload "libats/ML/SATS/list0.sats"
staload _(*anon*) = "libats/ML/DATS/list0.dats"
staload UN = "prelude/SATS/unsafe.sats"

// One cool thing about ATS is linear resource management.
// You can see here that I have defined a raw file_t which is
// a typedef for FILE* from C's stdlib.
typedef file_t = $extype"FILE*"

// Then, we have this data view type which is a linear version of this same
// file type. This means that variables with this type must be "consumed"
// before falling out of scope, otherwise the compiler refuses compilation. 
// It must only be consumed once, so it is appropriate for objects that you 
// might otherwise manage using RAII in languages like C++ or Rust.
datavtype File = file_t

// Now let's construct some simple operations for opening, closing, 
// reading, and writing files

// fopen gives us a File. We assume for sake of simplicity that this operation
// always works.
extern fun file_open: (string, string) -> File = "mac#fopen"
// fclose consumes the file and returns an int
extern fun file_close: (File) -> int = "mac#fclose"
// fwrite takes the file as a parameter but does not consume
// it, as denoted by the exclamation mark
extern fun file_write: (string, size_t, size_t, !File) -> size_t = "mac#fwrite"

// A dummy function that's a simple wrapper over fread. More details below.
extern fun file_read1 {m, n: nat | m <= n}{l: agz}
           (b0ytes n @ l | ptr l, size_t 1, size_t m, !File): 
           (b0ytes n @ l | size_t) = 
           "mac#fread"

// A relatively safe version of fread.
// Let's go bit by bit:
//
// {m, n: nat | m <= n}{l: agz}
// m, n: nat | m <= n => non-negative numbers. m must be less than or equal to n
// 
// l: agz => l is type agz: Address greater than zero. Full definition:
// sortdef agz = {a: addr | a > null}
// 
// pf: b0ytes n @ l => a "proof" that there are n possibly-uninitialized bytes
// located at (@) address l.
//
// p: ptr l => a pointer with value l. Like "void*" in C, except it must have
// a value equal to l.
//
// sz: size_t m => the amount of bytes to read, where sz = m
//
// f: !File => as before, take the file as a parameter without consuming it.
//
// Altogether, this ensures some nice safety properties:
// 1. The file pointer passed to file_read must be live.
// 2. The buffer pointer passed to file_read cannot be null.
// 3. file_read cannot cause a buffer overflow because the buffer passed must
//    have enough bytes to hold all the read bytes.
fun file_read {m, n: nat | m <= n}{l: agz}
    (pf: b0ytes n @ l | p: ptr l, sz: size_t m, f: !File): 
    (b0ytes n @ l | size_t) = 
    file_read1 (pf | p, i2sz(1), sz, f)

// Simple wrappers over malloc and free with some basic safety properties.
// (Note that the definition for malloc here is practical but not *exactly* safe: 
// malloc is free to return NULL. However, for userspace programs, it is all but 
// impossible for most programs to try and recover from out-of-memory errors.)
extern fun raw_malloc {n: nat}(size_t n): [l: agz] (b0ytes n @ l | ptr l) = "mac#malloc"

extern fun raw_free {n: nat}{l: addr}(b0ytes n @ l | ptr l): void = "mac#free"

// This function is templated, taking a generic type "a" and allocating the
// required space for it. It returns a proof of uninitialized memory at a given
// address (a? @ l), and a pointer to this address.
fun {a:vt0p} ty_malloc (): [l: agz] (a? @ l | ptr l) =
    $extfcall([l: agz] (a? @ l | ptr l), "malloc", sizeof<a>)

extern fun ty_free {a: t@ype} {l: addr} (a @ l | ptr l): void = "mac#free"

// This function takes a reference to an array and a number of elements
// to sum up in series.
// 
// The cool thing is that this function is entirely safe! It cannot index
// invalidly, and it is guaranteed to terminate. At the same time, absolutely 
// no run time cost is incurred for this safety.
//
// There are a couple of new constructs here: &(@[int][n]) is a reference to
// a flat array of n ints (i.e., it's not a reference to a boxed array, which
// is itself a pointer to the heap). 
// 
// In addition, .<m - i>. is a terminating condition: the compiler verifies 
// that on each subsequent recursive call, "m - i" shrinks to zero and 
// eventually results in the termination of the loop.
//
// Note also that sum_up is tail-recursive, so there should be ~zero overhead
// compared to a manual effectful loop.
fun sum_up {n, m: nat | m <= n} (A: &(@[int][n]), num_elts: int m): int =
    let
        fun loop {n, m, i: nat | i <= m | m <= n} .<m - i>.
            (A: &(@[int][n]), idx: int i, num_elts: int m, acc: int): int =
            if idx = num_elts then acc
            else loop (A, idx + 1, num_elts, acc + A[idx])
    in
        loop (A, 0, num_elts, 0)
end


implement main0 () = () where {
    val file = file_open ("output1.txt", "w")

    val _ = file_write ("Hello, World!", i2sz(1), i2sz(13), file)

    // val (pf | p) = raw_malloc (i2sz(10))
    // val (pf | res) = file_read (pf | p, i2sz(10), file)
    // val () = raw_free (pf | p)

    // If we omit this line, type-checking fails. We must always
    // consume the linear variable "file".
    val _ = file_close (file)

    var A = @[int](1, 2, 3, 4, 5)
    
    // Sum of all 5 numbers
    val sum_5 = sum_up (A, 5)

    // Sum of the first 4 numbers
    val sum_4 = sum_up (A, 4)
    
    // This would fail type checking:
    // val sum_6 = sum_up (A, 6)

    // Prints 15
    val () = print (sum_5)
}

