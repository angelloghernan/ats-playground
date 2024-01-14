// #include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include
"share/atspre_staload_libats_ML.hats"

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
datavtype File = File_Ptr of (file_t)

// Now let's construct some simple operations for opening, closing, 
// reading, and writing files

// fopen gives us a File. We assume for sake of simplicity that this operation
// always works.
extern fun file_open_raw: (string, string) -> File = "mac#fopen"
// fclose consumes the file and returns an int
extern fun file_close_raw: (File) -> int = "mac#fclose"
// fwrite takes the file as a parameter but does not consume
// it, as denoted by the exclamation mark
extern fun file_write_raw: (string, size_t, size_t, !File) -> size_t = "mac#fwrite"

// A dummy function that's a simple wrapper over fread. More details below.
extern fun file_read_raw {m, n: nat | m <= n}{l: agz}
           (b0ytes n @ l | ptr l, size_t 1, size_t m, !File): 
           [o: nat | o <= m]
           (b0ytes n @ l | size_t o) = 
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
fun file_read1 {m, n: nat | m <= n}{l: agz}
    (pf: b0ytes n @ l | p: ptr l, sz: size_t m, f: !File): 
    (b0ytes n @ l | size_t) = 
    file_read_raw (pf | p, i2sz(1), sz, f)

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

// We can forward-declare functions like this.
// Also, "fun" means the function can recurse, whereas "fn" means the function
// cannot recurse.
extern fn {a: t@ype} init_one (A: &(@[a?][1]) >> @[a][1], elt: a): void

// This function replicates the functionality of memset. It takes a possibly
// uninitialized array of size n and mutates it into an initialized array of 
// size n. It uses array view splits to initialize one element at a time in 
// sequence. It should optimize down to a tail-recursive function, because we 
// only use proof-level functions after the tail-call (i.e. no actual work is 
// done after calling 'loop')
fun {a: t@ype} mem_init {n: pos} 
    (A: &(@[a?][n]) >> @[a][n], size: int n, elt: a): void =
    let
        fun {a: t@ype} loop {n: pos} .<n>.
            (A: &(@[a?][n]) >> @[a][n], size: int n, elt: a): void =
            if size = 1 then init_one (A, elt)
            else let
                prval (pfA1, pfA2) = array_v_split{..}{..}{n}{1} (view@A)
                val () = init_one (A, elt)
                val pA2 = ptr_add<a> (addr@A, 1)
                val (pfA2 | pA2) = viewptr_match (pfA2 | pA2)
                val () = loop (!pA2, size - 1, elt)
                prval () = view@(A) := array_v_unsplit (pfA1, pfA2)
            in () end
    in
    loop (A, size, elt)
end

implement {a} init_one (A, elt) = 
    let 
        prval (pf1, _) = array_v_uncons(view@A)
        val p = addr@A
        val () = ptr_set<a>(pf1 | p, elt)
        prval () = view@(A) := array_v_cons (pf1, array_v_nil ())
    in ()
end

extern fun file_read_raw1 {m, n: nat | m <= n}{l: addr}
           (array_v (char?, l, n) | ptr l, size_t 1, size_t m, !File): 
           [o: nat | o <= m]
           (@[char][o] @ l, @[char?][n - o] @ (l + o * sizeof(char)) | size_t o) = 
           "mac#fread"

// A better function for file reading. It lets us know that the number of 
// bytes initialized in our buffer is dependent on the return value of fread, 
// which may be smaller than the number of bytes requested, which in turn can
// be smaller than the number of bytes in our buffer.
fn file_read {m, n: nat | m <= n}{l: addr}
    (pf: array_v (char?, l, n) | p: ptr l, sz: size_t m, f: !File):
    [o: nat | o <= m]
    (@[char][o] @ l, @[char?][n - o] @ (l + o * sizeof(char)) | size_t o) =
    let
        val (pf1, pf2 | ret) = file_read_raw1 (pf | p, i2sz(1), sz, f)
    in
        (pf1, pf2 | ret)
end

fn file_write {m, n: nat | m <= n}
    (A: &(@[char][n]), sz: size_t m, f: !File):
    [o: nat | o <= m] (size_t o) =
    let
        val+@File_Ptr (f_ptr) = f
        val ret = $extfcall([o: nat | o <= m] size_t o, 
                            "fwrite", addr@A, 1, sz, f_ptr)
        prval () = fold@(f)
    in
        ret
end

fn print_buf {n: nat} (A: &(@[char][n]), sz: size_t n): void =
    let
        fun loop {n: nat}{l: addr} .<n>.
        (pf: !array_v (char, l, n) | p: ptr l, sz: size_t n): void =
            if sz = 0 then ()
            else let
                prval (pf1, pf2) = array_v_uncons (pf)
                val () = print (!p)
                val p2 = ptr_add<char>(p, 1)
                val () = loop (pf2 | p2, sz - 1)
                prval () = pf := array_v_cons (pf1, pf2)
            in () end
    in
        loop (view@A | addr@A, sz)
end

fn print_file (file_name: string): void =
    let
        fun loop (A: &(@[char?][256]), file: !File): void =
            let
                val (pf1, pf2 | nread) = file_read (view@A | addr@A, i2sz(256), file)
            in
                // Cool thing about file_read is that now ATS knows the length of init-
                // ialized bytes located at A's address is equivalent to "nread". This
                // is something that could not ever be captured by C's type system.
                if nread = 0 then let 
                    prval () = view@A := array_v_unsplit{char?}{..}{..} (pf1, pf2)
                in () end
                else let
                    val p = addr@A
                    val p2 = addr@A

                    val p2 = ptr_add<char>(p2, nread)

                    val () = print_buf (!p, nread)

                    prval () = view@A := array_v_unsplit{char?}{..}{..} (pf1, pf2)
                    val () = loop (A, file)

                in () end
        end
        val file = file_open_raw (file_name, "r")
        var A = @[char?][256]()
        val () = loop (A, file)
        // If we omit this line, type-checking fails. We must always
        // consume the linear variable "file".
        val _ = file_close_raw (file)
    in () end
    

implement main0 () = () where {
    val () = print_file ("sample_text.txt")

    var A = @[int](1, 2, 3, 4, 5)
    
    // Sum of all 5 numbers
    val sum_5 = sum_up (A, 5)

    // Sum of the first 4 numbers
    val sum_4 = sum_up (A, 4)

    var B = @[int][5]()

    // If this initialization is skipped, type checking fails
    val () = mem_init (B, 5, 10) 

    val sum_B = sum_up (B, 5) // equals 50
    
    // This would fail type checking since it goes out of bounds
    // val sum_6 = sum_up (A, 6)

    val () = println! ("sum 5: ", sum_5)
    val () = println! ("sum 10: ", sum_B)
}

