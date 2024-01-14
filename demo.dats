// #include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include
"share/atspre_staload_libats_ML.hats"

staload UN = "prelude/SATS/unsafe.sats"

// One cool thing about ATS is linear resource management.
// You can see here that I have defined a raw file_t which is
// a typedef for FILE from C's stdlib.
typedef file_t = $extype"FILE"

// Now let's construct some simple operations for opening, closing, 
// reading, and writing files

// fopen gives us a proof and a pointer. The proof tells us that there is
// a file_t at location l (more on that later).
// The proof must only be consumed once, so it is appropriate for objects that 
// you might otherwise manage using RAII in languages like C++ or Rust.
// We assume for now that fopen always succeeds.
extern fun file_open_raw: (string, string) -> [l: agz](file_t @ l | ptr l) = "mac#fopen"
// fclose consumes the file proof and returns an int. The file proof MUST be consumed
// exactly once, so the proof ensures that we always close the file.
extern fun file_close_raw: {l: agz}(file_t @ l | ptr l) -> int = "mac#fclose"
// fwrite takes the file proof as a parameter but does not consume
// it, as denoted by the exclamation mark. Remember, we only want to consume
// the proof exactly once.
extern fun file_write_raw: {l: agz}(!(file_t @ l) | string, size_t, size_t) -> size_t = "mac#fwrite"

// A dummy function that's a simple wrapper over fread. More details below.
extern fun file_read_raw {m, n: nat | m <= n}{l: agz}{l2: agz}
           (b0ytes n @ l, !(file_t @ l2) | ptr l, size_t 1, size_t m, ptr l2): 
           [o: nat | o <= m]
           (b0ytes n @ l | size_t o) = 
           "mac#fread"

// In the future, we can save ourselves some typing like this:
viewdef File(l: addr) = file_t @ l

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
// Altogether, this ensures some nice safety properties:
// 1. The file pointer passed to file_read must be live.
// 2. The buffer pointer passed to file_read cannot be null.
// 3. file_read cannot cause a buffer overflow because the buffer passed must
//    have enough bytes to hold all the read bytes.
fun file_read1 {m, n: nat | m <= n}{l: agz}{l2: agz}
    (pf: b0ytes n @ l, fpf: !File(l2) | p: ptr l, sz: size_t m, fptr: ptr l2): 
    (b0ytes n @ l | size_t) = 
    file_read_raw (pf, fpf | p, i2sz(1), sz, fptr)

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

extern fun file_read_raw1 {m, n: nat | m <= n}{l: agz}{l2: agz}
           (array_v (char?, l, n), !File(l2) | ptr l, size_t 1, size_t m, f: ptr l2): 
           [o: nat | o <= m]
           (@[char][o] @ l, @[char?][n - o] @ (l + o * sizeof(char)) | size_t o) = 
           "mac#fread"

// A better function for file reading. It lets us know that the number of 
// bytes initialized in our buffer is dependent on the return value of fread, 
// which may be smaller than the number of bytes requested, which in turn can
// be smaller than the number of bytes in our buffer.
fn file_read {m, n: nat | m <= n}{l: agz}{l2: agz}
    (pf: array_v (char?, l, n), fpf: !File(l2) | p: ptr l, sz: size_t m, f: ptr l2):
    [o: nat | o <= m]
    (@[char][o] @ l, @[char?][n - o] @ (l + o * sizeof(char)) | size_t o) =
    let
        val (pf1, pf2 | ret) = file_read_raw1 (pf, fpf | p, i2sz(1), sz, f)
    in
        (pf1, pf2 | ret)
end

fn file_write {m, n: nat | m <= n}{l: agz}
    (fpf: !File(l) | A: &(@[char][n]), sz: size_t m, f: ptr l):
    [o: nat | o <= m] (size_t o) =
    let
        val ret = $extfcall([o: nat | o <= m] size_t o, 
                            "fwrite", addr@A, 1, sz, f)
    in
        ret
end

// A safer version of file_open that doesn't assume opening a file always
// succeeds.
fn file_open {l: addr} (file_name: string, mode: string): 
   [l: addr] (option_v(File(l), l > null) | ptr l) =
       $extfcall([l: addr] (option_v(File(l), l > null) | ptr l), 
                 "fopen", file_name, mode)

    

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
        fun loop {l: agz}{l2: agz} 
            (pfa: !array_v(char?, l, 256), fpf: !File(l2) | pa: ptr l, file: ptr l2): void =
            let
                val (pf1, pf2 | nread) = file_read (pfa, fpf | pa, i2sz(256), file)
            in
                if nread = 0 then let
                    prval () = pfa := array_v_unsplit{char?}{..}{..} (pf1, pf2)
                in () end
                else let
                    val () = print_buf (!pa, nread)
                    prval () = pfa := array_v_unsplit{char?}{..}{..} (pf1, pf2)
                    val () = loop (pfa, fpf | pa, file)
                in () end
        end
        val (fpf | fptr) = file_open (file_name, "r")
        val () = if fptr > the_null_ptr then {
            prval Some_v (fpf) = fpf
            var A = @[char?][256]()
            val () = loop (view@A, fpf | addr@A, fptr)
            // If we omit this line, type-checking fails. We must always
            // consume the linear variable "file".
            val _ = file_close_raw (fpf | fptr)
        } else {
            prval None_v () = fpf
        }
    in () end
 
fn display_help (): void =
    println! ("usage: demo [FILE]")

implement main0 (argc, argv) = 
    if argc <= 1 then display_help ()
    else let
        val () = print_file (argv[1])

        var A = @[int](1, 2, 3, 4, 5)

        fun loop {n, m: nat | m <= n} .<n - m>.
            (A: &(@[int][n]), i: int m, sz: int n): void =
            if i = sz then ()
            else let
                val sum = sum_up (A, i)
                val () = println! ("sum ", i + 1, ": ", sum)
            in loop (A, i + 1, sz) end

        val () = loop (A, 0, 5)

        var B = @[int][10]()

        // If this initialization is skipped, type checking fails
        val () = mem_init (B, 10, 10)

        val () = loop (B, 0, 10) // equals 100
        
        // This would fail type checking since it goes out of bounds
        // val sum_6 = sum_up (A, 6)
    in () end
