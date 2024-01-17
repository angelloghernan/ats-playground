// A formally-proven version of the infamous left-pad function.

#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"

dataview str_v(addr, int) =
  | {l: addr}
    str_v_nil (l, 0) of ()
  | {l: addr}{n: nat}
    str_v_cons (l, n + 1) of (char @ l, str_v(l + sizeof(char), n))

vtypedef str(l: addr, n: int) = (str_v(l, n) | ptr l)

dataview uninit_str_v(addr, int) =
  | {l: addr}
    uninit_str_v_nil (l, 0) of ()
  | {l: addr}{n: nat}
    uninit_str_v_cons (l, n + 1) of (char? @ l, uninit_str_v(l + sizeof(char), n))

vtypedef uninit_str(l: addr, n: int) = (uninit_str_v(l, n) | ptr l)

fun str_malloc {n: nat} (len: int n): [l: agz] (uninit_str(l, n)) =
    $extfcall([l: agz] (uninit_str(l, n)), "malloc", sizeof<char>)

fn str_free {n: nat}{l: addr} (s: str(l, n)): void =
    let
        val (_ | p) = s
    in
        $extfcall(void, "free", p)
end


// Params: (string len, pad len, padding character, address)
dataview LPAD(int, int, int, addr) =
  | {c: int}{l: addr}
    LPADBase(0, 0, c, l) of ()
  | {c: int}{n: nat}{l: addr}
    LPADStrChar(n + 1, 0, c, l) of (char @ l, LPAD(n, 0, c, l + sizeof(char)))
  | {c: int}{n: nat}{m: nat}{l: addr}
    LPADPadChar(n, m + 1, c, l) of (char(c) @ l, LPAD(n, m, c, l + sizeof(char)))

vtypedef lpad_str(n: int, m: int, c: int, l: addr) = (LPAD(n, m, c, l) | ptr l)

fn str_init {l: agz}{n: nat}
            (s: !uninit_str(l, n) >> str(l, n), s2: string(n), size: int n): void =
    let
        fun loop {l: addr}{n, i: nat | i <= n} .<n - i>.
            (s: !uninit_str(l, n - i) >> str(l, n - i), 
             s2: string n, size: int n, i: int i): void =
            if i = size then let
                prval uninit_str_v_nil () = s.0
                prval () = s.0 := str_v_nil ()
            in () end
            else let
                prval uninit_str_v_cons(l, r) = s.0
                val () = !(s.1) := s2[i]
                val tmp = (r | ptr_succ<char>(s.1))
                val () = loop (tmp, s2, size, i + 1)
                prval () = s.0 := str_v_cons(l, tmp.0)
            in () end
    in
    loop (s, s2, size, 0)
end

fn str_init_c {l: agz}{n: nat}
              (s: !uninit_str(l, n) >> str(l, n), size: int n, c: char): void =
    let
        fun loop {l: addr}{n, i: nat | i <= n} .<n - i>.
            (s: !uninit_str(l, n - i) >> str(l, n - i), 
             c: char, size: int n, i: int i): void =
            if i = size then let
                prval uninit_str_v_nil () = s.0
                prval () = s.0 := str_v_nil ()
            in () end
            else let
               prval uninit_str_v_cons(l, r) = s.0
               // val () = print ("Str init: ")
               // val () = print ("\n")
               val () = !(s.1) := c
               val tmp = (r | ptr_succ<char>(s.1))
               val () = loop (tmp, c, size, i + 1)
               prval () = s.0 := str_v_cons(l, tmp.0)
            in () end
    in
    loop (s, c, size, 0)
end


fun left_pad {l: agz}{n, m: nat}{c: int} 
             (s: !str(l, n), size: int n, pad_size: int m, c: char c):
             [l2: agz][p: nat | p == max(0, m - n)]
             (LPAD(n, p, c, l2) | ptr l2) =
    let
        fun loop {l: addr}{l2: addr}{n, m, r: nat | r == n + m}{c: int}
                 (s1: !str(l, n), s2: !str(l2, r) >> lpad_str(n, m, c, l2),
                  size: int n, pad_size: int m, c: char c): void =
                 if pad_size = 0 && size = 0 then
                 let
                     val () = assertloc (pad_size + size = 0)
                     // val () = print ("End\n")
                     prval str_v_nil() = s2.0
                     prval () = s2.0 := LPADBase ()
                 in
                     ()
                 end
                 else if pad_size = 0 then let
                     val () = assertloc(size > 0)
                     prval str_v_cons(pl, pr) = s1.0
                     prval str_v_cons(p2l, p2r) = s2.0
                     val () = ptr_set<char>(p2l | s2.1, !(s1.1))
                     // val () = println!("Recurse size, added ", !(s1.1))
                     val tmp1 = (pr | ptr_succ<char>(s1.1))
                     val tmp2 = (p2r | ptr_succ<char>(s2.1))
                     val () = loop (tmp1, tmp2, size - 1, 0, c)
                     prval () = s1.0 := str_v_cons (pl, tmp1.0)
                     prval () = s2.0 := LPADStrChar (p2l, tmp2.0)
                 in
                    ()
                 end
                 else let
                     val () = assertloc(pad_size > 0)
                     prval str_v_cons(p2l, p2r) = s2.0
                     val () = ptr_set<char(c)>(p2l | s2.1, c)
                     // val () = println!("Recurse pad, added ", !(s2.1))
                     val tmp = (p2r | ptr_succ<char>(s2.1))
                     val () = loop (s1, tmp, size, pad_size - 1, c)
                     prval () = s2.0 := LPADPadChar (p2l, tmp.0)
                 in
                     ()
                 end
    in
        if size >= pad_size then let
            val s2 = str_malloc (size)
            val () = str_init_c (s2, size, 'k')
            val () = loop (s, s2, size, 0, c)
        in
            s2
        end
        else let
            val s2 = str_malloc (pad_size)
            val () = str_init_c (s2, pad_size, 'k')
            val () = loop (s, s2, size, pad_size - size, c)
        in
            s2
        end
end

fun print_str {l: addr}{n: nat} .<n>. (s: !str(l, n), size: int n): void =
    if size = 0 then ()
    else let
        // val () = print ("Recurse str: ")
        prval str_v_cons(l, r) = s.0
        // val i_c = $UN.cast{int}(!(s.1))
        val () = print (!(s.1))
        // val () = print ("\n")
        val tmp = (r | ptr_succ<char>(s.1))
        val () = print_str (tmp, size - 1)
        prval () = s.0 := str_v_cons (l, tmp.0)
    in () end

prfun lpad_str_to_str {l: addr}{n, m: nat}{c: int} .<n,m>.
      (pf: !LPAD(n, m, c, l) >> str_v(l, n + m)): void =
      case+ pf of
      | LPADBase () => let prval () = pf := str_v_nil () in end
      | LPADStrChar (lpf, cons) => let
                                      prval () = lpad_str_to_str(cons)
                                      prval () = pf := str_v_cons(lpf, cons)
                                   in end
      | LPADPadChar (lpf, cons) => let
                                      prval () = lpad_str_to_str(cons)
                                      prval () = pf := str_v_cons(lpf, cons)
                                   in end

implement main0 (argc, argv) = () where {
    val s = str_malloc (13)

    val () = str_init_c (s, 13, 'l')

    // val () = print_str (s, 13)

    // val () = print ("First time\n")
    
    val (pf | p) = left_pad (s, 13, 16, 'd')

    prval () = lpad_str_to_str (pf)

    val s2 = (pf | p)

    val () = print_str (s, 13)

    val () = print ("\n")

    val () = print_str (s2, 16)

    val () = str_free (s)
    val () = str_free (s2)
}
