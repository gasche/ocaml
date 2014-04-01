(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Translation from closed lambda to C-- *)

ouvre Misc
ouvre Arch
ouvre Asttypes
ouvre Primitive
ouvre Types
ouvre Lambda
ouvre Clambda
ouvre Cmm
ouvre Cmx_format

(* Local binding of complex expressions *)

soit bind name arg fn =
  filtre arg avec
    Cvar _ | Cconst_int _ | Cconst_natint _ | Cconst_symbol _
  | Cconst_pointer _ | Cconst_natpointer _
  | Cconst_blockheader _ -> fn arg
  | _ -> soit id = Ident.create name dans Clet(id, arg, fn (Cvar id))

soit bind_nonvar name arg fn =
  filtre arg avec
    Cconst_int _ | Cconst_natint _ | Cconst_symbol _
  | Cconst_pointer _ | Cconst_natpointer _
  | Cconst_blockheader _ -> fn arg
  | _ -> soit id = Ident.create name dans Clet(id, arg, fn (Cvar id))

(* Block headers. Meaning of the tag field: see stdlib/obj.ml *)

soit floatarray_tag = Cconst_int Obj.double_array_tag

soit block_header tag sz =
  Nativeint.add (Nativeint.shift_left (Nativeint.of_int sz) 10)
                (Nativeint.of_int tag)
soit closure_header sz = block_header Obj.closure_tag sz
soit infix_header ofs = block_header Obj.infix_tag ofs
soit float_header = block_header Obj.double_tag (size_float / size_addr)
soit floatarray_header len =
      block_header Obj.double_array_tag (len * size_float / size_addr)
soit string_header len =
      block_header Obj.string_tag ((len + size_addr) / size_addr)
soit boxedint32_header = block_header Obj.custom_tag 2
soit boxedint64_header = block_header Obj.custom_tag (1 + 8 / size_addr)
soit boxedintnat_header = block_header Obj.custom_tag 2

soit alloc_block_header tag sz = Cconst_blockheader(block_header tag sz)
soit alloc_float_header = Cconst_blockheader(float_header)
soit alloc_floatarray_header len = Cconst_blockheader(floatarray_header len)
soit alloc_closure_header sz = Cconst_blockheader(closure_header sz)
soit alloc_infix_header ofs = Cconst_blockheader(infix_header ofs)
soit alloc_boxedint32_header = Cconst_blockheader(boxedint32_header)
soit alloc_boxedint64_header = Cconst_blockheader(boxedint64_header)
soit alloc_boxedintnat_header = Cconst_blockheader(boxedintnat_header)

(* Integers *)

soit max_repr_int = max_int dda 1
soit min_repr_int = min_int dda 1

soit int_const n =
  si n <= max_repr_int && n >= min_repr_int
  alors Cconst_int((n dgl 1) + 1)
  sinon Cconst_natint
          (Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n)

soit rec add_const c n =
  si n = 0 alors c
  sinon filtre c avec
  | Cconst_int x quand no_overflow_add x n -> Cconst_int (x + n)
  | Cop(Csubi, [Cconst_int x; c]) quand no_overflow_add n x ->
      Cop(Csubi, [Cconst_int (n + x); c])
  | Cop(Csubi, [c; Cconst_int x]) quand no_overflow_sub n x ->
      add_const c (n - x)
  | c -> Cop(Caddi, [c; Cconst_int n])

soit incr_int = fonction
    Cconst_int n quand n < max_int -> Cconst_int(n+1)
  | Cop(Caddi, [c; Cconst_int n]) quand n < max_int -> add_const c (n + 1)
  | c -> add_const c 1

soit decr_int = fonction
    Cconst_int n quand n > min_int -> Cconst_int(n-1)
  | Cop(Caddi, [c; Cconst_int n]) quand n > min_int -> add_const c (n - 1)
  | c -> add_const c (-1)

soit add_int c1 c2 =
  filtre (c1, c2) avec
    (Cop(Caddi, [c1; Cconst_int n1]),
     Cop(Caddi, [c2; Cconst_int n2])) quand no_overflow_add n1 n2 ->
      add_const (Cop(Caddi, [c1; c2])) (n1 + n2)
  | (Cop(Caddi, [c1; Cconst_int n1]), c2) ->
      add_const (Cop(Caddi, [c1; c2])) n1
  | (c1, Cop(Caddi, [c2; Cconst_int n2])) ->
      add_const (Cop(Caddi, [c1; c2])) n2
  | (Cconst_int _, _) ->
      Cop(Caddi, [c2; c1])
  | (_, _) ->
      Cop(Caddi, [c1; c2])

soit sub_int c1 c2 =
  filtre (c1, c2) avec
    (Cop(Caddi, [c1; Cconst_int n1]),
     Cop(Caddi, [c2; Cconst_int n2])) quand no_overflow_sub n1 n2 ->
      add_const (Cop(Csubi, [c1; c2])) (n1 - n2)
  | (Cop(Caddi, [c1; Cconst_int n1]), c2) ->
      add_const (Cop(Csubi, [c1; c2])) n1
  | (c1, Cop(Caddi, [c2; Cconst_int n2])) quand n2 <> min_int ->
      add_const (Cop(Csubi, [c1; c2])) (-n2)
  | (c1, Cconst_int n) quand n <> min_int ->
      add_const c1 (-n)
  | (c1, c2) ->
      Cop(Csubi, [c1; c2])

soit mul_int c1 c2 =
  filtre (c1, c2) avec
    (c, Cconst_int 0) | (Cconst_int 0, c) ->
      Cconst_int 0
  | (c, Cconst_int 1) | (Cconst_int 1, c) ->
      c
  | (c, Cconst_int(-1)) | (Cconst_int(-1), c) ->
      sub_int (Cconst_int 0) c
  | (c, Cconst_int n) | (Cconst_int n, c) quand n = 1 dgl Misc.log2 n->
      Cop(Clsl, [c; Cconst_int(Misc.log2 n)])
  | (c1, c2) ->
      Cop(Cmuli, [c1; c2])

soit lsl_int c1 c2 =
  filtre (c1, c2) avec
    (Cop(Clsl, [c; Cconst_int n1]), Cconst_int n2)
    quand n1 > 0 && n2 > 0 && n1 + n2 < size_int * 8 ->
      Cop(Clsl, [c; Cconst_int (n1 + n2)])
  | (_, _) ->
      Cop(Clsl, [c1; c2])

soit ignore_low_bit_int = fonction
    Cop(Caddi, [(Cop(Clsl, [_; Cconst_int n]) tel c); Cconst_int 1]) quand n > 0
      -> c
  | Cop(Cor, [c; Cconst_int 1]) -> c
  | c -> c

soit lsr_int c1 c2 =
  filtre c2 avec
    Cconst_int 0 ->
      c1
  | Cconst_int n quand n > 0 ->
      Cop(Clsr, [ignore_low_bit_int c1; c2])
  | _ ->
      Cop(Clsr, [c1; c2])

soit asr_int c1 c2 =
  filtre c2 avec
    Cconst_int 0 ->
      c1
  | Cconst_int n quand n > 0 ->
      Cop(Casr, [ignore_low_bit_int c1; c2])
  | _ ->
      Cop(Casr, [c1; c2])

soit tag_int = fonction
    Cconst_int n ->
      int_const n
  | Cop(Casr, [c; Cconst_int n]) quand n > 0 ->
      Cop(Cor, [asr_int c (Cconst_int (n - 1)); Cconst_int 1])
  | c ->
      incr_int (lsl_int c (Cconst_int 1))

soit force_tag_int = fonction
    Cconst_int n ->
      int_const n
  | Cop(Casr, [c; Cconst_int n]) quand n > 0 ->
      Cop(Cor, [asr_int c (Cconst_int (n - 1)); Cconst_int 1])
  | c ->
      Cop(Cor, [lsl_int c (Cconst_int 1); Cconst_int 1])

soit untag_int = fonction
    Cconst_int n -> Cconst_int(n dda 1)
  | Cop(Caddi, [Cop(Clsl, [c; Cconst_int 1]); Cconst_int 1]) -> c
  | Cop(Cor, [Cop(Casr, [c; Cconst_int n]); Cconst_int 1])
    quand n > 0 && n < size_int * 8 ->
      Cop(Casr, [c; Cconst_int (n+1)])
  | Cop(Cor, [Cop(Clsr, [c; Cconst_int n]); Cconst_int 1])
    quand n > 0 && n < size_int * 8 ->
      Cop(Clsr, [c; Cconst_int (n+1)])
  | Cop(Cor, [c; Cconst_int 1]) -> Cop(Casr, [c; Cconst_int 1])
  | c -> Cop(Casr, [c; Cconst_int 1])

(* Turning integer divisions into multiply-high then shift.
   The [division_parameters] function is used in module Emit for
   those target platforms that support this optimization. *)

(* Unsigned comparison between native integers. *)

soit ucompare x y = Nativeint.(compare (add x min_int) (add y min_int))

(* Unsigned division and modulus at type nativeint.
   Algorithm: Hacker's Delight section 9.3 *)

soit udivmod n d = Nativeint.(
  si d < 0n alors
    si ucompare n d < 0 alors (0n, n) sinon (1n, sub n d)
  sinon début
    soit q = shift_left (div (shift_right_logical n 1) d) 1 dans
    soit r = sub n (mul q d) dans
    si ucompare r d >= 0 alors (succ q, sub r d) sinon (q, r)
  fin)

(* Compute division parameters.
   Algorithm: Hacker's Delight chapter 10, fig 10-1. *)

soit divimm_parameters d = Nativeint.(
  affirme (d > 0n);
  soit twopsm1 = min_int dans (* 2^31 for 32-bit archs, 2^63 for 64-bit archs *)
  soit nc = sub (pred twopsm1) (snd (udivmod twopsm1 d)) dans
  soit rec loop p (q1, r1) (q2, r2) =
    soit p = p + 1 dans
    soit q1 = shift_left q1 1 et r1 = shift_left r1 1 dans
    soit (q1, r1) =
      si ucompare r1 nc >= 0 alors (succ q1, sub r1 nc) sinon (q1, r1) dans
    soit q2 = shift_left q2 1 et r2 = shift_left r2 1 dans
    soit (q2, r2) =
      si ucompare r2 d >= 0 alors (succ q2, sub r2 d) sinon (q2, r2) dans
    soit delta = sub d r2 dans
    si ucompare q1 delta < 0 || (q1 = delta && r1 = 0n)
    alors loop p (q1, r1) (q2, r2)
    sinon (succ q2, p - size)
  dans loop (size - 1) (udivmod twopsm1 nc) (udivmod twopsm1 d))

(* The result [(m, p)] of [divimm_parameters d] satisfies the following
   inequality:

      2^(wordsize + p) < m * d <= 2^(wordsize + p) + 2^(p + 1)    (i)

   from which it follows that

      floor(n / d) = floor(n * m / 2^(wordsize+p))
                              if 0 <= n < 2^(wordsize-1)
      ceil(n / d) = floor(n * m / 2^(wordsize+p)) + 1
                              if -2^(wordsize-1) <= n < 0

   The correctness condition (i) above can be checked by the code below.
   It was exhaustively tested for values of d from 2 to 10^9 in the
   wordsize = 64 case.

let add2 (xh, xl) (yh, yl) =
  let zl = add xl yl and zh = add xh yh in
  ((if ucompare zl xl < 0 then succ zh else zh), zl)

let shl2 (xh, xl) n =
  assert (0 < n && n < size + size);
  if n < size
  then (logor (shift_left xh n) (shift_right_logical xl (size - n)),
        shift_left xl n)
  else (shift_left xl (n - size), 0n)

let mul2 x y =
  let halfsize = size / 2 in
  let halfmask = pred (shift_left 1n halfsize) in
  let xl = logand x halfmask and xh = shift_right_logical x halfsize in
  let yl = logand y halfmask and yh = shift_right_logical y halfsize in
  add2 (mul xh yh, 0n)
    (add2 (shl2 (0n, mul xl yh) halfsize)
       (add2 (shl2 (0n, mul xh yl) halfsize)
          (0n, mul xl yl)))

let ucompare2 (xh, xl) (yh, yl) =
  let c = ucompare xh yh in if c = 0 then ucompare xl yl else c

let validate d m p =
  let md = mul2 m d in
  let one2 = (0n, 1n) in
  let twoszp = shl2 one2 (size + p) in
  let twop1 = shl2 one2 (p + 1) in
  ucompare2 twoszp md < 0 && ucompare2 md (add2 twoszp twop1) <= 0
*)

soit rec div_int c1 c2 dbg =
  filtre (c1, c2) avec
    (c1, Cconst_int 0) ->
      Csequence(c1, Cop(Craise (Raise_regular, dbg),
                        [Cconst_symbol "caml_exn_Division_by_zero"]))
  | (c1, Cconst_int 1) ->
      c1
  | (Cconst_int 0 tel c1, c2) ->
      Csequence(c2, c1)
  | (Cconst_int n1, Cconst_int n2) ->
      Cconst_int (n1 / n2)
  | (c1, Cconst_int n) quand n <> min_int ->
      soit l = Misc.log2 n dans
      si n = 1 dgl l alors
        (* Algorithm:
              t = shift-right-signed(c1, l - 1)
              t = shift-right(t, W - l)
              t = c1 + t
              res = shift-right-signed(c1 + t, l)
        *)
        Cop(Casr, [bind "dividend" c1 (fonc c1 ->
                     soit t = asr_int c1 (Cconst_int (l - 1)) dans
                     soit t = lsr_int t (Cconst_int (Nativeint.size - l)) dans
                     add_int c1 t);
                   Cconst_int l])
      sinon si n < 0 alors
        sub_int (Cconst_int 0) (div_int c1 (Cconst_int (-n)) dbg)
      sinon début
        soit (m, p) = divimm_parameters (Nativeint.of_int n) dans
        (* Algorithm:
              t = multiply-high-signed(c1, m)
              if m < 0, t = t + c1
              if p > 0, t = shift-right-signed(t, p)
              res = t + sign-bit(c1)
        *)
        bind "dividend" c1 (fonc c1 ->
          soit t = Cop(Cmulhi, [c1; Cconst_natint m]) dans
          soit t = si m < 0n alors Cop(Caddi, [t; c1]) sinon t dans
          soit t = si p > 0 alors Cop(Casr, [t; Cconst_int p]) sinon t dans
          add_int t (lsr_int c1 (Cconst_int (Nativeint.size - 1))))
      fin
  | (c1, c2) quand !Clflags.fast ->
      Cop(Cdivi, [c1; c2])
  | (c1, c2) ->
      bind "divisor" c2 (fonc c2 ->
        Cifthenelse(c2,
                    Cop(Cdivi, [c1; c2]),
                    Cop(Craise (Raise_regular, dbg),
                        [Cconst_symbol "caml_exn_Division_by_zero"])))

soit mod_int c1 c2 dbg =
  filtre (c1, c2) avec
    (c1, Cconst_int 0) ->
      Csequence(c1, Cop(Craise (Raise_regular, dbg),
                        [Cconst_symbol "caml_exn_Division_by_zero"]))
  | (c1, Cconst_int 1) ->
      c1
  | (Cconst_int(0 | 1) tel c1, c2) ->
      Csequence(c2, c1)
  | (Cconst_int n1, Cconst_int n2) ->
      Cconst_int (n1 mod n2)
  | (c1, (Cconst_int n tel c2)) quand n <> min_int ->
      soit l = Misc.log2 n dans
      si n = 1 dgl l alors
        (* Algorithm:
              t = shift-right-signed(c1, l - 1)
              t = shift-right(t, W - l)
              t = c1 + t
              t = bit-and(t, -n)
              res = c1 - t
         *)
        bind "dividend" c1 (fonc c1 ->
          soit t = asr_int c1 (Cconst_int (l - 1)) dans
          soit t = lsr_int t (Cconst_int (Nativeint.size - l)) dans
          soit t = add_int c1 t dans
          soit t = Cop(Cand, [t; Cconst_int (-n)]) dans
          sub_int c1 t)
      sinon
        bind "dividend" c1 (fonc c1 ->
          sub_int c1 (mul_int (div_int c1 c2 dbg) c2))
  | (c1, c2) quand !Clflags.fast ->
      Cop(Cmodi, [c1; c2])
  | (c1, c2) ->
      bind "divisor" c2 (fonc c2 ->
        Cifthenelse(c2,
                    Cop(Cmodi, [c1; c2]),
                    Cop(Craise (Raise_regular, dbg),
                        [Cconst_symbol "caml_exn_Division_by_zero"])))

(* Division or modulo on boxed integers.  The overflow case min_int / -1
   can occur, in which case we force x / -1 = -x and x mod -1 = 0. (PR#5513). *)

soit is_different_from x = fonction
    Cconst_int n -> n <> x
  | Cconst_natint n -> n <> Nativeint.of_int x
  | _ -> faux

soit safe_divmod_bi mkop mkm1 c1 c2 bi dbg =
  bind "dividend" c1 (fonc c1 ->
  bind "divisor" c2 (fonc c2 ->
    soit c = mkop c1 c2 dbg dans
    si Arch.division_crashes_on_overflow
    && (size_int = 4 || bi <> Pint32)
    && not (is_different_from (-1) c2)
    alors Cifthenelse(Cop(Ccmpi Cne, [c2; Cconst_int(-1)]), c, mkm1 c1)
    sinon c))

soit safe_div_bi =
  safe_divmod_bi div_int (fonc c1 -> Cop(Csubi, [Cconst_int 0; c1]))

soit safe_mod_bi =
  safe_divmod_bi mod_int (fonc c1 -> Cconst_int 0)

(* Bool *)

soit test_bool = fonction
    Cop(Caddi, [Cop(Clsl, [c; Cconst_int 1]); Cconst_int 1]) -> c
  | Cop(Clsl, [c; Cconst_int 1]) -> c
  | c -> Cop(Ccmpi Cne, [c; Cconst_int 1])

(* Float *)

soit box_float c = Cop(Calloc, [alloc_float_header; c])

soit rec unbox_float = fonction
    Cop(Calloc, [header; c]) -> c
  | Clet(id, exp, body) -> Clet(id, exp, unbox_float body)
  | Cifthenelse(cond, e1, e2) ->
      Cifthenelse(cond, unbox_float e1, unbox_float e2)
  | Csequence(e1, e2) -> Csequence(e1, unbox_float e2)
  | Cswitch(e, tbl, el) -> Cswitch(e, tbl, Array.map unbox_float el)
  | Ccatch(n, ids, e1, e2) -> Ccatch(n, ids, unbox_float e1, unbox_float e2)
  | Ctrywith(e1, id, e2) -> Ctrywith(unbox_float e1, id, unbox_float e2)
  | c -> Cop(Cload Double_u, [c])

(* Complex *)

soit box_complex c_re c_im =
  Cop(Calloc, [alloc_floatarray_header 2; c_re; c_im])

soit complex_re c = Cop(Cload Double_u, [c])
soit complex_im c = Cop(Cload Double_u,
                       [Cop(Cadda, [c; Cconst_int size_float])])

(* Unit *)

soit return_unit c = Csequence(c, Cconst_pointer 1)

soit rec remove_unit = fonction
    Cconst_pointer 1 -> Ctuple []
  | Csequence(c, Cconst_pointer 1) -> c
  | Csequence(c1, c2) ->
      Csequence(c1, remove_unit c2)
  | Cifthenelse(cond, ifso, ifnot) ->
      Cifthenelse(cond, remove_unit ifso, remove_unit ifnot)
  | Cswitch(sel, index, cases) ->
      Cswitch(sel, index, Array.map remove_unit cases)
  | Ccatch(io, ids, body, handler) ->
      Ccatch(io, ids, remove_unit body, remove_unit handler)
  | Ctrywith(body, exn, handler) ->
      Ctrywith(remove_unit body, exn, remove_unit handler)
  | Clet(id, c1, c2) ->
      Clet(id, c1, remove_unit c2)
  | Cop(Capply (mty, dbg), args) ->
      Cop(Capply (typ_void, dbg), args)
  | Cop(Cextcall(proc, mty, alloc, dbg), args) ->
      Cop(Cextcall(proc, typ_void, alloc, dbg), args)
  | Cexit (_,_) tel c -> c
  | Ctuple [] tel c -> c
  | c -> Csequence(c, Ctuple [])

(* Access to block fields *)

soit field_address ptr n =
  si n = 0
  alors ptr
  sinon Cop(Cadda, [ptr; Cconst_int(n * size_addr)])

soit get_field ptr n =
  Cop(Cload Word, [field_address ptr n])

soit set_field ptr n newval =
  Cop(Cstore Word, [field_address ptr n; newval])

soit header ptr =
  Cop(Cload Word, [Cop(Cadda, [ptr; Cconst_int(-size_int)])])

soit tag_offset =
  si big_endian alors -1 sinon -size_int

soit get_tag ptr =
  si Proc.word_addressed alors           (* If byte loads are slow *)
    Cop(Cand, [header ptr; Cconst_int 255])
  sinon                                  (* If byte loads are efficient *)
    Cop(Cload Byte_unsigned,
        [Cop(Cadda, [ptr; Cconst_int(tag_offset)])])

soit get_size ptr =
  Cop(Clsr, [header ptr; Cconst_int 10])

(* Array indexing *)

soit log2_size_addr = Misc.log2 size_addr
soit log2_size_float = Misc.log2 size_float

soit wordsize_shift = 9
soit numfloat_shift = 9 + log2_size_float - log2_size_addr

soit is_addr_array_hdr hdr =
  Cop(Ccmpi Cne, [Cop(Cand, [hdr; Cconst_int 255]); floatarray_tag])

soit is_addr_array_ptr ptr =
  Cop(Ccmpi Cne, [get_tag ptr; floatarray_tag])

soit addr_array_length hdr = Cop(Clsr, [hdr; Cconst_int wordsize_shift])
soit float_array_length hdr = Cop(Clsr, [hdr; Cconst_int numfloat_shift])

soit lsl_const c n =
  Cop(Clsl, [c; Cconst_int n])

soit array_indexing log2size ptr ofs =
  filtre ofs avec
    Cconst_int n ->
      soit i = n dda 1 dans
      si i = 0 alors ptr sinon Cop(Cadda, [ptr; Cconst_int(i dgl log2size)])
  | Cop(Caddi, [Cop(Clsl, [c; Cconst_int 1]); Cconst_int 1]) ->
      Cop(Cadda, [ptr; lsl_const c log2size])
  | Cop(Caddi, [c; Cconst_int n]) ->
      Cop(Cadda, [Cop(Cadda, [ptr; lsl_const c (log2size - 1)]);
                   Cconst_int((n-1) dgl (log2size - 1))])
  | _ ->
      Cop(Cadda, [Cop(Cadda, [ptr; lsl_const ofs (log2size - 1)]);
                   Cconst_int((-1) dgl (log2size - 1))])

soit addr_array_ref arr ofs =
  Cop(Cload Word, [array_indexing log2_size_addr arr ofs])
soit unboxed_float_array_ref arr ofs =
  Cop(Cload Double_u, [array_indexing log2_size_float arr ofs])
soit float_array_ref arr ofs =
  box_float(unboxed_float_array_ref arr ofs)

soit addr_array_set arr ofs newval =
  Cop(Cextcall("caml_modify", typ_void, faux, Debuginfo.none),
      [array_indexing log2_size_addr arr ofs; newval])
soit int_array_set arr ofs newval =
  Cop(Cstore Word, [array_indexing log2_size_addr arr ofs; newval])
soit float_array_set arr ofs newval =
  Cop(Cstore Double_u, [array_indexing log2_size_float arr ofs; newval])

(* String length *)

(* Length of string block *)

soit string_length exp =
  bind "str" exp (fonc str ->
    soit tmp_var = Ident.create "tmp" dans
    Clet(tmp_var,
         Cop(Csubi,
             [Cop(Clsl,
                   [get_size str;
                     Cconst_int log2_size_addr]);
              Cconst_int 1]),
         Cop(Csubi,
             [Cvar tmp_var;
               Cop(Cload Byte_unsigned,
                     [Cop(Cadda, [str; Cvar tmp_var])])])))

(* Message sending *)

soit lookup_tag obj tag =
  bind "tag" tag (fonc tag ->
    Cop(Cextcall("caml_get_public_method", typ_addr, faux, Debuginfo.none),
        [obj; tag]))

soit lookup_label obj lab =
  bind "lab" lab (fonc lab ->
    soit table = Cop (Cload Word, [obj]) dans
    addr_array_ref table lab)

soit call_cached_method obj tag cache pos args dbg =
  soit arity = List.length args dans
  soit cache = array_indexing log2_size_addr cache pos dans
  Compilenv.need_send_fun arity;
  Cop(Capply (typ_addr, dbg),
      Cconst_symbol("caml_send" ^ string_of_int arity) ::
      obj :: tag :: cache :: args)

(* Allocation *)

soit make_alloc_generic set_fn tag wordsize args =
  si wordsize <= Config.max_young_wosize alors
    Cop(Calloc, Cconst_blockheader(block_header tag wordsize) :: args)
  sinon début
    soit id = Ident.create "alloc" dans
    soit rec fill_fields idx = fonction
      [] -> Cvar id
    | e1::el -> Csequence(set_fn (Cvar id) (Cconst_int idx) e1,
                          fill_fields (idx + 2) el) dans
    Clet(id,
         Cop(Cextcall("caml_alloc", typ_addr, vrai, Debuginfo.none),
                 [Cconst_int wordsize; Cconst_int tag]),
         fill_fields 1 args)
  fin

soit make_alloc tag args =
  make_alloc_generic addr_array_set tag (List.length args) args
soit make_float_alloc tag args =
  make_alloc_generic float_array_set tag
                     (List.length args * size_float / size_addr) args

(* Bounds checking *)

soit make_checkbound dbg = fonction
  | [Cop(Clsr, [a1; Cconst_int n]); Cconst_int m] quand (m dgl n) > n ->
      Cop(Ccheckbound dbg, [a1; Cconst_int(m dgl n + 1 dgl n - 1)])
  | args ->
      Cop(Ccheckbound dbg, args)

(* To compile "let rec" over values *)

soit fundecls_size fundecls =
  soit sz = ref (-1) dans
  List.iter
    (fonc f -> sz := !sz + 1 + (si f.arity = 1 alors 2 sinon 3))
    fundecls;
  !sz

type rhs_kind =
  | RHS_block de int
  | RHS_floatblock de int
  | RHS_nonrec
;;
soit rec expr_size env = fonction
  | Uvar id ->
      début essaie Ident.find_same id env avec Not_found -> RHS_nonrec fin
  | Uclosure(fundecls, clos_vars) ->
      RHS_block (fundecls_size fundecls + List.length clos_vars)
  | Ulet(id, exp, body) ->
      expr_size (Ident.add id (expr_size env exp) env) body
  | Uletrec(bindings, body) ->
      expr_size env body
  | Uprim(Pmakeblock(tag, mut), args, _) ->
      RHS_block (List.length args)
  | Uprim(Pmakearray(Paddrarray | Pintarray), args, _) ->
      RHS_block (List.length args)
  | Uprim(Pmakearray(Pfloatarray), args, _) ->
      RHS_floatblock (List.length args)
  | Uprim (Pduprecord (Record_regular, sz), _, _) ->
      RHS_block sz
  | Uprim (Pduprecord (Record_float, sz), _, _) ->
      RHS_floatblock sz
  | Usequence(exp, exp') ->
      expr_size env exp'
  | _ -> RHS_nonrec

(* Record application and currying functions *)

soit apply_function n =
  Compilenv.need_apply_fun n; "caml_apply" ^ string_of_int n
soit curry_function n =
  Compilenv.need_curry_fun n;
  si n >= 0
  alors "caml_curry" ^ string_of_int n
  sinon "caml_tuplify" ^ string_of_int (-n)

(* Comparisons *)

soit transl_comparison = fonction
    Lambda.Ceq -> Ceq
  | Lambda.Cneq -> Cne
  | Lambda.Cge -> Cge
  | Lambda.Cgt -> Cgt
  | Lambda.Cle -> Cle
  | Lambda.Clt -> Clt

(* Translate structured constants *)

soit transl_constant = fonction
  | Uconst_int n ->
      int_const n
  | Uconst_ptr n ->
      si n <= max_repr_int && n >= min_repr_int
      alors Cconst_pointer((n dgl 1) + 1)
      sinon Cconst_natpointer
              (Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n)
  | Uconst_ref (label, _) ->
      Cconst_symbol label

soit transl_structured_constant cst =
  soit label = Compilenv.new_structured_constant cst ~shared:vrai dans
  Cconst_symbol label

(* Translate constant closures *)

soit constant_closures =
  ref ([] : (string * ufunction list) list)

(* Boxed integers *)

soit box_int_constant bi n =
  filtre bi avec
    Pnativeint -> Uconst_nativeint n
  | Pint32 -> Uconst_int32 (Nativeint.to_int32 n)
  | Pint64 -> Uconst_int64 (Int64.of_nativeint n)

soit operations_boxed_int bi =
  filtre bi avec
    Pnativeint -> "caml_nativeint_ops"
  | Pint32 -> "caml_int32_ops"
  | Pint64 -> "caml_int64_ops"

soit alloc_header_boxed_int bi =
  filtre bi avec
    Pnativeint -> alloc_boxedintnat_header
  | Pint32 -> alloc_boxedint32_header
  | Pint64 -> alloc_boxedint64_header

soit box_int bi arg =
  filtre arg avec
    Cconst_int n ->
      transl_structured_constant (box_int_constant bi (Nativeint.of_int n))
  | Cconst_natint n ->
      transl_structured_constant (box_int_constant bi n)
  | _ ->
      soit arg' =
        si bi = Pint32 && size_int = 8 && big_endian
        alors Cop(Clsl, [arg; Cconst_int 32])
        sinon arg dans
      Cop(Calloc, [alloc_header_boxed_int bi;
                   Cconst_symbol(operations_boxed_int bi);
                   arg'])

soit rec unbox_int bi arg =
  filtre arg avec
    Cop(Calloc, [hdr; ops; Cop(Clsl, [contents; Cconst_int 32])])
    quand bi = Pint32 && size_int = 8 && big_endian ->
      (* Force sign-extension of low 32 bits *)
      Cop(Casr, [Cop(Clsl, [contents; Cconst_int 32]); Cconst_int 32])
  | Cop(Calloc, [hdr; ops; contents])
    quand bi = Pint32 && size_int = 8 && not big_endian ->
      (* Force sign-extension of low 32 bits *)
      Cop(Casr, [Cop(Clsl, [contents; Cconst_int 32]); Cconst_int 32])
  | Cop(Calloc, [hdr; ops; contents]) ->
      contents
  | Clet(id, exp, body) -> Clet(id, exp, unbox_int bi body)
  | Cifthenelse(cond, e1, e2) ->
      Cifthenelse(cond, unbox_int bi e1, unbox_int bi e2)
  | Csequence(e1, e2) -> Csequence(e1, unbox_int bi e2)
  | Cswitch(e, tbl, el) -> Cswitch(e, tbl, Array.map (unbox_int bi) el)
  | Ccatch(n, ids, e1, e2) -> Ccatch(n, ids, unbox_int bi e1, unbox_int bi e2)
  | Ctrywith(e1, id, e2) -> Ctrywith(unbox_int bi e1, id, unbox_int bi e2)
  | _ ->
      Cop(Cload(si bi = Pint32 alors Thirtytwo_signed sinon Word),
          [Cop(Cadda, [arg; Cconst_int size_addr])])

soit make_unsigned_int bi arg =
  si bi = Pint32 && size_int = 8
  alors Cop(Cand, [arg; Cconst_natint 0xFFFFFFFFn])
  sinon arg

(* Big arrays *)

soit bigarray_elt_size = fonction
    Pbigarray_unknown -> affirme faux
  | Pbigarray_float32 -> 4
  | Pbigarray_float64 -> 8
  | Pbigarray_sint8 -> 1
  | Pbigarray_uint8 -> 1
  | Pbigarray_sint16 -> 2
  | Pbigarray_uint16 -> 2
  | Pbigarray_int32 -> 4
  | Pbigarray_int64 -> 8
  | Pbigarray_caml_int -> size_int
  | Pbigarray_native_int -> size_int
  | Pbigarray_complex32 -> 8
  | Pbigarray_complex64 -> 16

soit bigarray_indexing unsafe elt_kind layout b args dbg =
  soit check_bound a1 a2 k =
    si unsafe alors k sinon Csequence(make_checkbound dbg [a1;a2], k) dans
  soit rec ba_indexing dim_ofs delta_ofs = fonction
    [] -> affirme faux
  | [arg] ->
      bind "idx" (untag_int arg)
        (fonc idx ->
           check_bound (Cop(Cload Word,[field_address b dim_ofs])) idx idx)
  | arg1 :: argl ->
      soit rem = ba_indexing (dim_ofs + delta_ofs) delta_ofs argl dans
      bind "idx" (untag_int arg1)
        (fonc idx ->
          bind "bound" (Cop(Cload Word, [field_address b dim_ofs]))
          (fonc bound ->
            check_bound bound idx (add_int (mul_int rem bound) idx))) dans
  soit offset =
    filtre layout avec
      Pbigarray_unknown_layout ->
        affirme faux
    | Pbigarray_c_layout ->
        ba_indexing (4 + List.length args) (-1) (List.rev args)
    | Pbigarray_fortran_layout ->
        ba_indexing 5 1 (List.map (fonc idx -> sub_int idx (Cconst_int 2)) args)
  et elt_size =
    bigarray_elt_size elt_kind dans
  soit byte_offset =
    si elt_size = 1
    alors offset
    sinon Cop(Clsl, [offset; Cconst_int(log2 elt_size)]) dans
  Cop(Cadda, [Cop(Cload Word, [field_address b 1]); byte_offset])

soit bigarray_word_kind = fonction
    Pbigarray_unknown -> affirme faux
  | Pbigarray_float32 -> Single
  | Pbigarray_float64 -> Double
  | Pbigarray_sint8 -> Byte_signed
  | Pbigarray_uint8 -> Byte_unsigned
  | Pbigarray_sint16 -> Sixteen_signed
  | Pbigarray_uint16 -> Sixteen_unsigned
  | Pbigarray_int32 -> Thirtytwo_signed
  | Pbigarray_int64 -> Word
  | Pbigarray_caml_int -> Word
  | Pbigarray_native_int -> Word
  | Pbigarray_complex32 -> Single
  | Pbigarray_complex64 -> Double

soit bigarray_get unsafe elt_kind layout b args dbg =
  bind "ba" b (fonc b ->
    filtre elt_kind avec
      Pbigarray_complex32 | Pbigarray_complex64 ->
        soit kind = bigarray_word_kind elt_kind dans
        soit sz = bigarray_elt_size elt_kind / 2 dans
        bind "addr" (bigarray_indexing unsafe elt_kind layout b args dbg)
          (fonc addr ->
          box_complex
            (Cop(Cload kind, [addr]))
            (Cop(Cload kind, [Cop(Cadda, [addr; Cconst_int sz])])))
    | _ ->
        Cop(Cload (bigarray_word_kind elt_kind),
            [bigarray_indexing unsafe elt_kind layout b args dbg]))

soit bigarray_set unsafe elt_kind layout b args newval dbg =
  bind "ba" b (fonc b ->
    filtre elt_kind avec
      Pbigarray_complex32 | Pbigarray_complex64 ->
        soit kind = bigarray_word_kind elt_kind dans
        soit sz = bigarray_elt_size elt_kind / 2 dans
        bind "newval" newval (fonc newv ->
        bind "addr" (bigarray_indexing unsafe elt_kind layout b args dbg)
          (fonc addr ->
          Csequence(
            Cop(Cstore kind, [addr; complex_re newv]),
            Cop(Cstore kind,
                [Cop(Cadda, [addr; Cconst_int sz]); complex_im newv]))))
    | _ ->
        Cop(Cstore (bigarray_word_kind elt_kind),
            [bigarray_indexing unsafe elt_kind layout b args dbg; newval]))

soit unaligned_load_16 ptr idx =
  si Arch.allow_unaligned_access
  alors Cop(Cload Sixteen_unsigned, [add_int ptr idx])
  sinon
    soit v1 = Cop(Cload Byte_unsigned, [add_int ptr idx]) dans
    soit v2 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 1)]) dans
    soit b1, b2 = si Arch.big_endian alors v1, v2 sinon v2, v1 dans
    Cop(Cor, [lsl_int b1 (Cconst_int 8); b2])

soit unaligned_set_16 ptr idx newval =
  si Arch.allow_unaligned_access
  alors Cop(Cstore Sixteen_unsigned, [add_int ptr idx; newval])
  sinon
    soit v1 = Cop(Cand, [Cop(Clsr, [newval; Cconst_int 8]); Cconst_int 0xFF]) dans
    soit v2 = Cop(Cand, [newval; Cconst_int 0xFF]) dans
    soit b1, b2 = si Arch.big_endian alors v1, v2 sinon v2, v1 dans
    Csequence(
        Cop(Cstore Byte_unsigned, [add_int ptr idx; b1]),
        Cop(Cstore Byte_unsigned,
            [add_int (add_int ptr idx) (Cconst_int 1); b2]))

soit unaligned_load_32 ptr idx =
  si Arch.allow_unaligned_access
  alors Cop(Cload Thirtytwo_unsigned, [add_int ptr idx])
  sinon
    soit v1 = Cop(Cload Byte_unsigned, [add_int ptr idx]) dans
    soit v2 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 1)]) dans
    soit v3 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 2)]) dans
    soit v4 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 3)]) dans
    soit b1, b2, b3, b4 =
      si Arch.big_endian
      alors v1, v2, v3, v4
      sinon v4, v3, v2, v1 dans
    Cop(Cor,
        [Cop(Cor, [lsl_int b1 (Cconst_int 24); lsl_int b2 (Cconst_int 16)]);
         Cop(Cor, [lsl_int b3 (Cconst_int 8); b4])])

soit unaligned_set_32 ptr idx newval =
  si Arch.allow_unaligned_access
  alors Cop(Cstore Thirtytwo_unsigned, [add_int ptr idx; newval])
  sinon
    soit v1 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int 24]); Cconst_int 0xFF]) dans
    soit v2 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int 16]); Cconst_int 0xFF]) dans
    soit v3 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int 8]); Cconst_int 0xFF]) dans
    soit v4 = Cop(Cand, [newval; Cconst_int 0xFF]) dans
    soit b1, b2, b3, b4 =
      si Arch.big_endian
      alors v1, v2, v3, v4
      sinon v4, v3, v2, v1 dans
    Csequence(
        Csequence(
            Cop(Cstore Byte_unsigned, [add_int ptr idx; b1]),
            Cop(Cstore Byte_unsigned,
                [add_int (add_int ptr idx) (Cconst_int 1); b2])),
        Csequence(
            Cop(Cstore Byte_unsigned,
                [add_int (add_int ptr idx) (Cconst_int 2); b3]),
            Cop(Cstore Byte_unsigned,
                [add_int (add_int ptr idx) (Cconst_int 3); b4])))

soit unaligned_load_64 ptr idx =
  affirme(size_int = 8);
  si Arch.allow_unaligned_access
  alors Cop(Cload Word, [add_int ptr idx])
  sinon
    soit v1 = Cop(Cload Byte_unsigned, [add_int ptr idx]) dans
    soit v2 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 1)]) dans
    soit v3 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 2)]) dans
    soit v4 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 3)]) dans
    soit v5 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 4)]) dans
    soit v6 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 5)]) dans
    soit v7 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 6)]) dans
    soit v8 = Cop(Cload Byte_unsigned,
                 [add_int (add_int ptr idx) (Cconst_int 7)]) dans
    soit b1, b2, b3, b4, b5, b6, b7, b8 =
      si Arch.big_endian
      alors v1, v2, v3, v4, v5, v6, v7, v8
      sinon v8, v7, v6, v5, v4, v3, v2, v1 dans
    Cop(Cor,
        [Cop(Cor,
             [Cop(Cor, [lsl_int b1 (Cconst_int (8*7));
                        lsl_int b2 (Cconst_int (8*6))]);
              Cop(Cor, [lsl_int b3 (Cconst_int (8*5));
                        lsl_int b4 (Cconst_int (8*4))])]);
         Cop(Cor,
             [Cop(Cor, [lsl_int b5 (Cconst_int (8*3));
                        lsl_int b6 (Cconst_int (8*2))]);
              Cop(Cor, [lsl_int b7 (Cconst_int 8);
                        b8])])])

soit unaligned_set_64 ptr idx newval =
  affirme(size_int = 8);
  si Arch.allow_unaligned_access
  alors Cop(Cstore Word, [add_int ptr idx; newval])
  sinon
    soit v1 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int (8*7)]); Cconst_int 0xFF]) dans
    soit v2 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int (8*6)]); Cconst_int 0xFF]) dans
    soit v3 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int (8*5)]); Cconst_int 0xFF]) dans
    soit v4 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int (8*4)]); Cconst_int 0xFF]) dans
    soit v5 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int (8*3)]); Cconst_int 0xFF]) dans
    soit v6 =
      Cop(Cand, [Cop(Clsr, [newval; Cconst_int (8*2)]); Cconst_int 0xFF]) dans
    soit v7 = Cop(Cand, [Cop(Clsr, [newval; Cconst_int 8]); Cconst_int 0xFF]) dans
    soit v8 = Cop(Cand, [newval; Cconst_int 0xFF]) dans
    soit b1, b2, b3, b4, b5, b6, b7, b8 =
      si Arch.big_endian
      alors v1, v2, v3, v4, v5, v6, v7, v8
      sinon v8, v7, v6, v5, v4, v3, v2, v1 dans
    Csequence(
        Csequence(
            Csequence(
                Cop(Cstore Byte_unsigned, [add_int ptr idx; b1]),
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 1); b2])),
            Csequence(
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 2); b3]),
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 3); b4]))),
        Csequence(
            Csequence(
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 4); b5]),
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 5); b6])),
            Csequence(
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 6); b7]),
                Cop(Cstore Byte_unsigned,
                    [add_int (add_int ptr idx) (Cconst_int 7); b8]))))

soit check_bound unsafe dbg a1 a2 k =
  si unsafe alors k sinon Csequence(make_checkbound dbg [a1;a2], k)

(* Simplification of some primitives into C calls *)

soit default_prim name =
  { prim_name = name; prim_arity = 0 (*ignored*);
    prim_alloc = vrai; prim_native_name = ""; prim_native_float = faux }

soit simplif_primitive_32bits = fonction
    Pbintofint Pint64 -> Pccall (default_prim "caml_int64_of_int")
  | Pintofbint Pint64 -> Pccall (default_prim "caml_int64_to_int")
  | Pcvtbint(Pint32, Pint64) -> Pccall (default_prim "caml_int64_of_int32")
  | Pcvtbint(Pint64, Pint32) -> Pccall (default_prim "caml_int64_to_int32")
  | Pcvtbint(Pnativeint, Pint64) ->
      Pccall (default_prim "caml_int64_of_nativeint")
  | Pcvtbint(Pint64, Pnativeint) ->
      Pccall (default_prim "caml_int64_to_nativeint")
  | Pnegbint Pint64 -> Pccall (default_prim "caml_int64_neg")
  | Paddbint Pint64 -> Pccall (default_prim "caml_int64_add")
  | Psubbint Pint64 -> Pccall (default_prim "caml_int64_sub")
  | Pmulbint Pint64 -> Pccall (default_prim "caml_int64_mul")
  | Pdivbint Pint64 -> Pccall (default_prim "caml_int64_div")
  | Pmodbint Pint64 -> Pccall (default_prim "caml_int64_mod")
  | Pandbint Pint64 -> Pccall (default_prim "caml_int64_and")
  | Porbint Pint64 ->  Pccall (default_prim "caml_int64_or")
  | Pxorbint Pint64 -> Pccall (default_prim "caml_int64_xor")
  | Plslbint Pint64 -> Pccall (default_prim "caml_int64_shift_left")
  | Plsrbint Pint64 -> Pccall (default_prim "caml_int64_shift_right_unsigned")
  | Pasrbint Pint64 -> Pccall (default_prim "caml_int64_shift_right")
  | Pbintcomp(Pint64, Lambda.Ceq) -> Pccall (default_prim "caml_equal")
  | Pbintcomp(Pint64, Lambda.Cneq) -> Pccall (default_prim "caml_notequal")
  | Pbintcomp(Pint64, Lambda.Clt) -> Pccall (default_prim "caml_lessthan")
  | Pbintcomp(Pint64, Lambda.Cgt) -> Pccall (default_prim "caml_greaterthan")
  | Pbintcomp(Pint64, Lambda.Cle) -> Pccall (default_prim "caml_lessequal")
  | Pbintcomp(Pint64, Lambda.Cge) -> Pccall (default_prim "caml_greaterequal")
  | Pbigarrayref(unsafe, n, Pbigarray_int64, layout) ->
      Pccall (default_prim ("caml_ba_get_" ^ string_of_int n))
  | Pbigarrayset(unsafe, n, Pbigarray_int64, layout) ->
      Pccall (default_prim ("caml_ba_set_" ^ string_of_int n))
  | Pstring_load_64(_) -> Pccall (default_prim "caml_string_get64")
  | Pstring_set_64(_) -> Pccall (default_prim "caml_string_set64")
  | Pbigstring_load_64(_) -> Pccall (default_prim "caml_ba_uint8_get64")
  | Pbigstring_set_64(_) -> Pccall (default_prim "caml_ba_uint8_set64")
  | Pbbswap Pint64 -> Pccall (default_prim "caml_int64_bswap")
  | p -> p

soit simplif_primitive p =
  filtre p avec
  | Pduprecord _ ->
      Pccall (default_prim "caml_obj_dup")
  | Pbigarrayref(unsafe, n, Pbigarray_unknown, layout) ->
      Pccall (default_prim ("caml_ba_get_" ^ string_of_int n))
  | Pbigarrayset(unsafe, n, Pbigarray_unknown, layout) ->
      Pccall (default_prim ("caml_ba_set_" ^ string_of_int n))
  | Pbigarrayref(unsafe, n, kind, Pbigarray_unknown_layout) ->
      Pccall (default_prim ("caml_ba_get_" ^ string_of_int n))
  | Pbigarrayset(unsafe, n, kind, Pbigarray_unknown_layout) ->
      Pccall (default_prim ("caml_ba_set_" ^ string_of_int n))
  | p ->
      si size_int = 8 alors p sinon simplif_primitive_32bits p

(* Build switchers both for constants and blocks *)

(* constants first *)

soit transl_isout h arg = tag_int (Cop(Ccmpa Clt, [h ; arg]))

soit make_switch_gen arg cases acts =
  soit lcases = Array.length cases dans
  soit new_cases = Array.create lcases 0 dans
  soit store = Switch.mk_store (=) dans

  pour i = 0 à Array.length cases-1 faire
    soit act = cases.(i) dans
    soit new_act = store.Switch.act_store act dans
    new_cases.(i) <- new_act
  fait ;
  Cswitch
    (arg, new_cases,
     Array.map
       (fonc n -> acts.(n))
       (store.Switch.act_get ()))


(* Then for blocks *)

module SArgBlocks =
struct
  type primitive = operation

  soit eqint = Ccmpi Ceq
  soit neint = Ccmpi Cne
  soit leint = Ccmpi Cle
  soit ltint = Ccmpi Clt
  soit geint = Ccmpi Cge
  soit gtint = Ccmpi Cgt

  type act = expression

  soit default = Cexit (0,[])
  soit make_prim p args = Cop (p,args)
  soit make_offset arg n = add_const arg n
  soit make_isout h arg =  Cop (Ccmpa Clt, [h ; arg])
  soit make_isin h arg =  Cop (Ccmpa Cge, [h ; arg])
  soit make_if cond ifso ifnot = Cifthenelse (cond, ifso, ifnot)
  soit make_switch arg cases actions =
    make_switch_gen arg cases actions
  soit bind arg body = bind "switcher" arg body

fin

module SwitcherBlocks = Switch.Make(SArgBlocks)

(* Int switcher, arg in [low..high],
   cases is list of individual cases, and is sorted by first component *)

soit transl_int_switch arg low high cases default = filtre cases avec
| [] -> affirme faux
| (k0,_)::_ ->    
    soit nacts = List.length cases + 1 dans
    soit actions = Array.create nacts default dans
    soit rec set_acts idx = fonction
      | [] -> affirme faux
      | [i,act] ->
          actions.(idx) <- act ;
          si i = high alors [(i,i,idx)]
          sinon [(i,i,idx); (i+1,max_int,0)]
      | (i,act)::((j,_)::_ tel rem) ->
          actions.(idx) <- act ;
          soit inters = set_acts (idx+1) rem dans
          (i,i,idx)::
          début
            si j = i+1 alors inters
            sinon (i+1,j-1,0)::inters
          fin dans
    soit inters = set_acts 1 cases dans
    soit inters =
      si k0 = low alors inters sinon (low,k0-1,0)::inters dans
      bind "switcher" arg
        (fonc a ->
          SwitcherBlocks.zyva
            (low,high)
            (fonc i -> Cconst_int i)
            a
            (Array.of_list inters) actions)

        

(* Auxiliary functions for optimizing "let" of boxed numbers (floats and
   boxed integers *)

type unboxed_number_kind =
    No_unboxing
  | Boxed_float
  | Boxed_integer de boxed_integer

soit rec is_unboxed_number = fonction
    Uconst(Uconst_ref(_, Uconst_float _)) ->
      Boxed_float
  | Uprim(p, _, _) ->
      début filtre simplif_primitive p avec
          Pccall p -> si p.prim_native_float alors Boxed_float sinon No_unboxing
        | Pfloatfield _ -> Boxed_float
        | Pfloatofint -> Boxed_float
        | Pnegfloat -> Boxed_float
        | Pabsfloat -> Boxed_float
        | Paddfloat -> Boxed_float
        | Psubfloat -> Boxed_float
        | Pmulfloat -> Boxed_float
        | Pdivfloat -> Boxed_float
        | Parrayrefu Pfloatarray -> Boxed_float
        | Parrayrefs Pfloatarray -> Boxed_float
        | Pbintofint bi -> Boxed_integer bi
        | Pcvtbint(src, dst) -> Boxed_integer dst
        | Pnegbint bi -> Boxed_integer bi
        | Paddbint bi -> Boxed_integer bi
        | Psubbint bi -> Boxed_integer bi
        | Pmulbint bi -> Boxed_integer bi
        | Pdivbint bi -> Boxed_integer bi
        | Pmodbint bi -> Boxed_integer bi
        | Pandbint bi -> Boxed_integer bi
        | Porbint bi -> Boxed_integer bi
        | Pxorbint bi -> Boxed_integer bi
        | Plslbint bi -> Boxed_integer bi
        | Plsrbint bi -> Boxed_integer bi
        | Pasrbint bi -> Boxed_integer bi
        | Pbigarrayref(_, _, (Pbigarray_float32 | Pbigarray_float64), _) ->
            Boxed_float
        | Pbigarrayref(_, _, Pbigarray_int32, _) -> Boxed_integer Pint32
        | Pbigarrayref(_, _, Pbigarray_int64, _) -> Boxed_integer Pint64
        | Pbigarrayref(_, _, Pbigarray_native_int,_) -> Boxed_integer Pnativeint
        | Pstring_load_32(_) -> Boxed_integer Pint32
        | Pstring_load_64(_) -> Boxed_integer Pint64
        | Pbigstring_load_32(_) -> Boxed_integer Pint32
        | Pbigstring_load_64(_) -> Boxed_integer Pint64
        | Pbbswap bi -> Boxed_integer bi
        | _ -> No_unboxing
      fin
  | Ulet (_, _, e) | Usequence (_, e) -> is_unboxed_number e
  | _ -> No_unboxing

soit subst_boxed_number unbox_fn boxed_id unboxed_id box_chunk box_offset exp =
  soit need_boxed = ref faux dans
  soit assigned = ref faux dans
  soit rec subst = fonction
      Cvar id tel e ->
        si Ident.same id boxed_id alors need_boxed := vrai; e
    | Clet(id, arg, body) -> Clet(id, subst arg, subst body)
    | Cassign(id, arg) ->
        si Ident.same id boxed_id alors début
          assigned := vrai;
          Cassign(unboxed_id, subst(unbox_fn arg))
        fin sinon
          Cassign(id, subst arg)
    | Ctuple argv -> Ctuple(List.map subst argv)
    | Cop(Cload chunk, [Cvar id]) tel e ->
        si Ident.same id boxed_id && chunk = box_chunk && box_offset = 0
        alors Cvar unboxed_id
        sinon e
    | Cop(Cload chunk, [Cop(Cadda, [Cvar id; Cconst_int ofs])]) tel e ->
        si Ident.same id boxed_id && chunk = box_chunk && ofs = box_offset
        alors Cvar unboxed_id
        sinon e
    | Cop(op, argv) -> Cop(op, List.map subst argv)
    | Csequence(e1, e2) -> Csequence(subst e1, subst e2)
    | Cifthenelse(e1, e2, e3) -> Cifthenelse(subst e1, subst e2, subst e3)
    | Cswitch(arg, index, cases) ->
        Cswitch(subst arg, index, Array.map subst cases)
    | Cloop e -> Cloop(subst e)
    | Ccatch(nfail, ids, e1, e2) -> Ccatch(nfail, ids, subst e1, subst e2)
    | Cexit (nfail, el) -> Cexit (nfail, List.map subst el)
    | Ctrywith(e1, id, e2) -> Ctrywith(subst e1, id, subst e2)
    | e -> e dans
  soit res = subst exp dans
  (res, !need_boxed, !assigned)

(* Translate an expression *)

soit functions = (Queue.create() : ufunction Queue.t)

soit strmatch_compile =
  soit module S =
    Strmatch.Make
      (struct
        soit string_block_length = get_size
        soit transl_switch = transl_int_switch
      fin) dans
  S.compile
    
soit rec transl = fonction
    Uvar id ->
      Cvar id
  | Uconst sc ->
      transl_constant sc
  | Uclosure(fundecls, []) ->
      soit lbl = Compilenv.new_const_symbol() dans
      constant_closures := (lbl, fundecls) :: !constant_closures;
      List.iter (fonc f -> Queue.add f functions) fundecls;
      Cconst_symbol lbl
  | Uclosure(fundecls, clos_vars) ->
      soit block_size =
        fundecls_size fundecls + List.length clos_vars dans
      soit rec transl_fundecls pos = fonction
          [] ->
            List.map transl clos_vars
        | f :: rem ->
            Queue.add f functions;
            soit header =
              si pos = 0
              alors alloc_closure_header block_size
              sinon alloc_infix_header pos dans
            si f.arity = 1 alors
              header ::
              Cconst_symbol f.label ::
              int_const 1 ::
              transl_fundecls (pos + 3) rem
            sinon
              header ::
              Cconst_symbol(curry_function f.arity) ::
              int_const f.arity ::
              Cconst_symbol f.label ::
              transl_fundecls (pos + 4) rem dans
      Cop(Calloc, transl_fundecls 0 fundecls)
  | Uoffset(arg, offset) ->
      field_address (transl arg) offset
  | Udirect_apply(lbl, args, dbg) ->
      Cop(Capply(typ_addr, dbg), Cconst_symbol lbl :: List.map transl args)
  | Ugeneric_apply(clos, [arg], dbg) ->
      bind "fun" (transl clos) (fonc clos ->
        Cop(Capply(typ_addr, dbg), [get_field clos 0; transl arg; clos]))
  | Ugeneric_apply(clos, args, dbg) ->
      soit arity = List.length args dans
      soit cargs = Cconst_symbol(apply_function arity) ::
        List.map transl (args @ [clos]) dans
      Cop(Capply(typ_addr, dbg), cargs)
  | Usend(kind, met, obj, args, dbg) ->
      soit call_met obj args clos =
        si args = [] alors
          Cop(Capply(typ_addr, dbg), [get_field clos 0;obj;clos])
        sinon
          soit arity = List.length args + 1 dans
          soit cargs = Cconst_symbol(apply_function arity) :: obj ::
            (List.map transl args) @ [clos] dans
          Cop(Capply(typ_addr, dbg), cargs)
      dans
      bind "obj" (transl obj) (fonc obj ->
        filtre kind, args avec
          Self, _ ->
            bind "met" (lookup_label obj (transl met)) (call_met obj args)
        | Cached, cache :: pos :: args ->
            call_cached_method obj (transl met) (transl cache) (transl pos)
              (List.map transl args) dbg
        | _ ->
            bind "met" (lookup_tag obj (transl met)) (call_met obj args))
  | Ulet(id, exp, body) ->
      début filtre is_unboxed_number exp avec
        No_unboxing ->
          Clet(id, transl exp, transl body)
      | Boxed_float ->
          transl_unbox_let box_float unbox_float transl_unbox_float
                           Double_u 0
                           id exp body
      | Boxed_integer bi ->
          transl_unbox_let (box_int bi) (unbox_int bi) (transl_unbox_int bi)
                           (si bi = Pint32 alors Thirtytwo_signed sinon Word)
                           size_addr
                           id exp body
      fin
  | Uletrec(bindings, body) ->
      transl_letrec bindings (transl body)

  (* Primitives *)
  | Uprim(prim, args, dbg) ->
      début filtre (simplif_primitive prim, args) avec
        (Pgetglobal id, []) ->
          Cconst_symbol (Ident.name id)
      | (Pmakeblock(tag, mut), []) ->
          affirme faux
      | (Pmakeblock(tag, mut), args) ->
          make_alloc tag (List.map transl args)
      | (Pccall prim, args) ->
          si prim.prim_native_float alors
            box_float
              (Cop(Cextcall(prim.prim_native_name, typ_float, faux, dbg),
                   List.map transl_unbox_float args))
          sinon
            Cop(Cextcall(Primitive.native_name prim, typ_addr, prim.prim_alloc,
                         dbg),
                List.map transl args)
      | (Pmakearray kind, []) ->
          transl_structured_constant (Uconst_block(0, []))
      | (Pmakearray kind, args) ->
          début filtre kind avec
            Pgenarray ->
              Cop(Cextcall("caml_make_array", typ_addr, vrai, Debuginfo.none),
                  [make_alloc 0 (List.map transl args)])
          | Paddrarray | Pintarray ->
              make_alloc 0 (List.map transl args)
          | Pfloatarray ->
              make_float_alloc Obj.double_array_tag
                              (List.map transl_unbox_float args)
          fin
      | (Pbigarrayref(unsafe, num_dims, elt_kind, layout), arg1 :: argl) ->
          soit elt =
            bigarray_get unsafe elt_kind layout
              (transl arg1) (List.map transl argl) dbg dans
          début filtre elt_kind avec
            Pbigarray_float32 | Pbigarray_float64 -> box_float elt
          | Pbigarray_complex32 | Pbigarray_complex64 -> elt
          | Pbigarray_int32 -> box_int Pint32 elt
          | Pbigarray_int64 -> box_int Pint64 elt
          | Pbigarray_native_int -> box_int Pnativeint elt
          | Pbigarray_caml_int -> force_tag_int elt
          | _ -> tag_int elt
          fin
      | (Pbigarrayset(unsafe, num_dims, elt_kind, layout), arg1 :: argl) ->
          soit (argidx, argnewval) = split_last argl dans
          return_unit(bigarray_set unsafe elt_kind layout
            (transl arg1)
            (List.map transl argidx)
            (filtre elt_kind avec
              Pbigarray_float32 | Pbigarray_float64 ->
                transl_unbox_float argnewval
            | Pbigarray_complex32 | Pbigarray_complex64 -> transl argnewval
            | Pbigarray_int32 -> transl_unbox_int Pint32 argnewval
            | Pbigarray_int64 -> transl_unbox_int Pint64 argnewval
            | Pbigarray_native_int -> transl_unbox_int Pnativeint argnewval
            | _ -> untag_int (transl argnewval))
            dbg)
      | (Pbigarraydim(n), [b]) ->
          soit dim_ofs = 4 + n dans
          tag_int (Cop(Cload Word, [field_address (transl b) dim_ofs]))
      | (p, [arg]) ->
          transl_prim_1 p arg dbg
      | (p, [arg1; arg2]) ->
          transl_prim_2 p arg1 arg2 dbg
      | (p, [arg1; arg2; arg3]) ->
          transl_prim_3 p arg1 arg2 arg3 dbg
      | (_, _) ->
          fatal_error "Cmmgen.transl:prim"
      fin

  (* Control structures *)
  | Uswitch(arg, s) ->
      (* As in the bytecode interpreter, only matching against constants
         can be checked *)
      si Array.length s.us_index_blocks = 0 alors
        Cswitch
          (untag_int (transl arg),
           s.us_index_consts,
           Array.map transl s.us_actions_consts)
      sinon si Array.length s.us_index_consts = 0 alors
        transl_switch (get_tag (transl arg))
          s.us_index_blocks s.us_actions_blocks
      sinon
        bind "switch" (transl arg) (fonc arg ->
          Cifthenelse(
          Cop(Cand, [arg; Cconst_int 1]),
          transl_switch
            (untag_int arg) s.us_index_consts s.us_actions_consts,
          transl_switch
            (get_tag arg) s.us_index_blocks s.us_actions_blocks))
  | Ustringswitch(arg,sw,d) ->
      bind "switch" (transl arg)
        (fonc arg ->
          strmatch_compile arg (transl d)
            (List.map (fonc (s,act) -> s,transl act) sw))
  | Ustaticfail (nfail, args) ->
      Cexit (nfail, List.map transl args)
  | Ucatch(nfail, [], body, handler) ->
      make_catch nfail (transl body) (transl handler)
  | Ucatch(nfail, ids, body, handler) ->
      Ccatch(nfail, ids, transl body, transl handler)
  | Utrywith(body, exn, handler) ->
      Ctrywith(transl body, exn, transl handler)
  | Uifthenelse(Uprim(Pnot, [arg], _), ifso, ifnot) ->
      transl (Uifthenelse(arg, ifnot, ifso))
  | Uifthenelse(cond, ifso, Ustaticfail (nfail, [])) ->
      exit_if_false cond (transl ifso) nfail
  | Uifthenelse(cond, Ustaticfail (nfail, []), ifnot) ->
      exit_if_true cond nfail (transl ifnot)
  | Uifthenelse(Uprim(Psequand, _, _) tel cond, ifso, ifnot) ->
      soit raise_num = next_raise_count () dans
      make_catch
        raise_num
        (exit_if_false cond (transl ifso) raise_num)
        (transl ifnot)
  | Uifthenelse(Uprim(Psequor, _, _) tel cond, ifso, ifnot) ->
      soit raise_num = next_raise_count () dans
      make_catch
        raise_num
        (exit_if_true cond raise_num (transl ifnot))
        (transl ifso)
  | Uifthenelse (Uifthenelse (cond, condso, condnot), ifso, ifnot) ->
      soit num_true = next_raise_count () dans
      make_catch
        num_true
        (make_catch2
           (fonc shared_false ->
             Cifthenelse
               (test_bool (transl cond),
                exit_if_true condso num_true shared_false,
                exit_if_true condnot num_true shared_false))
           (transl ifnot))
        (transl ifso)
  | Uifthenelse(cond, ifso, ifnot) ->
      Cifthenelse(test_bool(transl cond), transl ifso, transl ifnot)
  | Usequence(exp1, exp2) ->
      Csequence(remove_unit(transl exp1), transl exp2)
  | Uwhile(cond, body) ->
      soit raise_num = next_raise_count () dans
      return_unit
        (Ccatch
           (raise_num, [],
            Cloop(exit_if_false cond (remove_unit(transl body)) raise_num),
            Ctuple []))
  | Ufor(id, low, high, dir, body) ->
      soit tst = filtre dir avec Upto -> Cgt   | Downto -> Clt dans
      soit inc = filtre dir avec Upto -> Caddi | Downto -> Csubi dans
      soit raise_num = next_raise_count () dans
      soit id_prev = Ident.rename id dans
      return_unit
        (Clet
           (id, transl low,
            bind_nonvar "bound" (transl high) (fonc high ->
              Ccatch
                (raise_num, [],
                 Cifthenelse
                   (Cop(Ccmpi tst, [Cvar id; high]), Cexit (raise_num, []),
                    Cloop
                      (Csequence
                         (remove_unit(transl body),
                         Clet(id_prev, Cvar id,
                          Csequence
                            (Cassign(id,
                               Cop(inc, [Cvar id; Cconst_int 2])),
                             Cifthenelse
                               (Cop(Ccmpi Ceq, [Cvar id_prev; high]),
                                Cexit (raise_num,[]), Ctuple [])))))),
                 Ctuple []))))
  | Uassign(id, exp) ->
      return_unit(Cassign(id, transl exp))

et transl_prim_1 p arg dbg =
  filtre p avec
  (* Generic operations *)
    Pidentity ->
      transl arg
  | Pignore ->
      return_unit(remove_unit (transl arg))
  (* Heap operations *)
  | Pfield n ->
      get_field (transl arg) n
  | Pfloatfield n ->
      soit ptr = transl arg dans
      box_float(
        Cop(Cload Double_u,
            [si n = 0 alors ptr
                       sinon Cop(Cadda, [ptr; Cconst_int(n * size_float)])]))
  (* Exceptions *)
  | Praise k ->
      Cop(Craise (k, dbg), [transl arg])
  (* Integer operations *)
  | Pnegint ->
      Cop(Csubi, [Cconst_int 2; transl arg])
  | Pctconst c ->
      soit const_of_bool b = tag_int (Cconst_int (si b alors 1 sinon 0)) dans
      début
        filtre c avec
        | Big_endian -> const_of_bool Arch.big_endian
        | Word_size -> tag_int (Cconst_int (8*Arch.size_int))
        | Ostype_unix -> const_of_bool (Sys.os_type = "Unix")
        | Ostype_win32 -> const_of_bool (Sys.os_type = "Win32")
        | Ostype_cygwin -> const_of_bool (Sys.os_type = "Cygwin")
      fin
  | Poffsetint n ->
      si no_overflow_lsl n alors
        add_const (transl arg) (n dgl 1)
      sinon
        transl_prim_2 Paddint arg (Uconst (Uconst_int n))
                      Debuginfo.none
  | Poffsetref n ->
      return_unit
        (bind "ref" (transl arg) (fonc arg ->
          Cop(Cstore Word,
              [arg; add_const (Cop(Cload Word, [arg])) (n dgl 1)])))
  (* Floating-point operations *)
  | Pfloatofint ->
      box_float(Cop(Cfloatofint, [untag_int(transl arg)]))
  | Pintoffloat ->
     tag_int(Cop(Cintoffloat, [transl_unbox_float arg]))
  | Pnegfloat ->
      box_float(Cop(Cnegf, [transl_unbox_float arg]))
  | Pabsfloat ->
      box_float(Cop(Cabsf, [transl_unbox_float arg]))
  (* String operations *)
  | Pstringlength ->
      tag_int(string_length (transl arg))
  (* Array operations *)
  | Parraylength kind ->
      début filtre kind avec
        Pgenarray ->
          soit len =
            si wordsize_shift = numfloat_shift alors
              Cop(Clsr, [header(transl arg); Cconst_int wordsize_shift])
            sinon
              bind "header" (header(transl arg)) (fonc hdr ->
                Cifthenelse(is_addr_array_hdr hdr,
                            Cop(Clsr, [hdr; Cconst_int wordsize_shift]),
                            Cop(Clsr, [hdr; Cconst_int numfloat_shift]))) dans
          Cop(Cor, [len; Cconst_int 1])
      | Paddrarray | Pintarray ->
          Cop(Cor, [addr_array_length(header(transl arg)); Cconst_int 1])
      | Pfloatarray ->
          Cop(Cor, [float_array_length(header(transl arg)); Cconst_int 1])
      fin
  (* Boolean operations *)
  | Pnot ->
      Cop(Csubi, [Cconst_int 4; transl arg]) (* 1 -> 3, 3 -> 1 *)
  (* Test integer/block *)
  | Pisint ->
      tag_int(Cop(Cand, [transl arg; Cconst_int 1]))
  (* Boxed integers *)
  | Pbintofint bi ->
      box_int bi (untag_int (transl arg))
  | Pintofbint bi ->
      force_tag_int (transl_unbox_int bi arg)
  | Pcvtbint(bi1, bi2) ->
      box_int bi2 (transl_unbox_int bi1 arg)
  | Pnegbint bi ->
      box_int bi (Cop(Csubi, [Cconst_int 0; transl_unbox_int bi arg]))
  | Pbbswap bi ->
      soit prim = filtre bi avec
        | Pnativeint -> "nativeint"
        | Pint32 -> "int32"
        | Pint64 -> "int64" dans
      box_int bi (Cop(Cextcall(Printf.sprintf "caml_%s_direct_bswap" prim,
                               typ_int, faux, Debuginfo.none),
                      [transl_unbox_int bi arg]))
  | Pbswap16 ->
      tag_int (Cop(Cextcall("caml_bswap16_direct", typ_int, faux,
                            Debuginfo.none),
                   [untag_int (transl arg)]))
  | _ ->
      fatal_error "Cmmgen.transl_prim_1"

et transl_prim_2 p arg1 arg2 dbg =
  filtre p avec
  (* Heap operations *)
    Psetfield(n, ptr) ->
      si ptr alors
        return_unit(Cop(Cextcall("caml_modify", typ_void, faux,Debuginfo.none),
                        [field_address (transl arg1) n; transl arg2]))
      sinon
        return_unit(set_field (transl arg1) n (transl arg2))
  | Psetfloatfield n ->
      soit ptr = transl arg1 dans
      return_unit(
        Cop(Cstore Double_u,
            [si n = 0 alors ptr
                       sinon Cop(Cadda, [ptr; Cconst_int(n * size_float)]);
                   transl_unbox_float arg2]))

  (* Boolean operations *)
  | Psequand ->
      Cifthenelse(test_bool(transl arg1), transl arg2, Cconst_int 1)
      (* let id = Ident.create "res1" in
      Clet(id, transl arg1,
           Cifthenelse(test_bool(Cvar id), transl arg2, Cvar id)) *)
  | Psequor ->
      Cifthenelse(test_bool(transl arg1), Cconst_int 3, transl arg2)

  (* Integer operations *)
  | Paddint ->
      decr_int(add_int (transl arg1) (transl arg2))
  | Psubint ->
      incr_int(sub_int (transl arg1) (transl arg2))
  | Pmulint ->
      incr_int(mul_int (decr_int(transl arg1)) (untag_int(transl arg2)))
  | Pdivint ->
      tag_int(div_int (untag_int(transl arg1)) (untag_int(transl arg2)) dbg)
  | Pmodint ->
      tag_int(mod_int (untag_int(transl arg1)) (untag_int(transl arg2)) dbg)
  | Pandint ->
      Cop(Cand, [transl arg1; transl arg2])
  | Porint ->
      Cop(Cor, [transl arg1; transl arg2])
  | Pxorint ->
      Cop(Cor, [Cop(Cxor, [ignore_low_bit_int(transl arg1);
                           ignore_low_bit_int(transl arg2)]);
                Cconst_int 1])
  | Plslint ->
      incr_int(lsl_int (decr_int(transl arg1)) (untag_int(transl arg2)))
  | Plsrint ->
      Cop(Cor, [lsr_int (transl arg1) (untag_int(transl arg2));
                Cconst_int 1])
  | Pasrint ->
      Cop(Cor, [asr_int (transl arg1) (untag_int(transl arg2));
                Cconst_int 1])
  | Pintcomp cmp ->
      tag_int(Cop(Ccmpi(transl_comparison cmp), [transl arg1; transl arg2]))
  | Pisout ->
      transl_isout (transl arg1) (transl arg2)
  (* Float operations *)
  | Paddfloat ->
      box_float(Cop(Caddf,
                    [transl_unbox_float arg1; transl_unbox_float arg2]))
  | Psubfloat ->
      box_float(Cop(Csubf,
                    [transl_unbox_float arg1; transl_unbox_float arg2]))
  | Pmulfloat ->
      box_float(Cop(Cmulf,
                    [transl_unbox_float arg1; transl_unbox_float arg2]))
  | Pdivfloat ->
      box_float(Cop(Cdivf,
                    [transl_unbox_float arg1; transl_unbox_float arg2]))
  | Pfloatcomp cmp ->
      tag_int(Cop(Ccmpf(transl_comparison cmp),
                  [transl_unbox_float arg1; transl_unbox_float arg2]))

  (* String operations *)
  | Pstringrefu ->
      tag_int(Cop(Cload Byte_unsigned,
                  [add_int (transl arg1) (untag_int(transl arg2))]))
  | Pstringrefs ->
      tag_int
        (bind "str" (transl arg1) (fonc str ->
          bind "index" (untag_int (transl arg2)) (fonc idx ->
            Csequence(
              make_checkbound dbg [string_length str; idx],
              Cop(Cload Byte_unsigned, [add_int str idx])))))

  | Pstring_load_16(unsafe) ->
     tag_int
       (bind "str" (transl arg1) (fonc str ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
          check_bound unsafe dbg (sub_int (string_length str) (Cconst_int 1))
                      idx (unaligned_load_16 str idx))))

  | Pbigstring_load_16(unsafe) ->
     tag_int
       (bind "ba" (transl arg1) (fonc ba ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "ba_data" (Cop(Cload Word, [field_address ba 1])) (fonc ba_data ->
          check_bound unsafe dbg (sub_int (Cop(Cload Word,[field_address ba 5]))
                                          (Cconst_int 1)) idx
                      (unaligned_load_16 ba_data idx)))))

  | Pstring_load_32(unsafe) ->
     box_int Pint32
       (bind "str" (transl arg1) (fonc str ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
          check_bound unsafe dbg (sub_int (string_length str) (Cconst_int 3))
                      idx (unaligned_load_32 str idx))))

  | Pbigstring_load_32(unsafe) ->
     box_int Pint32
       (bind "ba" (transl arg1) (fonc ba ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "ba_data" (Cop(Cload Word, [field_address ba 1])) (fonc ba_data ->
          check_bound unsafe dbg (sub_int (Cop(Cload Word,[field_address ba 5]))
                                          (Cconst_int 3)) idx
                      (unaligned_load_32 ba_data idx)))))

  | Pstring_load_64(unsafe) ->
     box_int Pint64
       (bind "str" (transl arg1) (fonc str ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
          check_bound unsafe dbg (sub_int (string_length str) (Cconst_int 7))
                      idx (unaligned_load_64 str idx))))

  | Pbigstring_load_64(unsafe) ->
     box_int Pint64
       (bind "ba" (transl arg1) (fonc ba ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "ba_data" (Cop(Cload Word, [field_address ba 1])) (fonc ba_data ->
          check_bound unsafe dbg (sub_int (Cop(Cload Word,[field_address ba 5]))
                                          (Cconst_int 7)) idx
                      (unaligned_load_64 ba_data idx)))))

  (* Array operations *)
  | Parrayrefu kind ->
      début filtre kind avec
        Pgenarray ->
          bind "arr" (transl arg1) (fonc arr ->
            bind "index" (transl arg2) (fonc idx ->
              Cifthenelse(is_addr_array_ptr arr,
                          addr_array_ref arr idx,
                          float_array_ref arr idx)))
      | Paddrarray | Pintarray ->
          addr_array_ref (transl arg1) (transl arg2)
      | Pfloatarray ->
          float_array_ref (transl arg1) (transl arg2)
      fin
  | Parrayrefs kind ->
      début filtre kind avec
      | Pgenarray ->
          bind "index" (transl arg2) (fonc idx ->
          bind "arr" (transl arg1) (fonc arr ->
          bind "header" (header arr) (fonc hdr ->
            si wordsize_shift = numfloat_shift alors
              Csequence(make_checkbound dbg [addr_array_length hdr; idx],
                        Cifthenelse(is_addr_array_hdr hdr,
                                    addr_array_ref arr idx,
                                    float_array_ref arr idx))
            sinon
              Cifthenelse(is_addr_array_hdr hdr,
                Csequence(make_checkbound dbg [addr_array_length hdr; idx],
                          addr_array_ref arr idx),
                Csequence(make_checkbound dbg [float_array_length hdr; idx],
                          float_array_ref arr idx)))))
      | Paddrarray | Pintarray ->
          bind "index" (transl arg2) (fonc idx ->
          bind "arr" (transl arg1) (fonc arr ->
            Csequence(make_checkbound dbg [addr_array_length(header arr); idx],
                      addr_array_ref arr idx)))
      | Pfloatarray ->
          box_float(
            bind "index" (transl arg2) (fonc idx ->
            bind "arr" (transl arg1) (fonc arr ->
              Csequence(make_checkbound dbg
                                        [float_array_length(header arr); idx],
                        unboxed_float_array_ref arr idx))))
      fin

  (* Operations on bitvects *)
  | Pbittest ->
      bind "index" (untag_int(transl arg2)) (fonc idx ->
        tag_int(
          Cop(Cand, [Cop(Clsr, [Cop(Cload Byte_unsigned,
                                    [add_int (transl arg1)
                                      (Cop(Clsr, [idx; Cconst_int 3]))]);
                                Cop(Cand, [idx; Cconst_int 7])]);
                     Cconst_int 1])))

  (* Boxed integers *)
  | Paddbint bi ->
      box_int bi (Cop(Caddi,
                      [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | Psubbint bi ->
      box_int bi (Cop(Csubi,
                      [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | Pmulbint bi ->
      box_int bi (Cop(Cmuli,
                      [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | Pdivbint bi ->
      box_int bi (safe_div_bi
                      (transl_unbox_int bi arg1) (transl_unbox_int bi arg2)
                      bi dbg)
  | Pmodbint bi ->
      box_int bi (safe_mod_bi
                      (transl_unbox_int bi arg1) (transl_unbox_int bi arg2)
                      bi dbg)
  | Pandbint bi ->
      box_int bi (Cop(Cand,
                     [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | Porbint bi ->
      box_int bi (Cop(Cor,
                     [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | Pxorbint bi ->
      box_int bi (Cop(Cxor,
                     [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | Plslbint bi ->
      box_int bi (Cop(Clsl,
                     [transl_unbox_int bi arg1; untag_int(transl arg2)]))
  | Plsrbint bi ->
      box_int bi (Cop(Clsr,
                     [make_unsigned_int bi (transl_unbox_int bi arg1);
                      untag_int(transl arg2)]))
  | Pasrbint bi ->
      box_int bi (Cop(Casr,
                     [transl_unbox_int bi arg1; untag_int(transl arg2)]))
  | Pbintcomp(bi, cmp) ->
      tag_int (Cop(Ccmpi(transl_comparison cmp),
                     [transl_unbox_int bi arg1; transl_unbox_int bi arg2]))
  | _ ->
      fatal_error "Cmmgen.transl_prim_2"

et transl_prim_3 p arg1 arg2 arg3 dbg =
  filtre p avec
  (* String operations *)
    Pstringsetu ->
      return_unit(Cop(Cstore Byte_unsigned,
                      [add_int (transl arg1) (untag_int(transl arg2));
                        untag_int(transl arg3)]))
  | Pstringsets ->
      return_unit
        (bind "str" (transl arg1) (fonc str ->
          bind "index" (untag_int (transl arg2)) (fonc idx ->
            Csequence(
              make_checkbound dbg [string_length str; idx],
              Cop(Cstore Byte_unsigned,
                  [add_int str idx; untag_int(transl arg3)])))))

  (* Array operations *)
  | Parraysetu kind ->
      return_unit(début filtre kind avec
        Pgenarray ->
          bind "newval" (transl arg3) (fonc newval ->
            bind "index" (transl arg2) (fonc index ->
              bind "arr" (transl arg1) (fonc arr ->
                Cifthenelse(is_addr_array_ptr arr,
                            addr_array_set arr index newval,
                            float_array_set arr index (unbox_float newval)))))
      | Paddrarray ->
          addr_array_set (transl arg1) (transl arg2) (transl arg3)
      | Pintarray ->
          int_array_set (transl arg1) (transl arg2) (transl arg3)
      | Pfloatarray ->
          float_array_set (transl arg1) (transl arg2) (transl_unbox_float arg3)
      fin)
  | Parraysets kind ->
      return_unit(début filtre kind avec
      | Pgenarray ->
          bind "newval" (transl arg3) (fonc newval ->
          bind "index" (transl arg2) (fonc idx ->
          bind "arr" (transl arg1) (fonc arr ->
          bind "header" (header arr) (fonc hdr ->
            si wordsize_shift = numfloat_shift alors
              Csequence(make_checkbound dbg [addr_array_length hdr; idx],
                        Cifthenelse(is_addr_array_hdr hdr,
                                    addr_array_set arr idx newval,
                                    float_array_set arr idx
                                                    (unbox_float newval)))
            sinon
              Cifthenelse(is_addr_array_hdr hdr,
                Csequence(make_checkbound dbg [addr_array_length hdr; idx],
                          addr_array_set arr idx newval),
                Csequence(make_checkbound dbg [float_array_length hdr; idx],
                          float_array_set arr idx
                                          (unbox_float newval)))))))
      | Paddrarray ->
          bind "newval" (transl arg3) (fonc newval ->
          bind "index" (transl arg2) (fonc idx ->
          bind "arr" (transl arg1) (fonc arr ->
            Csequence(make_checkbound dbg [addr_array_length(header arr); idx],
                      addr_array_set arr idx newval))))
      | Pintarray ->
          bind "newval" (transl arg3) (fonc newval ->
          bind "index" (transl arg2) (fonc idx ->
          bind "arr" (transl arg1) (fonc arr ->
            Csequence(make_checkbound dbg [addr_array_length(header arr); idx],
                      int_array_set arr idx newval))))
      | Pfloatarray ->
          bind "newval" (transl_unbox_float arg3) (fonc newval ->
          bind "index" (transl arg2) (fonc idx ->
          bind "arr" (transl arg1) (fonc arr ->
            Csequence(make_checkbound dbg [float_array_length(header arr);idx],
                      float_array_set arr idx newval))))
      fin)

  | Pstring_set_16(unsafe) ->
     return_unit
       (bind "str" (transl arg1) (fonc str ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "newval" (untag_int (transl arg3)) (fonc newval ->
          check_bound unsafe dbg (sub_int (string_length str) (Cconst_int 1))
                      idx (unaligned_set_16 str idx newval)))))

  | Pbigstring_set_16(unsafe) ->
     return_unit
       (bind "ba" (transl arg1) (fonc ba ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "newval" (untag_int (transl arg3)) (fonc newval ->
        bind "ba_data" (Cop(Cload Word, [field_address ba 1])) (fonc ba_data ->
          check_bound unsafe dbg (sub_int (Cop(Cload Word,[field_address ba 5]))
                                          (Cconst_int 1))
                      idx (unaligned_set_16 ba_data idx newval))))))

  | Pstring_set_32(unsafe) ->
     return_unit
       (bind "str" (transl arg1) (fonc str ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "newval" (transl_unbox_int Pint32 arg3) (fonc newval ->
          check_bound unsafe dbg (sub_int (string_length str) (Cconst_int 3))
                      idx (unaligned_set_32 str idx newval)))))

  | Pbigstring_set_32(unsafe) ->
     return_unit
       (bind "ba" (transl arg1) (fonc ba ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "newval" (transl_unbox_int Pint32 arg3) (fonc newval ->
        bind "ba_data" (Cop(Cload Word, [field_address ba 1])) (fonc ba_data ->
          check_bound unsafe dbg (sub_int (Cop(Cload Word,[field_address ba 5]))
                                          (Cconst_int 3))
                      idx (unaligned_set_32 ba_data idx newval))))))

  | Pstring_set_64(unsafe) ->
     return_unit
       (bind "str" (transl arg1) (fonc str ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "newval" (transl_unbox_int Pint64 arg3) (fonc newval ->
          check_bound unsafe dbg (sub_int (string_length str) (Cconst_int 7))
                      idx (unaligned_set_64 str idx newval)))))

  | Pbigstring_set_64(unsafe) ->
     return_unit
       (bind "ba" (transl arg1) (fonc ba ->
        bind "index" (untag_int (transl arg2)) (fonc idx ->
        bind "newval" (transl_unbox_int Pint64 arg3) (fonc newval ->
        bind "ba_data" (Cop(Cload Word, [field_address ba 1])) (fonc ba_data ->
          check_bound unsafe dbg (sub_int (Cop(Cload Word,[field_address ba 5]))
                                          (Cconst_int 7)) idx
                      (unaligned_set_64 ba_data idx newval))))))

  | _ ->
    fatal_error "Cmmgen.transl_prim_3"

et transl_unbox_float = fonction
    Uconst(Uconst_ref(_, Uconst_float f)) -> Cconst_float f
  | exp -> unbox_float(transl exp)

et transl_unbox_int bi = fonction
    Uconst(Uconst_ref(_, Uconst_int32 n)) ->
      Cconst_natint (Nativeint.of_int32 n)
  | Uconst(Uconst_ref(_, Uconst_nativeint n)) ->
      Cconst_natint n
  | Uconst(Uconst_ref(_, Uconst_int64 n)) ->
      affirme (size_int = 8); Cconst_natint (Int64.to_nativeint n)
  | Uprim(Pbintofint bi',[Uconst(Uconst_int i)],_) quand bi = bi' ->
      Cconst_int i
  | exp -> unbox_int bi (transl exp)

et transl_unbox_let box_fn unbox_fn transl_unbox_fn box_chunk box_offset 
                     id exp body =
  soit unboxed_id = Ident.create (Ident.name id) dans
  soit trbody1 = transl body dans
  soit (trbody2, need_boxed, is_assigned) =
    subst_boxed_number unbox_fn id unboxed_id box_chunk box_offset trbody1 dans
  si need_boxed && is_assigned alors
    Clet(id, transl exp, trbody1)
  sinon
    Clet(unboxed_id, transl_unbox_fn exp,
         si need_boxed
         alors Clet(id, box_fn(Cvar unboxed_id), trbody2)
         sinon trbody2)

et make_catch ncatch body handler = filtre body avec
| Cexit (nexit,[]) quand nexit=ncatch -> handler
| _ ->  Ccatch (ncatch, [], body, handler)

et make_catch2 mk_body handler = filtre handler avec
| Cexit (_,[])|Ctuple []|Cconst_int _|Cconst_pointer _ ->
    mk_body handler
| _ ->
    soit nfail = next_raise_count () dans
    make_catch
      nfail
      (mk_body (Cexit (nfail,[])))
      handler

et exit_if_true cond nfail otherwise =
  filtre cond avec
  | Uconst (Uconst_ptr 0) -> otherwise
  | Uconst (Uconst_ptr 1) -> Cexit (nfail,[])
  | Uprim(Psequor, [arg1; arg2], _) ->
      exit_if_true arg1 nfail (exit_if_true arg2 nfail otherwise)
  | Uprim(Psequand, _, _) ->
      début filtre otherwise avec
      | Cexit (raise_num,[]) ->
          exit_if_false cond (Cexit (nfail,[])) raise_num
      | _ ->
          soit raise_num = next_raise_count () dans
          make_catch
            raise_num
            (exit_if_false cond (Cexit (nfail,[])) raise_num)
            otherwise
      fin
  | Uprim(Pnot, [arg], _) ->
      exit_if_false arg otherwise nfail
  | Uifthenelse (cond, ifso, ifnot) ->
      make_catch2
        (fonc shared ->
          Cifthenelse
            (test_bool (transl cond),
             exit_if_true ifso nfail shared,
             exit_if_true ifnot nfail shared))
        otherwise
  | _ ->
      Cifthenelse(test_bool(transl cond), Cexit (nfail, []), otherwise)

et exit_if_false cond otherwise nfail =
  filtre cond avec
  | Uconst (Uconst_ptr 0) -> Cexit (nfail,[])
  | Uconst (Uconst_ptr 1) -> otherwise
  | Uprim(Psequand, [arg1; arg2], _) ->
      exit_if_false arg1 (exit_if_false arg2 otherwise nfail) nfail
  | Uprim(Psequor, _, _) ->
      début filtre otherwise avec
      | Cexit (raise_num,[]) ->
          exit_if_true cond raise_num (Cexit (nfail,[]))
      | _ ->
          soit raise_num = next_raise_count () dans
          make_catch
            raise_num
            (exit_if_true cond raise_num (Cexit (nfail,[])))
            otherwise
      fin
  | Uprim(Pnot, [arg], _) ->
      exit_if_true arg nfail otherwise
  | Uifthenelse (cond, ifso, ifnot) ->
      make_catch2
        (fonc shared ->
          Cifthenelse
            (test_bool (transl cond),
             exit_if_false ifso shared nfail,
             exit_if_false ifnot shared nfail))
        otherwise
  | _ ->
      Cifthenelse(test_bool(transl cond), otherwise, Cexit (nfail, []))

et transl_switch arg index cases = filtre Array.length cases avec
| 0 -> fatal_error "Cmmgen.transl_switch"
| 1 -> transl cases.(0)
| _ ->
    soit n_index = Array.length index dans
    soit actions = Array.map transl cases dans

    soit inters = ref []
    et this_high = ref (n_index-1)
    et this_low = ref (n_index-1)
    et this_act = ref index.(n_index-1) dans
    pour i = n_index-2 descendant_jusqu'a 0 faire
      soit act = index.(i) dans
      si act = !this_act alors
        decr this_low
      sinon début
        inters := (!this_low, !this_high, !this_act) :: !inters ;
        this_high := i ;
        this_low := i ;
        this_act := act
      fin
    fait ;
    inters := (0, !this_high, !this_act) :: !inters ;
    bind "switcher" arg
      (fonc a ->
        SwitcherBlocks.zyva
          (0,n_index-1)
          (fonc i -> Cconst_int i)
          a
          (Array.of_list !inters) actions)

et transl_letrec bindings cont =
  soit bsz =
    List.map (fonc (id, exp) -> (id, exp, expr_size Ident.empty exp)) bindings dans
  soit op_alloc prim sz =
    Cop(Cextcall(prim, typ_addr, vrai, Debuginfo.none), [int_const sz]) dans
  soit rec init_blocks = fonction
    | [] -> fill_nonrec bsz
    | (id, exp, RHS_block sz) :: rem ->
        Clet(id, op_alloc "caml_alloc_dummy" sz, init_blocks rem)
    | (id, exp, RHS_floatblock sz) :: rem ->
        Clet(id, op_alloc "caml_alloc_dummy_float" sz, init_blocks rem)
    | (id, exp, RHS_nonrec) :: rem ->
        Clet (id, Cconst_int 0, init_blocks rem)
  et fill_nonrec = fonction
    | [] -> fill_blocks bsz
    | (id, exp, (RHS_block _ | RHS_floatblock _)) :: rem ->
        fill_nonrec rem
    | (id, exp, RHS_nonrec) :: rem ->
        Clet (id, transl exp, fill_nonrec rem)
  et fill_blocks = fonction
    | [] -> cont
    | (id, exp, (RHS_block _ | RHS_floatblock _)) :: rem ->
        soit op =
          Cop(Cextcall("caml_update_dummy", typ_void, faux, Debuginfo.none),
              [Cvar id; transl exp]) dans
        Csequence(op, fill_blocks rem)
    | (id, exp, RHS_nonrec) :: rem ->
        fill_blocks rem
  dans init_blocks bsz

(* Translate a function definition *)

soit transl_function f =
  Cfunction {fun_name = f.label;
             fun_args = List.map (fonc id -> (id, typ_addr)) f.params;
             fun_body = transl f.body;
             fun_fast = !Clflags.optimize_for_speed;
             fun_dbg  = f.dbg; }

(* Translate all function definitions *)

module StringSet =
  Set.Make(struct
    type t = string
    soit compare (x:t) y = compare x y
  fin)

soit rec transl_all_functions already_translated cont =
  essaie
    soit f = Queue.take functions dans
    si StringSet.mem f.label already_translated alors
      transl_all_functions already_translated cont
    sinon début
      transl_all_functions
        (StringSet.add f.label already_translated)
        (transl_function f :: cont)
    fin
  avec Queue.Empty ->
    cont

(* Emit structured constants *)

soit emit_block header symb cont =
  Cint header :: Cdefine_symbol symb :: cont

soit rec emit_structured_constant symb cst cont =
  filtre cst avec
  | Uconst_float s->
      emit_block float_header symb (Cdouble s :: cont)
  | Uconst_string s ->
      emit_block (string_header (String.length s)) symb
        (emit_string_constant s cont)
  | Uconst_int32 n ->
      emit_block boxedint32_header symb
        (emit_boxed_int32_constant n cont)
  | Uconst_int64 n ->
      emit_block boxedint64_header symb
        (emit_boxed_int64_constant n cont)
  | Uconst_nativeint n ->
      emit_block boxedintnat_header symb
        (emit_boxed_nativeint_constant n cont)
  | Uconst_block (tag, csts) ->
      soit cont = List.fold_right emit_constant csts cont dans
      emit_block (block_header tag (List.length csts)) symb cont
  | Uconst_float_array fields ->
      emit_block (floatarray_header (List.length fields)) symb
        (Misc.map_end (fonc f -> Cdouble f) fields cont)

et emit_constant cst cont =
  filtre cst avec
  | Uconst_int n | Uconst_ptr n ->
      Cint(Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n) :: cont
  | Uconst_ref (label, _) ->
      Csymbol_address label :: cont

et emit_string_constant s cont =
  soit n = size_int - 1 - (String.length s) mod size_int dans
  Cstring s :: Cskip n :: Cint8 n :: cont

et emit_boxed_int32_constant n cont =
  soit n = Nativeint.of_int32 n dans
  si size_int = 8 alors
    Csymbol_address("caml_int32_ops") :: Cint32 n :: Cint32 0n :: cont
  sinon
    Csymbol_address("caml_int32_ops") :: Cint n :: cont

et emit_boxed_nativeint_constant n cont =
  Csymbol_address("caml_nativeint_ops") :: Cint n :: cont

et emit_boxed_int64_constant n cont =
  soit lo = Int64.to_nativeint n dans
  si size_int = 8 alors
    Csymbol_address("caml_int64_ops") :: Cint lo :: cont
  sinon début
    soit hi = Int64.to_nativeint (Int64.shift_right n 32) dans
    si big_endian alors
      Csymbol_address("caml_int64_ops") :: Cint hi :: Cint lo :: cont
    sinon
      Csymbol_address("caml_int64_ops") :: Cint lo :: Cint hi :: cont
  fin

(* Emit constant closures *)

soit emit_constant_closure symb fundecls cont =
  filtre fundecls avec
    [] -> affirme faux
  | f1 :: remainder ->
      soit rec emit_others pos = fonction
        [] -> cont
      | f2 :: rem ->
          si f2.arity = 1 alors
            Cint(infix_header pos) ::
            Csymbol_address f2.label ::
            Cint 3n ::
            emit_others (pos + 3) rem
          sinon
            Cint(infix_header pos) ::
            Csymbol_address(curry_function f2.arity) ::
            Cint(Nativeint.of_int (f2.arity dgl 1 + 1)) ::
            Csymbol_address f2.label ::
            emit_others (pos + 4) rem dans
      Cint(closure_header (fundecls_size fundecls)) ::
      Cdefine_symbol symb ::
      si f1.arity = 1 alors
        Csymbol_address f1.label ::
        Cint 3n ::
        emit_others 3 remainder
      sinon
        Csymbol_address(curry_function f1.arity) ::
        Cint(Nativeint.of_int (f1.arity dgl 1 + 1)) ::
        Csymbol_address f1.label ::
        emit_others 4 remainder

(* Emit all structured constants *)

soit emit_all_constants cont =
  soit c = ref cont dans
  List.iter
    (fonc (lbl, global, cst) ->
       soit cst = emit_structured_constant lbl cst [] dans
       soit cst = si global alors
         Cglobal_symbol lbl :: cst
       sinon cst dans
         c:= Cdata(cst):: !c)
    (Compilenv.structured_constants());
  List.iter
    (fonc (symb, fundecls) ->
        c := Cdata(emit_constant_closure symb fundecls []) :: !c)
    !constant_closures;
  constant_closures := [];
  !c

(* Translate a compilation unit *)

soit compunit size ulam =
  soit glob = Compilenv.make_symbol None dans
  soit init_code = transl ulam dans
  soit c1 = [Cfunction {fun_name = Compilenv.make_symbol (Some "entry");
                       fun_args = [];
                       fun_body = init_code; fun_fast = faux;
                       fun_dbg  = Debuginfo.none }] dans
  soit c2 = transl_all_functions StringSet.empty c1 dans
  soit c3 = emit_all_constants c2 dans
  Cdata [Cint(block_header 0 size);
         Cglobal_symbol glob;
         Cdefine_symbol glob;
         Cskip(size * size_addr)] :: c3

(*
CAMLprim value caml_cache_public_method (value meths, value tag, value *cache)
{
  int li = 3, hi = Field(meths,0), mi;
  while (li < hi) { // no need to check the 1st time
    mi = ((li+hi) >> 1) | 1;
    if (tag < Field(meths,mi)) hi = mi-2;
    else li = mi;
  }
  *cache = (li-3)*sizeof(value)+1;
  return Field (meths, li-1);
}
*)

soit cache_public_method meths tag cache =
  soit raise_num = next_raise_count () dans
  soit li = Ident.create "li" et hi = Ident.create "hi"
  et mi = Ident.create "mi" et tagged = Ident.create "tagged" dans
  Clet (
  li, Cconst_int 3,
  Clet (
  hi, Cop(Cload Word, [meths]),
  Csequence(
  Ccatch
    (raise_num, [],
     Cloop
       (Clet(
        mi,
        Cop(Cor,
            [Cop(Clsr, [Cop(Caddi, [Cvar li; Cvar hi]); Cconst_int 1]);
             Cconst_int 1]),
        Csequence(
        Cifthenelse
          (Cop (Ccmpi Clt,
                [tag;
                 Cop(Cload Word,
                     [Cop(Cadda,
                          [meths; lsl_const (Cvar mi) log2_size_addr])])]),
           Cassign(hi, Cop(Csubi, [Cvar mi; Cconst_int 2])),
           Cassign(li, Cvar mi)),
        Cifthenelse
          (Cop(Ccmpi Cge, [Cvar li; Cvar hi]), Cexit (raise_num, []),
           Ctuple [])))),
     Ctuple []),
  Clet (
  tagged, Cop(Cadda, [lsl_const (Cvar li) log2_size_addr;
                      Cconst_int(1 - 3 * size_addr)]),
  Csequence(Cop (Cstore Word, [cache; Cvar tagged]),
            Cvar tagged)))))

(* Generate an application function:
     (defun caml_applyN (a1 ... aN clos)
       (if (= clos.arity N)
         (app clos.direct a1 ... aN clos)
         (let (clos1 (app clos.code a1 clos)
               clos2 (app clos1.code a2 clos)
               ...
               closN-1 (app closN-2.code aN-1 closN-2))
           (app closN-1.code aN closN-1))))
*)

soit apply_function_body arity =
  soit arg = Array.create arity (Ident.create "arg") dans
  pour i = 1 à arity - 1 faire arg.(i) <- Ident.create "arg" fait;
  soit clos = Ident.create "clos" dans
  soit rec app_fun clos n =
    si n = arity-1 alors
      Cop(Capply(typ_addr, Debuginfo.none),
          [get_field (Cvar clos) 0; Cvar arg.(n); Cvar clos])
    sinon début
      soit newclos = Ident.create "clos" dans
      Clet(newclos,
           Cop(Capply(typ_addr, Debuginfo.none),
               [get_field (Cvar clos) 0; Cvar arg.(n); Cvar clos]),
           app_fun newclos (n+1))
    fin dans
  soit args = Array.to_list arg dans
  soit all_args = args @ [clos] dans
  (args, clos,
   si arity = 1 alors app_fun clos 0 sinon
   Cifthenelse(
   Cop(Ccmpi Ceq, [get_field (Cvar clos) 1; int_const arity]),
   Cop(Capply(typ_addr, Debuginfo.none),
       get_field (Cvar clos) 2 :: List.map (fonc s -> Cvar s) all_args),
   app_fun clos 0))

soit send_function arity =
  soit (args, clos', body) = apply_function_body (1+arity) dans
  soit cache = Ident.create "cache"
  et obj = List.hd args
  et tag = Ident.create "tag" dans
  soit clos =
    soit cache = Cvar cache et obj = Cvar obj et tag = Cvar tag dans
    soit meths = Ident.create "meths" et cached = Ident.create "cached" dans
    soit real = Ident.create "real" dans
    soit mask = get_field (Cvar meths) 1 dans
    soit cached_pos = Cvar cached dans
    soit tag_pos = Cop(Cadda, [Cop (Cadda, [cached_pos; Cvar meths]);
                              Cconst_int(3*size_addr-1)]) dans
    soit tag' = Cop(Cload Word, [tag_pos]) dans
    Clet (
    meths, Cop(Cload Word, [obj]),
    Clet (
    cached, Cop(Cand, [Cop(Cload Word, [cache]); mask]),
    Clet (
    real,
    Cifthenelse(Cop(Ccmpa Cne, [tag'; tag]),
                cache_public_method (Cvar meths) tag cache,
                cached_pos),
    Cop(Cload Word, [Cop(Cadda, [Cop (Cadda, [Cvar real; Cvar meths]);
                                 Cconst_int(2*size_addr-1)])]))))

  dans
  soit body = Clet(clos', clos, body) dans
  soit fun_args =
    [obj, typ_addr; tag, typ_int; cache, typ_addr]
    @ List.map (fonc id -> (id, typ_addr)) (List.tl args) dans
  Cfunction
   {fun_name = "caml_send" ^ string_of_int arity;
    fun_args = fun_args;
    fun_body = body;
    fun_fast = vrai;
    fun_dbg  = Debuginfo.none }

soit apply_function arity =
  soit (args, clos, body) = apply_function_body arity dans
  soit all_args = args @ [clos] dans
  Cfunction
   {fun_name = "caml_apply" ^ string_of_int arity;
    fun_args = List.map (fonc id -> (id, typ_addr)) all_args;
    fun_body = body;
    fun_fast = vrai;
    fun_dbg  = Debuginfo.none }

(* Generate tuplifying functions:
      (defun caml_tuplifyN (arg clos)
        (app clos.direct #0(arg) ... #N-1(arg) clos)) *)

soit tuplify_function arity =
  soit arg = Ident.create "arg" dans
  soit clos = Ident.create "clos" dans
  soit rec access_components i =
    si i >= arity
    alors []
    sinon get_field (Cvar arg) i :: access_components(i+1) dans
  Cfunction
   {fun_name = "caml_tuplify" ^ string_of_int arity;
    fun_args = [arg, typ_addr; clos, typ_addr];
    fun_body =
      Cop(Capply(typ_addr, Debuginfo.none),
          get_field (Cvar clos) 2 :: access_components 0 @ [Cvar clos]);
    fun_fast = vrai;
    fun_dbg  = Debuginfo.none }

(* Generate currying functions:
      (defun caml_curryN (arg clos)
         (alloc HDR caml_curryN_1 <arity (N-1)> caml_curry_N_1_app arg clos))
      (defun caml_curryN_1 (arg clos)
         (alloc HDR caml_curryN_2 <arity (N-2)> caml_curry_N_2_app arg clos))
      ...
      (defun caml_curryN_N-1 (arg clos)
         (let (closN-2 clos.vars[1]
               closN-3 closN-2.vars[1]
               ...
               clos1 clos2.vars[1]
               clos clos1.vars[1])
           (app clos.direct
                clos1.vars[0] ... closN-2.vars[0] clos.vars[0] arg clos)))

    Special "shortcut" functions are also generated to handle the
    case where a partially applied function is applied to all remaining
    arguments in one go.  For instance:
      (defun caml_curry_N_1_app (arg2 ... argN clos)
        (let clos' clos.vars[1]
           (app clos'.direct clos.vars[0] arg2 ... argN clos')))

    Those shortcuts may lead to a quadratic number of application
    primitives being generated in the worst case, which resulted in
    linking time blowup in practice (PR#5933), so we only generate and
    use them when below a fixed arity 'max_arity_optimized'.
*)

soit max_arity_optimized = 15
soit final_curry_function arity =
  soit last_arg = Ident.create "arg" dans
  soit last_clos = Ident.create "clos" dans
  soit rec curry_fun args clos n =
    si n = 0 alors
      Cop(Capply(typ_addr, Debuginfo.none),
          get_field (Cvar clos) 2 ::
          args @ [Cvar last_arg; Cvar clos])
    sinon
      si n = arity - 1 || arity > max_arity_optimized alors
        début
      soit newclos = Ident.create "clos" dans
      Clet(newclos,
           get_field (Cvar clos) 3,
           curry_fun (get_field (Cvar clos) 2 :: args) newclos (n-1))
        fin sinon
        début
          soit newclos = Ident.create "clos" dans
          Clet(newclos,
               get_field (Cvar clos) 4,
               curry_fun (get_field (Cvar clos) 3 :: args) newclos (n-1))
    fin dans
  Cfunction
   {fun_name = "caml_curry" ^ string_of_int arity ^
               "_" ^ string_of_int (arity-1);
    fun_args = [last_arg, typ_addr; last_clos, typ_addr];
    fun_body = curry_fun [] last_clos (arity-1);
    fun_fast = vrai;
    fun_dbg  = Debuginfo.none }

soit rec intermediate_curry_functions arity num =
  si num = arity - 1 alors
    [final_curry_function arity]
  sinon début
    soit name1 = "caml_curry" ^ string_of_int arity dans
    soit name2 = si num = 0 alors name1 sinon name1 ^ "_" ^ string_of_int num dans
    soit arg = Ident.create "arg" et clos = Ident.create "clos" dans
    Cfunction
     {fun_name = name2;
      fun_args = [arg, typ_addr; clos, typ_addr];
      fun_body =
         si arity - num > 2 && arity <= max_arity_optimized alors
           Cop(Calloc,
               [alloc_closure_header 5;
                Cconst_symbol(name1 ^ "_" ^ string_of_int (num+1));
                int_const (arity - num - 1);
                Cconst_symbol(name1 ^ "_" ^ string_of_int (num+1) ^ "_app");
                Cvar arg; Cvar clos])
         sinon
           Cop(Calloc,
                     [alloc_closure_header 4;
                      Cconst_symbol(name1 ^ "_" ^ string_of_int (num+1));
                      int_const 1; Cvar arg; Cvar clos]);
      fun_fast = vrai;
      fun_dbg  = Debuginfo.none }
    ::
      (si arity <= max_arity_optimized && arity - num > 2 alors
          soit rec iter i =
            si i <= arity alors
              soit arg = Ident.create (Printf.sprintf "arg%d" i) dans
              (arg, typ_addr) :: iter (i+1)
            sinon []
          dans
          soit direct_args = iter (num+2) dans
          soit rec iter i args clos =
            si i = 0 alors
              Cop(Capply(typ_addr, Debuginfo.none),
                  (get_field (Cvar clos) 2) :: args @ [Cvar clos])
            sinon
              soit newclos = Ident.create "clos" dans
              Clet(newclos,
                   get_field (Cvar clos) 4,
                   iter (i-1) (get_field (Cvar clos) 3 :: args) newclos)
          dans
          soit cf =
            Cfunction
              {fun_name = name1 ^ "_" ^ string_of_int (num+1) ^ "_app";
               fun_args = direct_args @ [clos, typ_addr];
               fun_body = iter (num+1)
                  (List.map (fonc (arg,_) -> Cvar arg) direct_args) clos;
               fun_fast = vrai;
               fun_dbg = Debuginfo.none }
          dans
          cf :: intermediate_curry_functions arity (num+1)
       sinon
          intermediate_curry_functions arity (num+1))
  fin

soit curry_function arity =
  si arity >= 0
  alors intermediate_curry_functions arity 0
  sinon [tuplify_function (-arity)]


module IntSet = Set.Make(
  struct
    type t = int
    soit compare (x:t) y = compare x y
  fin)

soit default_apply = IntSet.add 2 (IntSet.add 3 IntSet.empty)
  (* These apply funs are always present in the main program because
     the run-time system needs them (cf. asmrun/<arch>.S) . *)

soit generic_functions shared units =
  soit (apply,send,curry) =
    List.fold_left
      (fonc (apply,send,curry) ui ->
         List.fold_right IntSet.add ui.ui_apply_fun apply,
         List.fold_right IntSet.add ui.ui_send_fun send,
         List.fold_right IntSet.add ui.ui_curry_fun curry)
      (IntSet.empty,IntSet.empty,IntSet.empty)
      units dans
  soit apply = si shared alors apply sinon IntSet.union apply default_apply dans
  soit accu = IntSet.fold (fonc n accu -> apply_function n :: accu) apply [] dans
  soit accu = IntSet.fold (fonc n accu -> send_function n :: accu) send accu dans
  IntSet.fold (fonc n accu -> curry_function n @ accu) curry accu

(* Generate the entry point *)

soit entry_point namelist =
  soit incr_global_inited =
    Cop(Cstore Word,
        [Cconst_symbol "caml_globals_inited";
         Cop(Caddi, [Cop(Cload Word, [Cconst_symbol "caml_globals_inited"]);
                     Cconst_int 1])]) dans
  soit body =
    List.fold_right
      (fonc name next ->
        soit entry_sym = Compilenv.make_symbol ~unitname:name (Some "entry") dans
        Csequence(Cop(Capply(typ_void, Debuginfo.none),
                         [Cconst_symbol entry_sym]),
                  Csequence(incr_global_inited, next)))
      namelist (Cconst_int 1) dans
  Cfunction {fun_name = "caml_program";
             fun_args = [];
             fun_body = body;
             fun_fast = faux;
             fun_dbg  = Debuginfo.none }

(* Generate the table of globals *)

soit cint_zero = Cint 0n

soit global_table namelist =
  soit mksym name =
    Csymbol_address (Compilenv.make_symbol ~unitname:name None)
  dans
  Cdata(Cglobal_symbol "caml_globals" ::
        Cdefine_symbol "caml_globals" ::
        List.map mksym namelist @
        [cint_zero])

soit reference_symbols namelist =
  soit mksym name = Csymbol_address name dans
  Cdata(List.map mksym namelist)

soit global_data name v =
  Cdata(Cglobal_symbol name ::
          emit_structured_constant name
          (Uconst_string (Marshal.to_string v [])) [])

soit globals_map v = global_data "caml_globals_map" v

(* Generate the master table of frame descriptors *)

soit frame_table namelist =
  soit mksym name =
    Csymbol_address (Compilenv.make_symbol ~unitname:name (Some "frametable"))
  dans
  Cdata(Cglobal_symbol "caml_frametable" ::
        Cdefine_symbol "caml_frametable" ::
        List.map mksym namelist
        @ [cint_zero])

(* Generate the table of module data and code segments *)

soit segment_table namelist symbol begname endname =
  soit addsyms name lst =
    Csymbol_address (Compilenv.make_symbol ~unitname:name (Some begname)) ::
    Csymbol_address (Compilenv.make_symbol ~unitname:name (Some endname)) ::
    lst
  dans
  Cdata(Cglobal_symbol symbol ::
        Cdefine_symbol symbol ::
        List.fold_right addsyms namelist [cint_zero])

soit data_segment_table namelist =
  segment_table namelist "caml_data_segments" "data_begin" "data_end"

soit code_segment_table namelist =
  segment_table namelist "caml_code_segments" "code_begin" "code_end"

(* Initialize a predefined exception *)

soit predef_exception i name =
  soit symname = "caml_exn_" ^ name dans
  soit cst = Uconst_string name dans
  soit label = Compilenv.new_const_symbol () dans
  soit cont = emit_structured_constant label cst [] dans
  Cdata(Cglobal_symbol symname ::
        emit_structured_constant symname
          (Uconst_block(Obj.object_tag,
                       [
                         Uconst_ref(label, cst);
                         Uconst_int (-i-1);
                       ])) cont)

(* Header for a plugin *)

soit mapflat f l = List.flatten (List.map f l)

soit plugin_header units =
  soit mk (ui,crc) =
    { dynu_name = ui.ui_name;
      dynu_crc = crc;
      dynu_imports_cmi = ui.ui_imports_cmi;
      dynu_imports_cmx = ui.ui_imports_cmx;
      dynu_defines = ui.ui_defines
    } dans
  global_data "caml_plugin_header"
    { dynu_magic = Config.cmxs_magic_number; dynu_units = List.map mk units }
