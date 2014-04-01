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

ouvre Misc
ouvre Path
ouvre Asttypes

type compile_time_constant =
  | Big_endian
  | Word_size
  | Ostype_unix
  | Ostype_win32
  | Ostype_cygwin

type primitive =
    Pidentity
  | Pignore
  | Prevapply de Location.t
  | Pdirapply de Location.t
    (* Globals *)
  | Pgetglobal de Ident.t
  | Psetglobal de Ident.t
  (* Operations on heap blocks *)
  | Pmakeblock de int * mutable_flag
  | Pfield de int
  | Psetfield de int * bool
  | Pfloatfield de int
  | Psetfloatfield de int
  | Pduprecord de Types.record_representation * int
  (* Force lazy values *)
  | Plazyforce
  (* External call *)
  | Pccall de Primitive.description
  (* Exceptions *)
  | Praise de raise_kind
  (* Boolean operations *)
  | Psequand | Psequor | Pnot
  (* Integer operations *)
  | Pnegint | Paddint | Psubint | Pmulint | Pdivint | Pmodint
  | Pandint | Porint | Pxorint
  | Plslint | Plsrint | Pasrint
  | Pintcomp de comparison
  | Poffsetint de int
  | Poffsetref de int
  (* Float operations *)
  | Pintoffloat | Pfloatofint
  | Pnegfloat | Pabsfloat
  | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
  | Pfloatcomp de comparison
  (* String operations *)
  | Pstringlength | Pstringrefu | Pstringsetu | Pstringrefs | Pstringsets
  (* Array operations *)
  | Pmakearray de array_kind
  | Parraylength de array_kind
  | Parrayrefu de array_kind
  | Parraysetu de array_kind
  | Parrayrefs de array_kind
  | Parraysets de array_kind
  (* Test if the argument is a block or an immediate integer *)
  | Pisint
  (* Test if the (integer) argument is outside an interval *)
  | Pisout
  (* Bitvect operations *)
  | Pbittest
  (* Operations on boxed integers (Nativeint.t, Int32.t, Int64.t) *)
  | Pbintofint de boxed_integer
  | Pintofbint de boxed_integer
  | Pcvtbint de boxed_integer (*source*) * boxed_integer (*destination*)
  | Pnegbint de boxed_integer
  | Paddbint de boxed_integer
  | Psubbint de boxed_integer
  | Pmulbint de boxed_integer
  | Pdivbint de boxed_integer
  | Pmodbint de boxed_integer
  | Pandbint de boxed_integer
  | Porbint de boxed_integer
  | Pxorbint de boxed_integer
  | Plslbint de boxed_integer
  | Plsrbint de boxed_integer
  | Pasrbint de boxed_integer
  | Pbintcomp de boxed_integer * comparison
  (* Operations on big arrays: (unsafe, #dimensions, kind, layout) *)
  | Pbigarrayref de bool * int * bigarray_kind * bigarray_layout
  | Pbigarrayset de bool * int * bigarray_kind * bigarray_layout
  (* size of the nth dimension of a big array *)
  | Pbigarraydim de int
  (* load/set 16,32,64 bits from a string: (unsafe)*)
  | Pstring_load_16 de bool
  | Pstring_load_32 de bool
  | Pstring_load_64 de bool
  | Pstring_set_16 de bool
  | Pstring_set_32 de bool
  | Pstring_set_64 de bool
  (* load/set 16,32,64 bits from a
     (char, int8_unsigned_elt, c_layout) Bigarray.Array1.t : (unsafe) *)
  | Pbigstring_load_16 de bool
  | Pbigstring_load_32 de bool
  | Pbigstring_load_64 de bool
  | Pbigstring_set_16 de bool
  | Pbigstring_set_32 de bool
  | Pbigstring_set_64 de bool
  (* Compile time constants *)
  | Pctconst de compile_time_constant
  (* byte swap *)
  | Pbswap16
  | Pbbswap de boxed_integer

et comparison =
    Ceq | Cneq | Clt | Cgt | Cle | Cge

et array_kind =
    Pgenarray | Paddrarray | Pintarray | Pfloatarray

et boxed_integer =
    Pnativeint | Pint32 | Pint64

et bigarray_kind =
    Pbigarray_unknown
  | Pbigarray_float32 | Pbigarray_float64
  | Pbigarray_sint8 | Pbigarray_uint8
  | Pbigarray_sint16 | Pbigarray_uint16
  | Pbigarray_int32 | Pbigarray_int64
  | Pbigarray_caml_int | Pbigarray_native_int
  | Pbigarray_complex32 | Pbigarray_complex64

et bigarray_layout =
    Pbigarray_unknown_layout
  | Pbigarray_c_layout
  | Pbigarray_fortran_layout

et raise_kind =
  | Raise_regular
  | Raise_reraise
  | Raise_notrace

type structured_constant =
    Const_base de constant
  | Const_pointer de int
  | Const_block de int * structured_constant list
  | Const_float_array de string list
  | Const_immstring de string

type function_kind = Curried | Tupled

type let_kind = Strict | Alias | StrictOpt | Variable

type meth_kind = Self | Public | Cached

type shared_code = (int * int) list

type lambda =
    Lvar de Ident.t
  | Lconst de structured_constant
  | Lapply de lambda * lambda list * Location.t
  | Lfunction de function_kind * Ident.t list * lambda
  | Llet de let_kind * Ident.t * lambda * lambda
  | Lletrec de (Ident.t * lambda) list * lambda
  | Lprim de primitive * lambda list
  | Lswitch de lambda * lambda_switch
  | Lstringswitch de lambda * (string * lambda) list * lambda
  | Lstaticraise de int * lambda list
  | Lstaticcatch de lambda * (int * Ident.t list) * lambda
  | Ltrywith de lambda * Ident.t * lambda
  | Lifthenelse de lambda * lambda * lambda
  | Lsequence de lambda * lambda
  | Lwhile de lambda * lambda
  | Lfor de Ident.t * lambda * lambda * direction_flag * lambda
  | Lassign de Ident.t * lambda
  | Lsend de meth_kind * lambda * lambda * lambda list * Location.t
  | Levent de lambda * lambda_event
  | Lifused de Ident.t * lambda

et lambda_switch =
  { sw_numconsts: int;
    sw_consts: (int * lambda) list;
    sw_numblocks: int;
    sw_blocks: (int * lambda) list;
    sw_failaction : lambda option}

et lambda_event =
  { lev_loc: Location.t;
    lev_kind: lambda_event_kind;
    lev_repr: int ref option;
    lev_env: Env.summary }

et lambda_event_kind =
    Lev_before
  | Lev_after de Types.type_expr
  | Lev_function

soit const_unit = Const_pointer 0

soit lambda_unit = Lconst const_unit

soit rec same l1 l2 =
  filtre (l1, l2) avec
  | Lvar v1, Lvar v2 ->
      Ident.same v1 v2
  | Lconst (Const_base (Const_string _)), _ ->
      faux  (* do not share strings *)
  | Lconst c1, Lconst c2 ->
      c1 = c2
  | Lapply(a1, bl1, _), Lapply(a2, bl2, _) ->
      same a1 a2 && samelist same bl1 bl2
  | Lfunction(k1, idl1, a1), Lfunction(k2, idl2, a2) ->
      k1 = k2 && samelist Ident.same idl1 idl2 && same a1 a2
  | Llet(k1, id1, a1, b1), Llet(k2, id2, a2, b2) ->
      k1 = k2 && Ident.same id1 id2 && same a1 a2 && same b1 b2
  | Lletrec (bl1, a1), Lletrec (bl2, a2) ->
      samelist samebinding bl1 bl2 && same a1 a2
  | Lprim(p1, al1), Lprim(p2, al2) ->
      p1 = p2 && samelist same al1 al2
  | Lswitch(a1, s1), Lswitch(a2, s2) ->
      same a1 a2 && sameswitch s1 s2
  | Lstaticraise(n1, al1), Lstaticraise(n2, al2) ->
      n1 = n2 && samelist same al1 al2
  | Lstaticcatch(a1, (n1, idl1), b1), Lstaticcatch(a2, (n2, idl2), b2) ->
      same a1 a2 && n1 = n2 && samelist Ident.same idl1 idl2 && same b1 b2
  | Ltrywith(a1, id1, b1), Ltrywith(a2, id2, b2) ->
      same a1 a2 && Ident.same id1 id2 && same b1 b2
  | Lifthenelse(a1, b1, c1), Lifthenelse(a2, b2, c2) ->
      same a1 a2 && same b1 b2 && same c1 c2
  | Lsequence(a1, b1), Lsequence(a2, b2) ->
      same a1 a2 && same b1 b2
  | Lwhile(a1, b1), Lwhile(a2, b2) ->
      same a1 a2 && same b1 b2
  | Lfor(id1, a1, b1, df1, c1), Lfor(id2, a2, b2, df2, c2) ->
      Ident.same id1 id2 &&  same a1 a2 &&
      same b1 b2 && df1 = df2 && same c1 c2
  | Lassign(id1, a1), Lassign(id2, a2) ->
      Ident.same id1 id2 && same a1 a2
  | Lsend(k1, a1, b1, cl1, _), Lsend(k2, a2, b2, cl2, _) ->
      k1 = k2 && same a1 a2 && same b1 b2 && samelist same cl1 cl2
  | Levent(a1, ev1), Levent(a2, ev2) ->
      same a1 a2 && ev1.lev_loc = ev2.lev_loc
  | Lifused(id1, a1), Lifused(id2, a2) ->
      Ident.same id1 id2 && same a1 a2
  | _, _ ->
      faux

et samebinding (id1, c1) (id2, c2) =
  Ident.same id1 id2 && same c1 c2

et sameswitch sw1 sw2 =
  soit samecase (n1, a1) (n2, a2) = n1 = n2 && same a1 a2 dans
  sw1.sw_numconsts = sw2.sw_numconsts &&
  sw1.sw_numblocks = sw2.sw_numblocks &&
  samelist samecase sw1.sw_consts sw2.sw_consts &&
  samelist samecase sw1.sw_blocks sw2.sw_blocks &&
  (filtre (sw1.sw_failaction, sw2.sw_failaction) avec
    | (None, None) -> vrai
    | (Some a1, Some a2) -> same a1 a2
    | _ -> faux)

soit name_lambda strict arg fn =
  filtre arg avec
    Lvar id -> fn id
  | _ -> soit id = Ident.create "let" dans Llet(strict, id, arg, fn id)

soit name_lambda_list args fn =
  soit rec name_list names = fonction
    [] -> fn (List.rev names)
  | (Lvar id tel arg) :: rem ->
      name_list (arg :: names) rem
  | arg :: rem ->
      soit id = Ident.create "let" dans
      Llet(Strict, id, arg, name_list (Lvar id :: names) rem) dans
  name_list [] args

soit iter f = fonction
    Lvar _
  | Lconst _ -> ()
  | Lapply(fn, args, _) ->
      f fn; List.iter f args
  | Lfunction(kind, params, body) ->
      f body
  | Llet(str, id, arg, body) ->
      f arg; f body
  | Lletrec(decl, body) ->
      f body;
      List.iter (fonc (id, exp) -> f exp) decl
  | Lprim(p, args) ->
      List.iter f args
  | Lswitch(arg, sw) ->
      f arg;
      List.iter (fonc (key, case) -> f case) sw.sw_consts;
      List.iter (fonc (key, case) -> f case) sw.sw_blocks;
      début filtre sw.sw_failaction avec
      | None -> ()
      | Some l -> f l
      fin
  | Lstringswitch (arg,cases,default) ->
      f arg ;
      List.iter (fonc (_,act) -> f act) cases ;
      f default
  | Lstaticraise (_,args) ->
      List.iter f args
  | Lstaticcatch(e1, (_,vars), e2) ->
      f e1; f e2
  | Ltrywith(e1, exn, e2) ->
      f e1; f e2
  | Lifthenelse(e1, e2, e3) ->
      f e1; f e2; f e3
  | Lsequence(e1, e2) ->
      f e1; f e2
  | Lwhile(e1, e2) ->
      f e1; f e2
  | Lfor(v, e1, e2, dir, e3) ->
      f e1; f e2; f e3
  | Lassign(id, e) ->
      f e
  | Lsend (k, met, obj, args, _) ->
      List.iter f (met::obj::args)
  | Levent (lam, evt) ->
      f lam
  | Lifused (v, e) ->
      f e

module IdentSet =
  Set.Make(struct
    type t = Ident.t
    soit compare = compare
  fin)

soit free_ids get l =
  soit fv = ref IdentSet.empty dans
  soit rec free l =
    iter free l;
    fv := List.fold_right IdentSet.add (get l) !fv;
    filtre l avec
      Lfunction(kind, params, body) ->
        List.iter (fonc param -> fv := IdentSet.remove param !fv) params
    | Llet(str, id, arg, body) ->
        fv := IdentSet.remove id !fv
    | Lletrec(decl, body) ->
        List.iter (fonc (id, exp) -> fv := IdentSet.remove id !fv) decl
    | Lstaticcatch(e1, (_,vars), e2) ->
        List.iter (fonc id -> fv := IdentSet.remove id !fv) vars
    | Ltrywith(e1, exn, e2) ->
        fv := IdentSet.remove exn !fv
    | Lfor(v, e1, e2, dir, e3) ->
        fv := IdentSet.remove v !fv
    | Lassign(id, e) ->
        fv := IdentSet.add id !fv
    | Lvar _ | Lconst _ | Lapply _
    | Lprim _ | Lswitch _ | Lstringswitch _ | Lstaticraise _
    | Lifthenelse _ | Lsequence _ | Lwhile _
    | Lsend _ | Levent _ | Lifused _ -> ()
  dans free l; !fv

soit free_variables l =
  free_ids (fonction Lvar id -> [id] | _ -> []) l

soit free_methods l =
  free_ids (fonction Lsend(Self, Lvar meth, obj, _, _) -> [meth] | _ -> []) l

(* Check if an action has a "when" guard *)
soit raise_count = ref 0

soit next_raise_count () =
  incr raise_count ;
  !raise_count

(* Anticipated staticraise, for guards *)
soit staticfail = Lstaticraise (0,[])

soit rec is_guarded = fonction
  | Lifthenelse( cond, body, Lstaticraise (0,[])) -> vrai
  | Llet(str, id, lam, body) -> is_guarded body
  | Levent(lam, ev) -> is_guarded lam
  | _ -> faux

soit rec patch_guarded patch = fonction
  | Lifthenelse (cond, body, Lstaticraise (0,[])) ->
      Lifthenelse (cond, body, patch)
  | Llet(str, id, lam, body) ->
      Llet (str, id, lam, patch_guarded patch body)
  | Levent(lam, ev) ->
      Levent (patch_guarded patch lam, ev)
  | _ -> fatal_error "Lambda.patch_guarded"

(* Translate an access path *)

soit rec transl_normal_path = fonction
    Pident id ->
      si Ident.global id alors Lprim(Pgetglobal id, []) sinon Lvar id
  | Pdot(p, s, pos) ->
      Lprim(Pfield pos, [transl_normal_path p])
  | Papply(p1, p2) ->
      fatal_error "Lambda.transl_path"

(* Translation of value identifiers *)

soit transl_path ?(loc=Location.none) env path =
  transl_normal_path (Env.normalize_path (Some loc) env path) 

(* Compile a sequence of expressions *)

soit rec make_sequence fn = fonction
    [] -> lambda_unit
  | [x] -> fn x
  | x::rem ->
      soit lam = fn x dans Lsequence(lam, make_sequence fn rem)

(* Apply a substitution to a lambda-term.
   Assumes that the bound variables of the lambda-term do not
   belong to the domain of the substitution.
   Assumes that the image of the substitution is out of reach
   of the bound variables of the lambda-term (no capture). *)

soit subst_lambda s lam =
  soit rec subst = fonction
    Lvar id tel l ->
      début essaie Ident.find_same id s avec Not_found -> l fin
  | Lconst sc tel l -> l
  | Lapply(fn, args, loc) -> Lapply(subst fn, List.map subst args, loc)
  | Lfunction(kind, params, body) -> Lfunction(kind, params, subst body)
  | Llet(str, id, arg, body) -> Llet(str, id, subst arg, subst body)
  | Lletrec(decl, body) -> Lletrec(List.map subst_decl decl, subst body)
  | Lprim(p, args) -> Lprim(p, List.map subst args)
  | Lswitch(arg, sw) ->
      Lswitch(subst arg,
              {sw avec sw_consts = List.map subst_case sw.sw_consts;
                       sw_blocks = List.map subst_case sw.sw_blocks;
                       sw_failaction =
                         filtre sw.sw_failaction avec
                         | None -> None
                         | Some l -> Some (subst l)})
  | Lstringswitch (arg,cases,default) ->
      Lstringswitch
        (subst arg,List.map subst_strcase cases,subst default)
  | Lstaticraise (i,args) ->  Lstaticraise (i, List.map subst args)
  | Lstaticcatch(e1, io, e2) -> Lstaticcatch(subst e1, io, subst e2)
  | Ltrywith(e1, exn, e2) -> Ltrywith(subst e1, exn, subst e2)
  | Lifthenelse(e1, e2, e3) -> Lifthenelse(subst e1, subst e2, subst e3)
  | Lsequence(e1, e2) -> Lsequence(subst e1, subst e2)
  | Lwhile(e1, e2) -> Lwhile(subst e1, subst e2)
  | Lfor(v, e1, e2, dir, e3) -> Lfor(v, subst e1, subst e2, dir, subst e3)
  | Lassign(id, e) -> Lassign(id, subst e)
  | Lsend (k, met, obj, args, loc) ->
      Lsend (k, subst met, subst obj, List.map subst args, loc)
  | Levent (lam, evt) -> Levent (subst lam, evt)
  | Lifused (v, e) -> Lifused (v, subst e)
  et subst_decl (id, exp) = (id, subst exp)
  et subst_case (key, case) = (key, subst case)
  et subst_strcase (key, case) = (key, subst case)
  dans subst lam


(* To let-bind expressions to variables *)

soit bind str var exp body =
  filtre exp avec
    Lvar var' quand Ident.same var var' -> body
  | _ -> Llet(str, var, exp, body)

et commute_comparison = fonction
| Ceq -> Ceq| Cneq -> Cneq
| Clt -> Cgt | Cle -> Cge
| Cgt -> Clt | Cge -> Cle

et negate_comparison = fonction
| Ceq -> Cneq| Cneq -> Ceq
| Clt -> Cge | Cle -> Cgt
| Cgt -> Cle | Cge -> Clt

soit raise_kind = fonction
  | Raise_regular -> "raise"
  | Raise_reraise -> "reraise"
  | Raise_notrace -> "raise_notrace"
