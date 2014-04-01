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

(*  bytegen.ml : translation of lambda terms to lists of instructions. *)

ouvre Misc
ouvre Asttypes
ouvre Primitive
ouvre Types
ouvre Lambda
ouvre Switch
ouvre Instruct

(**** Label generation ****)

soit label_counter = ref 0

soit new_label () =
  incr label_counter; !label_counter

(**** Operations on compilation environments. ****)

soit empty_env =
  { ce_stack = Ident.empty; ce_heap = Ident.empty; ce_rec = Ident.empty }

(* Add a stack-allocated variable *)

soit add_var id pos env =
  { ce_stack = Ident.add id pos env.ce_stack;
    ce_heap = env.ce_heap;
    ce_rec = env.ce_rec }

soit rec add_vars idlist pos env =
  filtre idlist avec
    [] -> env
  | id :: rem -> add_vars rem (pos + 1) (add_var id pos env)

(**** Examination of the continuation ****)

(* Return a label to the beginning of the given continuation.
   If the sequence starts with a branch, use the target of that branch
   as the label, thus avoiding a jump to a jump. *)

soit label_code = fonction
    Kbranch lbl :: _ tel cont -> (lbl, cont)
  | Klabel lbl :: _ tel cont -> (lbl, cont)
  | cont -> soit lbl = new_label() dans (lbl, Klabel lbl :: cont)

(* Return a branch to the continuation. That is, an instruction that,
   when executed, branches to the continuation or performs what the
   continuation performs. We avoid generating branches to branches and
   branches to returns. *)

soit rec make_branch_2 lbl n cont =
  fonction
    Kreturn m :: _ -> (Kreturn (n + m), cont)
  | Klabel _ :: c  -> make_branch_2 lbl n cont c
  | Kpop m :: c    -> make_branch_2 lbl (n + m) cont c
  | _              ->
      filtre lbl avec
        Some lbl -> (Kbranch lbl, cont)
      | None     -> soit lbl = new_label() dans (Kbranch lbl, Klabel lbl :: cont)

soit make_branch cont =
  filtre cont avec
    (Kbranch _ tel branch) :: _ -> (branch, cont)
  | (Kreturn _ tel return) :: _ -> (return, cont)
  | Kraise k :: _ -> (Kraise k, cont)
  | Klabel lbl :: _ -> make_branch_2 (Some lbl) 0 cont cont
  | _ ->  make_branch_2 (None) 0 cont cont

(* Avoid a branch to a label that follows immediately *)

soit branch_to label cont = filtre cont avec
| Klabel label0::_ quand label = label0 -> cont
| _ -> Kbranch label::cont

(* Discard all instructions up to the next label.
   This function is to be applied to the continuation before adding a
   non-terminating instruction (branch, raise, return) in front of it. *)

soit rec discard_dead_code = fonction
    [] -> []
  | (Klabel _ | Krestart | Ksetglobal _) :: _ tel cont -> cont
  | _ :: cont -> discard_dead_code cont

(* Check if we're in tailcall position *)

soit rec is_tailcall = fonction
    Kreturn _ :: _ -> vrai
  | Klabel _ :: c -> is_tailcall c
  | Kpop _ :: c -> is_tailcall c
  | _ -> faux

(* Add a Kpop N instruction in front of a continuation *)

soit rec add_pop n cont =
  si n = 0 alors cont sinon
    filtre cont avec
      Kpop m :: cont -> add_pop (n + m) cont
    | Kreturn m :: cont -> Kreturn(n + m) :: cont
    | Kraise _ :: _ -> cont
    | _ -> Kpop n :: cont

(* Add the constant "unit" in front of a continuation *)

soit add_const_unit = fonction
    (Kacc _ | Kconst _ | Kgetglobal _ | Kpush_retaddr _) :: _ tel cont -> cont
  | cont -> Kconst const_unit :: cont

soit rec push_dummies n k = filtre n avec
| 0 -> k
| _ -> Kconst const_unit::Kpush::push_dummies (n-1) k


(**** Auxiliary for compiling "let rec" ****)

type rhs_kind =
  | RHS_block de int
  | RHS_floatblock de int
  | RHS_nonrec
;;

soit rec check_recordwith_updates id e =
  filtre e avec
  | Lsequence (Lprim ((Psetfield _ | Psetfloatfield _), [Lvar id2; _]), cont)
      -> id2 = id && check_recordwith_updates id cont
  | Lvar id2 -> id2 = id
  | _ -> faux
;;

soit rec size_of_lambda = fonction
  | Lfunction(kind, params, body) tel funct ->
      RHS_block (1 + IdentSet.cardinal(free_variables funct))
  | Llet (Strict, id, Lprim (Pduprecord (kind, size), _), body)
    quand check_recordwith_updates id body ->
      début filtre kind avec
      | Record_regular -> RHS_block size
      | Record_float -> RHS_floatblock size
      fin
  | Llet(str, id, arg, body) -> size_of_lambda body
  | Lletrec(bindings, body) -> size_of_lambda body
  | Lprim(Pmakeblock(tag, mut), args) -> RHS_block (List.length args)
  | Lprim (Pmakearray (Paddrarray|Pintarray), args) ->
      RHS_block (List.length args)
  | Lprim (Pmakearray Pfloatarray, args) -> RHS_floatblock (List.length args)
  | Lprim (Pmakearray Pgenarray, args) -> affirme faux
  | Lprim (Pduprecord (Record_regular, size), args) -> RHS_block size
  | Lprim (Pduprecord (Record_float, size), args) -> RHS_floatblock size
  | Levent (lam, _) -> size_of_lambda lam
  | Lsequence (lam, lam') -> size_of_lambda lam'
  | _ -> RHS_nonrec

(**** Merging consecutive events ****)

soit copy_event ev kind info repr =
  { ev_pos = 0;                   (* patched in emitcode *)
    ev_module = ev.ev_module;
    ev_loc = ev.ev_loc;
    ev_kind = kind;
    ev_info = info;
    ev_typenv = ev.ev_typenv;
    ev_typsubst = ev.ev_typsubst;
    ev_compenv = ev.ev_compenv;
    ev_stacksize = ev.ev_stacksize;
    ev_repr = repr }

soit merge_infos ev ev' =
  filtre ev.ev_info, ev'.ev_info avec
    Event_other, info -> info
  | info, Event_other -> info
  | _                 -> fatal_error "Bytegen.merge_infos"

soit merge_repr ev ev' =
  filtre ev.ev_repr, ev'.ev_repr avec
    Event_none, x -> x
  | x, Event_none -> x
  | Event_parent r, Event_child r' quand r == r' && !r = 1 -> Event_none
  | Event_child r, Event_parent r' quand r == r' -> Event_parent r
  | _, _          -> fatal_error "Bytegen.merge_repr"

soit merge_events ev ev' =
  soit (maj, min) =
    filtre ev.ev_kind, ev'.ev_kind avec
    (* Discard pseudo-events *)
      Event_pseudo,  _                              -> ev', ev
    | _,             Event_pseudo                   -> ev,  ev'
    (* Keep following event, supposedly more informative *)
    | Event_before,  (Event_after _ | Event_before) -> ev',  ev
    (* Discard following events, supposedly less informative *)
    | Event_after _, (Event_after _ | Event_before) -> ev, ev'
  dans
  copy_event maj maj.ev_kind (merge_infos maj min) (merge_repr maj min)

soit weaken_event ev cont =
  filtre ev.ev_kind avec
    Event_after _ ->
      début filtre cont avec
        Kpush :: Kevent ({ev_repr = Event_none} tel ev') :: c ->
          début filtre ev.ev_info avec
            Event_return _ ->
              (* Weaken event *)
              soit repr = ref 1 dans
              soit ev =
                copy_event ev Event_pseudo ev.ev_info (Event_parent repr)
              et ev' =
                copy_event ev' ev'.ev_kind ev'.ev_info (Event_child repr)
              dans
              Kevent ev :: Kpush :: Kevent ev' :: c
          | _ ->
              (* Only keep following event, equivalent *)
              cont
          fin
      | _ ->
          Kevent ev :: cont
      fin
  | _ ->
      Kevent ev :: cont

soit add_event ev =
  fonction
    Kevent ev' :: cont -> weaken_event (merge_events ev ev') cont
  | cont               -> weaken_event ev cont

(**** Compilation of a lambda expression ****)

(* association staticraise numbers -> (lbl,size of stack *)

soit sz_static_raises = ref []
soit find_raise_label i =
  essaie
    List.assoc i !sz_static_raises
  avec
  | Not_found ->
      Misc.fatal_error
        ("exit("^string_of_int i^") outside appropriated catch")

(* Will the translation of l lead to a jump to label ? *)
soit code_as_jump l sz = filtre l avec
| Lstaticraise (i,[]) ->
    soit label,size = find_raise_label i dans
    si sz = size alors
      Some label
    sinon
      None
| _ -> None

(* Function bodies that remain to be compiled *)

type function_to_compile =
  { params: Ident.t list;               (* function parameters *)
    body: lambda;                       (* the function body *)
    label: label;                       (* the label of the function entry *)
    free_vars: Ident.t list;            (* free variables of the function *)
    num_defs: int;            (* number of mutually recursive definitions *)
    rec_vars: Ident.t list;             (* mutually recursive fn names *)
    rec_pos: int }                      (* rank in recursive definition *)

soit functions_to_compile  = (Stack.create () : function_to_compile Stack.t)

(* Name of current compilation unit (for debugging events) *)

soit compunit_name = ref ""

(* Maximal stack size reached during the current function body *)

soit max_stack_used = ref 0


(* Sequence of string tests *)


(* Translate a primitive to a bytecode instruction (possibly a call to a C
   function) *)

soit comp_bint_primitive bi suff args =
  soit pref =
    filtre bi avec Pnativeint -> "caml_nativeint_"
                | Pint32 -> "caml_int32_"
                | Pint64 -> "caml_int64_" dans
  Kccall(pref ^ suff, List.length args)

soit comp_primitive p args =
  filtre p avec
    Pgetglobal id -> Kgetglobal id
  | Psetglobal id -> Ksetglobal id
  | Pintcomp cmp -> Kintcomp cmp
  | Pmakeblock(tag, mut) -> Kmakeblock(List.length args, tag)
  | Pfield n -> Kgetfield n
  | Psetfield(n, ptr) -> Ksetfield n
  | Pfloatfield n -> Kgetfloatfield n
  | Psetfloatfield n -> Ksetfloatfield n
  | Pduprecord _ -> Kccall("caml_obj_dup", 1)
  | Pccall p -> Kccall(p.prim_name, p.prim_arity)
  | Pnegint -> Knegint
  | Paddint -> Kaddint
  | Psubint -> Ksubint
  | Pmulint -> Kmulint
  | Pdivint -> Kdivint
  | Pmodint -> Kmodint
  | Pandint -> Kandint
  | Porint -> Korint
  | Pxorint -> Kxorint
  | Plslint -> Klslint
  | Plsrint -> Klsrint
  | Pasrint -> Kasrint
  | Poffsetint n -> Koffsetint n
  | Poffsetref n -> Koffsetref n
  | Pintoffloat -> Kccall("caml_int_of_float", 1)
  | Pfloatofint -> Kccall("caml_float_of_int", 1)
  | Pnegfloat -> Kccall("caml_neg_float", 1)
  | Pabsfloat -> Kccall("caml_abs_float", 1)
  | Paddfloat -> Kccall("caml_add_float", 2)
  | Psubfloat -> Kccall("caml_sub_float", 2)
  | Pmulfloat -> Kccall("caml_mul_float", 2)
  | Pdivfloat -> Kccall("caml_div_float", 2)
  | Pfloatcomp Ceq -> Kccall("caml_eq_float", 2)
  | Pfloatcomp Cneq -> Kccall("caml_neq_float", 2)
  | Pfloatcomp Clt -> Kccall("caml_lt_float", 2)
  | Pfloatcomp Cgt -> Kccall("caml_gt_float", 2)
  | Pfloatcomp Cle -> Kccall("caml_le_float", 2)
  | Pfloatcomp Cge -> Kccall("caml_ge_float", 2)
  | Pstringlength -> Kccall("caml_ml_string_length", 1)
  | Pstringrefs -> Kccall("caml_string_get", 2)
  | Pstringsets -> Kccall("caml_string_set", 3)
  | Pstringrefu -> Kgetstringchar
  | Pstringsetu -> Ksetstringchar
  | Pstring_load_16(_) -> Kccall("caml_string_get16", 2)
  | Pstring_load_32(_) -> Kccall("caml_string_get32", 2)
  | Pstring_load_64(_) -> Kccall("caml_string_get64", 2)
  | Pstring_set_16(_) -> Kccall("caml_string_set16", 3)
  | Pstring_set_32(_) -> Kccall("caml_string_set32", 3)
  | Pstring_set_64(_) -> Kccall("caml_string_set64", 3)
  | Parraylength kind -> Kvectlength
  | Parrayrefs Pgenarray -> Kccall("caml_array_get", 2)
  | Parrayrefs Pfloatarray -> Kccall("caml_array_get_float", 2)
  | Parrayrefs _ -> Kccall("caml_array_get_addr", 2)
  | Parraysets Pgenarray -> Kccall("caml_array_set", 3)
  | Parraysets Pfloatarray -> Kccall("caml_array_set_float", 3)
  | Parraysets _ -> Kccall("caml_array_set_addr", 3)
  | Parrayrefu Pgenarray -> Kccall("caml_array_unsafe_get", 2)
  | Parrayrefu Pfloatarray -> Kccall("caml_array_unsafe_get_float", 2)
  | Parrayrefu _ -> Kgetvectitem
  | Parraysetu Pgenarray -> Kccall("caml_array_unsafe_set", 3)
  | Parraysetu Pfloatarray -> Kccall("caml_array_unsafe_set_float", 3)
  | Parraysetu _ -> Ksetvectitem
  | Pctconst c ->
     soit const_name = filtre c avec
       | Big_endian -> "big_endian"
       | Word_size -> "word_size"
       | Ostype_unix -> "ostype_unix"
       | Ostype_win32 -> "ostype_win32"
       | Ostype_cygwin -> "ostype_cygwin" dans
     Kccall(Printf.sprintf "caml_sys_const_%s" const_name, 1)
  | Pisint -> Kisint
  | Pisout -> Kisout
  | Pbittest -> Kccall("caml_bitvect_test", 2)
  | Pbintofint bi -> comp_bint_primitive bi "of_int" args
  | Pintofbint bi -> comp_bint_primitive bi "to_int" args
  | Pcvtbint(Pint32, Pnativeint) -> Kccall("caml_nativeint_of_int32", 1)
  | Pcvtbint(Pnativeint, Pint32) -> Kccall("caml_nativeint_to_int32", 1)
  | Pcvtbint(Pint32, Pint64) -> Kccall("caml_int64_of_int32", 1)
  | Pcvtbint(Pint64, Pint32) -> Kccall("caml_int64_to_int32", 1)
  | Pcvtbint(Pnativeint, Pint64) -> Kccall("caml_int64_of_nativeint", 1)
  | Pcvtbint(Pint64, Pnativeint) -> Kccall("caml_int64_to_nativeint", 1)
  | Pnegbint bi -> comp_bint_primitive bi "neg" args
  | Paddbint bi -> comp_bint_primitive bi "add" args
  | Psubbint bi -> comp_bint_primitive bi "sub" args
  | Pmulbint bi -> comp_bint_primitive bi "mul" args
  | Pdivbint bi -> comp_bint_primitive bi "div" args
  | Pmodbint bi -> comp_bint_primitive bi "mod" args
  | Pandbint bi -> comp_bint_primitive bi "and" args
  | Porbint bi -> comp_bint_primitive bi "or" args
  | Pxorbint bi -> comp_bint_primitive bi "xor" args
  | Plslbint bi -> comp_bint_primitive bi "shift_left" args
  | Plsrbint bi -> comp_bint_primitive bi "shift_right_unsigned" args
  | Pasrbint bi -> comp_bint_primitive bi "shift_right" args
  | Pbintcomp(bi, Ceq) -> Kccall("caml_equal", 2)
  | Pbintcomp(bi, Cneq) -> Kccall("caml_notequal", 2)
  | Pbintcomp(bi, Clt) -> Kccall("caml_lessthan", 2)
  | Pbintcomp(bi, Cgt) -> Kccall("caml_greaterthan", 2)
  | Pbintcomp(bi, Cle) -> Kccall("caml_lessequal", 2)
  | Pbintcomp(bi, Cge) -> Kccall("caml_greaterequal", 2)
  | Pbigarrayref(_, n, _, _) -> Kccall("caml_ba_get_" ^ string_of_int n, n + 1)
  | Pbigarrayset(_, n, _, _) -> Kccall("caml_ba_set_" ^ string_of_int n, n + 2)
  | Pbigarraydim(n) -> Kccall("caml_ba_dim_" ^ string_of_int n, 1)
  | Pbigstring_load_16(_) -> Kccall("caml_ba_uint8_get16", 2)
  | Pbigstring_load_32(_) -> Kccall("caml_ba_uint8_get32", 2)
  | Pbigstring_load_64(_) -> Kccall("caml_ba_uint8_get64", 2)
  | Pbigstring_set_16(_) -> Kccall("caml_ba_uint8_set16", 3)
  | Pbigstring_set_32(_) -> Kccall("caml_ba_uint8_set32", 3)
  | Pbigstring_set_64(_) -> Kccall("caml_ba_uint8_set64", 3)
  | Pbswap16 -> Kccall("caml_bswap16", 1)
  | Pbbswap(bi) -> comp_bint_primitive bi "bswap" args
  | _ -> fatal_error "Bytegen.comp_primitive"

soit is_immed n = immed_min <= n && n <= immed_max


(* Compile an expression.
   The value of the expression is left in the accumulator.
   env = compilation environment
   exp = the lambda expression to compile
   sz = current size of the stack frame
   cont = list of instructions to execute afterwards
   Result = list of instructions that evaluate exp, then perform cont. *)

soit rec comp_expr env exp sz cont =
  si sz > !max_stack_used alors max_stack_used := sz;
  filtre exp avec
    Lvar id ->
      début essaie
        soit pos = Ident.find_same id env.ce_stack dans
        Kacc(sz - pos) :: cont
      avec Not_found ->
      essaie
        soit pos = Ident.find_same id env.ce_heap dans
        Kenvacc(pos) :: cont
      avec Not_found ->
      essaie
        soit ofs = Ident.find_same id env.ce_rec dans
        Koffsetclosure(ofs) :: cont
      avec Not_found ->
        Format.eprintf "%a@." Ident.print id;
        fatal_error ("Bytegen.comp_expr: var " ^ Ident.unique_name id)
      fin
  | Lconst cst ->
      Kconst cst :: cont
  | Lapply(func, args, loc) ->
      soit nargs = List.length args dans
      si is_tailcall cont alors début
        comp_args env args sz
          (Kpush :: comp_expr env func (sz + nargs)
            (Kappterm(nargs, sz + nargs) :: discard_dead_code cont))
      fin sinon début
        si nargs < 4 alors
          comp_args env args sz
            (Kpush :: comp_expr env func (sz + nargs) (Kapply nargs :: cont))
        sinon début
          soit (lbl, cont1) = label_code cont dans
          Kpush_retaddr lbl ::
          comp_args env args (sz + 3)
            (Kpush :: comp_expr env func (sz + 3 + nargs)
                      (Kapply nargs :: cont1))
        fin
      fin
  | Lsend(kind, met, obj, args, _) ->
      soit args = si kind = Cached alors List.tl args sinon args dans
      soit nargs = List.length args + 1 dans
      soit getmethod, args' =
        si kind = Self alors (Kgetmethod, met::obj::args) sinon
        filtre met avec
          Lconst(Const_base(Const_int n)) -> (Kgetpubmet n, obj::args)
        | _ -> (Kgetdynmet, met::obj::args)
      dans
      si is_tailcall cont alors
        comp_args env args' sz
          (getmethod :: Kappterm(nargs, sz + nargs) :: discard_dead_code cont)
      sinon
        si nargs < 4 alors
          comp_args env args' sz
            (getmethod :: Kapply nargs :: cont)
        sinon début
          soit (lbl, cont1) = label_code cont dans
          Kpush_retaddr lbl ::
          comp_args env args' (sz + 3)
            (getmethod :: Kapply nargs :: cont1)
        fin
  | Lfunction(kind, params, body) -> (* assume kind = Curried *)
      soit lbl = new_label() dans
      soit fv = IdentSet.elements(free_variables exp) dans
      soit to_compile =
        { params = params; body = body; label = lbl;
          free_vars = fv; num_defs = 1; rec_vars = []; rec_pos = 0 } dans
      Stack.push to_compile functions_to_compile;
      comp_args env (List.map (fonc n -> Lvar n) fv) sz
        (Kclosure(lbl, List.length fv) :: cont)
  | Llet(str, id, arg, body) ->
      comp_expr env arg sz
        (Kpush :: comp_expr (add_var id (sz+1) env) body (sz+1)
          (add_pop 1 cont))
  | Lletrec(decl, body) ->
      soit ndecl = List.length decl dans
      si List.for_all (fonction (_, Lfunction(_,_,_)) -> vrai | _ -> faux)
                      decl alors début
        (* let rec of functions *)
        soit fv =
          IdentSet.elements (free_variables (Lletrec(decl, lambda_unit))) dans
        soit rec_idents = List.map (fonc (id, lam) -> id) decl dans
        soit rec comp_fun pos = fonction
            [] -> []
          | (id, Lfunction(kind, params, body)) :: rem ->
              soit lbl = new_label() dans
              soit to_compile =
                { params = params; body = body; label = lbl; free_vars = fv;
                  num_defs = ndecl; rec_vars = rec_idents; rec_pos = pos} dans
              Stack.push to_compile functions_to_compile;
              lbl :: comp_fun (pos + 1) rem
          | _ -> affirme faux dans
        soit lbls = comp_fun 0 decl dans
        comp_args env (List.map (fonc n -> Lvar n) fv) sz
          (Kclosurerec(lbls, List.length fv) ::
            (comp_expr (add_vars rec_idents (sz+1) env) body (sz + ndecl)
                       (add_pop ndecl cont)))
      fin sinon début
        soit decl_size =
          List.map (fonc (id, exp) -> (id, exp, size_of_lambda exp)) decl dans
        soit rec comp_init new_env sz = fonction
          | [] -> comp_nonrec new_env sz ndecl decl_size
          | (id, exp, RHS_floatblock blocksize) :: rem ->
              Kconst(Const_base(Const_int blocksize)) ::
              Kccall("caml_alloc_dummy_float", 1) :: Kpush ::
              comp_init (add_var id (sz+1) new_env) (sz+1) rem
          | (id, exp, RHS_block blocksize) :: rem ->
              Kconst(Const_base(Const_int blocksize)) ::
              Kccall("caml_alloc_dummy", 1) :: Kpush ::
              comp_init (add_var id (sz+1) new_env) (sz+1) rem
          | (id, exp, RHS_nonrec) :: rem ->
              Kconst(Const_base(Const_int 0)) :: Kpush ::
              comp_init (add_var id (sz+1) new_env) (sz+1) rem
        et comp_nonrec new_env sz i = fonction
          | [] -> comp_rec new_env sz ndecl decl_size
          | (id, exp, (RHS_block _ | RHS_floatblock _)) :: rem ->
              comp_nonrec new_env sz (i-1) rem
          | (id, exp, RHS_nonrec) :: rem ->
              comp_expr new_env exp sz
                (Kassign (i-1) :: comp_nonrec new_env sz (i-1) rem)
        et comp_rec new_env sz i = fonction
          | [] -> comp_expr new_env body sz (add_pop ndecl cont)
          | (id, exp, (RHS_block _ | RHS_floatblock _)) :: rem ->
              comp_expr new_env exp sz
                (Kpush :: Kacc i :: Kccall("caml_update_dummy", 2) ::
                 comp_rec new_env sz (i-1) rem)
          | (id, exp, RHS_nonrec) :: rem ->
              comp_rec new_env sz (i-1) rem
        dans
        comp_init env sz decl_size
      fin
  | Lprim(Pidentity, [arg]) ->
      comp_expr env arg sz cont
  | Lprim(Pignore, [arg]) ->
      comp_expr env arg sz (add_const_unit cont)
  | Lprim(Pdirapply loc, [func;arg])
  | Lprim(Prevapply loc, [arg;func]) ->
      soit exp = Lapply(func, [arg], loc) dans
      comp_expr env exp sz cont
  | Lprim(Pnot, [arg]) ->
      soit newcont =
        filtre cont avec
          Kbranchif lbl :: cont1 -> Kbranchifnot lbl :: cont1
        | Kbranchifnot lbl :: cont1 -> Kbranchif lbl :: cont1
        | _ -> Kboolnot :: cont dans
      comp_expr env arg sz newcont
  | Lprim(Psequand, [exp1; exp2]) ->
      début filtre cont avec
        Kbranchifnot lbl :: _ ->
          comp_expr env exp1 sz (Kbranchifnot lbl ::
            comp_expr env exp2 sz cont)
      | Kbranchif lbl :: cont1 ->
          soit (lbl2, cont2) = label_code cont1 dans
          comp_expr env exp1 sz (Kbranchifnot lbl2 ::
            comp_expr env exp2 sz (Kbranchif lbl :: cont2))
      | _ ->
          soit (lbl, cont1) = label_code cont dans
          comp_expr env exp1 sz (Kstrictbranchifnot lbl ::
            comp_expr env exp2 sz cont1)
      fin
  | Lprim(Psequor, [exp1; exp2]) ->
      début filtre cont avec
        Kbranchif lbl :: _ ->
          comp_expr env exp1 sz (Kbranchif lbl ::
            comp_expr env exp2 sz cont)
      | Kbranchifnot lbl :: cont1 ->
          soit (lbl2, cont2) = label_code cont1 dans
          comp_expr env exp1 sz (Kbranchif lbl2 ::
            comp_expr env exp2 sz (Kbranchifnot lbl :: cont2))
      | _ ->
          soit (lbl, cont1) = label_code cont dans
          comp_expr env exp1 sz (Kstrictbranchif lbl ::
            comp_expr env exp2 sz cont1)
      fin
  | Lprim(Praise k, [arg]) ->
      comp_expr env arg sz (Kraise k :: discard_dead_code cont)
  | Lprim(Paddint, [arg; Lconst(Const_base(Const_int n))])
    quand is_immed n ->
      comp_expr env arg sz (Koffsetint n :: cont)
  | Lprim(Psubint, [arg; Lconst(Const_base(Const_int n))])
    quand is_immed (-n) ->
      comp_expr env arg sz (Koffsetint (-n) :: cont)
  | Lprim (Poffsetint n, [arg])
    quand not (is_immed n) ->
      comp_expr env arg sz
        (Kpush::
         Kconst (Const_base (Const_int n))::
         Kaddint::cont)
  | Lprim(Pmakearray kind, args) ->
      début filtre kind avec
        Pintarray | Paddrarray ->
          comp_args env args sz (Kmakeblock(List.length args, 0) :: cont)
      | Pfloatarray ->
          comp_args env args sz (Kmakefloatblock(List.length args) :: cont)
      | Pgenarray ->
          si args = []
          alors Kmakeblock(0, 0) :: cont
          sinon comp_args env args sz
                 (Kmakeblock(List.length args, 0) ::
                  Kccall("caml_make_array", 1) :: cont)
      fin
(* Integer first for enabling futher optimization (cf. emitcode.ml)  *)
  | Lprim (Pintcomp c, [arg ; (Lconst _ tel k)]) ->
      soit p = Pintcomp (commute_comparison c)
      et args = [k ; arg] dans
      comp_args env args sz (comp_primitive p args :: cont)
  | Lprim(p, args) ->
      comp_args env args sz (comp_primitive p args :: cont)
  | Lstaticcatch (body, (i, vars) , handler) ->
      soit nvars = List.length vars dans
      soit branch1, cont1 = make_branch cont dans
      soit r =
        si nvars <> 1 alors début (* general case *)
          soit lbl_handler, cont2 =
            label_code
              (comp_expr
                (add_vars vars (sz+1) env)
                handler (sz+nvars) (add_pop nvars cont1)) dans
          sz_static_raises :=
            (i, (lbl_handler, sz+nvars)) :: !sz_static_raises ;
          push_dummies nvars
            (comp_expr env body (sz+nvars)
            (add_pop nvars (branch1 :: cont2)))
        fin sinon début (* small optimization for nvars = 1 *)
          soit var = filtre vars avec [var] -> var | _ -> affirme faux dans
          soit lbl_handler, cont2 =
            label_code
              (Kpush::comp_expr
                (add_var var (sz+1) env)
                handler (sz+1) (add_pop 1 cont1)) dans
          sz_static_raises :=
            (i, (lbl_handler, sz)) :: !sz_static_raises ;
          comp_expr env body sz (branch1 :: cont2)
        fin dans
      sz_static_raises := List.tl !sz_static_raises ;
      r
  | Lstaticraise (i, args) ->
      soit cont = discard_dead_code cont dans
      soit label,size = find_raise_label i dans
      début filtre args avec
      | [arg] -> (* optim, argument passed in accumulator *)
          comp_expr env arg sz
            (add_pop (sz-size) (branch_to label cont))
      | _ ->
          comp_exit_args env args sz size
            (add_pop (sz-size) (branch_to label cont))
      fin
  | Ltrywith(body, id, handler) ->
      soit (branch1, cont1) = make_branch cont dans
      soit lbl_handler = new_label() dans
      Kpushtrap lbl_handler ::
        comp_expr env body (sz+4) (Kpoptrap :: branch1 ::
          Klabel lbl_handler :: Kpush ::
            comp_expr (add_var id (sz+1) env) handler (sz+1) (add_pop 1 cont1))
  | Lifthenelse(cond, ifso, ifnot) ->
      comp_binary_test env cond ifso ifnot sz cont
  | Lsequence(exp1, exp2) ->
      comp_expr env exp1 sz (comp_expr env exp2 sz cont)
  | Lwhile(cond, body) ->
      soit lbl_loop = new_label() dans
      soit lbl_test = new_label() dans
      Kbranch lbl_test :: Klabel lbl_loop :: Kcheck_signals ::
        comp_expr env body sz
          (Klabel lbl_test ::
            comp_expr env cond sz (Kbranchif lbl_loop :: add_const_unit cont))
  | Lfor(param, start, stop, dir, body) ->
      soit lbl_loop = new_label() dans
      soit lbl_exit = new_label() dans
      soit offset = filtre dir avec Upto -> 1 | Downto -> -1 dans
      soit comp = filtre dir avec Upto -> Cgt | Downto -> Clt dans
      comp_expr env start sz
        (Kpush :: comp_expr env stop (sz+1)
          (Kpush :: Kpush :: Kacc 2 :: Kintcomp comp :: Kbranchif lbl_exit ::
           Klabel lbl_loop :: Kcheck_signals ::
           comp_expr (add_var param (sz+1) env) body (sz+2)
             (Kacc 1 :: Kpush :: Koffsetint offset :: Kassign 2 ::
              Kacc 1 :: Kintcomp Cneq :: Kbranchif lbl_loop ::
              Klabel lbl_exit :: add_const_unit (add_pop 2 cont))))
  | Lswitch(arg, sw) ->
      soit (branch, cont1) = make_branch cont dans
      soit c = ref (discard_dead_code cont1) dans
(* Build indirection vectors *)
      soit store = mk_store Lambda.same dans
      soit act_consts = Array.create sw.sw_numconsts 0
      et act_blocks = Array.create sw.sw_numblocks 0 dans
      début filtre sw.sw_failaction avec (* default is index 0 *)
      | Some fail -> ignore (store.act_store fail)
      | None      -> ()
      fin ;
      List.iter
        (fonc (n, act) -> act_consts.(n) <- store.act_store act) sw.sw_consts;
      List.iter
        (fonc (n, act) -> act_blocks.(n) <- store.act_store act) sw.sw_blocks;
(* Compile and label actions *)
      soit acts = store.act_get () dans
      soit lbls = Array.create (Array.length acts) 0 dans
      pour i = Array.length acts-1 descendant_jusqu'a 0 faire
        soit lbl,c1 = label_code (comp_expr env acts.(i) sz (branch :: !c)) dans
        lbls.(i) <- lbl ;
        c := discard_dead_code c1
      fait ;

(* Build label vectors *)
      soit lbl_blocks = Array.create sw.sw_numblocks 0 dans
      pour i = sw.sw_numblocks - 1 descendant_jusqu'a 0 faire
        lbl_blocks.(i) <- lbls.(act_blocks.(i))
      fait;
      soit lbl_consts = Array.create sw.sw_numconsts 0 dans
      pour i = sw.sw_numconsts - 1 descendant_jusqu'a 0 faire
        lbl_consts.(i) <- lbls.(act_consts.(i))
      fait;
      comp_expr env arg sz (Kswitch(lbl_consts, lbl_blocks) :: !c)
  | Lstringswitch (arg,sw,d) ->
      comp_expr env (Matching.expand_stringswitch arg sw d) sz cont
  | Lassign(id, expr) ->
      début essaie
        soit pos = Ident.find_same id env.ce_stack dans
        comp_expr env expr sz (Kassign(sz - pos) :: cont)
      avec Not_found ->
        fatal_error "Bytegen.comp_expr: assign"
      fin
  | Levent(lam, lev) ->
      soit event kind info =
        { ev_pos = 0;                   (* patched in emitcode *)
          ev_module = !compunit_name;
          ev_loc = lev.lev_loc;
          ev_kind = kind;
          ev_info = info;
          ev_typenv = lev.lev_env;
          ev_typsubst = Subst.identity;
          ev_compenv = env;
          ev_stacksize = sz;
          ev_repr =
            début filtre lev.lev_repr avec
              None ->
                Event_none
            | Some ({contents = 1} tel repr) quand lev.lev_kind = Lev_function ->
                Event_child repr
            | Some ({contents = 1} tel repr) ->
                Event_parent repr
            | Some repr quand lev.lev_kind = Lev_function ->
                Event_parent repr
            | Some repr ->
                Event_child repr
            fin }
      dans
      début filtre lev.lev_kind avec
        Lev_before ->
          soit c = comp_expr env lam sz cont dans
          soit ev = event Event_before Event_other dans
          add_event ev c
      | Lev_function ->
          soit c = comp_expr env lam sz cont dans
          soit ev = event Event_pseudo Event_function dans
          add_event ev c
      | Lev_after _ quand is_tailcall cont -> (* don't destroy tail call opt *)
          comp_expr env lam sz cont
      | Lev_after ty ->
          soit info =
            filtre lam avec
              Lapply(_, args, _)      -> Event_return (List.length args)
            | Lsend(_, _, _, args, _) -> Event_return (List.length args + 1)
            | _                       -> Event_other
          dans
          soit ev = event (Event_after ty) info dans
          soit cont1 = add_event ev cont dans
          comp_expr env lam sz cont1
      fin
  | Lifused (_, exp) ->
      comp_expr env exp sz cont

(* Compile a list of arguments [e1; ...; eN] to a primitive operation.
   The values of eN ... e2 are pushed on the stack, e2 at top of stack,
   then e3, then ... The value of e1 is left in the accumulator. *)

et comp_args env argl sz cont =
  comp_expr_list env (List.rev argl) sz cont

et comp_expr_list env exprl sz cont = filtre exprl avec
    [] -> cont
  | [exp] -> comp_expr env exp sz cont
  | exp :: rem ->
      comp_expr env exp sz (Kpush :: comp_expr_list env rem (sz+1) cont)

et comp_exit_args  env argl sz pos cont =
   comp_expr_list_assign env (List.rev argl) sz pos cont

et comp_expr_list_assign env exprl sz pos cont = filtre exprl avec
  | [] -> cont
  | exp :: rem ->
      comp_expr env exp sz
        (Kassign (sz-pos)::comp_expr_list_assign env rem sz (pos-1) cont)

(* Compile an if-then-else test. *)

et comp_binary_test env cond ifso ifnot sz cont =
  soit cont_cond =
    si ifnot = Lconst const_unit alors début
      soit (lbl_end, cont1) = label_code cont dans
      Kstrictbranchifnot lbl_end :: comp_expr env ifso sz cont1
    fin sinon
    filtre code_as_jump ifso sz avec
    | Some label ->
      soit cont = comp_expr env ifnot sz cont dans
      Kbranchif label :: cont
    | _ ->
        filtre code_as_jump ifnot sz avec
        | Some label ->
            soit cont = comp_expr env ifso sz cont dans
            Kbranchifnot label :: cont
        | _ ->
            soit (branch_end, cont1) = make_branch cont dans
            soit (lbl_not, cont2) = label_code(comp_expr env ifnot sz cont1) dans
            Kbranchifnot lbl_not ::
            comp_expr env ifso sz (branch_end :: cont2) dans

  comp_expr env cond sz cont_cond

(* Compile string switch *)

et comp_string_switch env arg cases default sz cont = ()

(**** Compilation of a code block (with tracking of stack usage) ****)

soit comp_block env exp sz cont =
  max_stack_used := 0;
  soit code = comp_expr env exp sz cont dans
  (* +1 because comp_expr may have pushed one more word *)
  si !max_stack_used + 1 > Config.stack_threshold alors
    Kconst(Const_base(Const_int(!max_stack_used + 1))) ::
    Kccall("caml_ensure_stack_capacity", 1) ::
    code
  sinon
    code

(**** Compilation of functions ****)

soit comp_function tc cont =
  soit arity = List.length tc.params dans
  soit rec positions pos delta = fonction
      [] -> Ident.empty
    | id :: rem -> Ident.add id pos (positions (pos + delta) delta rem) dans
  soit env =
    { ce_stack = positions arity (-1) tc.params;
      ce_heap = positions (2 * (tc.num_defs - tc.rec_pos) - 1) 1 tc.free_vars;
      ce_rec = positions (-2 * tc.rec_pos) 2 tc.rec_vars } dans
  soit cont =
    comp_block env tc.body arity (Kreturn arity :: cont) dans
  si arity > 1 alors
    Krestart :: Klabel tc.label :: Kgrab(arity - 1) :: cont
  sinon
    Klabel tc.label :: cont

soit comp_remainder cont =
  soit c = ref cont dans
  début essaie
    pendant_que vrai faire
      c := comp_function (Stack.pop functions_to_compile) !c
    fait
  avec Stack.Empty ->
    ()
  fin;
  !c

(**** Compilation of a lambda phrase ****)

soit compile_implementation modulename expr =
  Stack.clear functions_to_compile;
  label_counter := 0;
  sz_static_raises := [] ;
  compunit_name := modulename;
  soit init_code = comp_block empty_env expr 0 [] dans
  si Stack.length functions_to_compile > 0 alors début
    soit lbl_init = new_label() dans
    Kbranch lbl_init :: comp_remainder (Klabel lbl_init :: init_code)
  fin sinon
    init_code

soit compile_phrase expr =
  Stack.clear functions_to_compile;
  label_counter := 0;
  sz_static_raises := [] ;
  soit init_code = comp_block empty_env expr 1 [Kreturn 1] dans
  soit fun_code = comp_remainder [] dans
  (init_code, fun_code)
