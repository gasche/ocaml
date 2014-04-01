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

(* Detection of partial matches and unused match cases. *)

ouvre Misc
ouvre Asttypes
ouvre Types
ouvre Typedtree

(*************************************)
(* Utilities for building patterns   *)
(*************************************)

soit make_pat desc ty tenv =
  {pat_desc = desc; pat_loc = Location.none; pat_extra = [];
   pat_type = ty ; pat_env = tenv;
   pat_attributes = [];
  }

soit omega = make_pat Tpat_any Ctype.none Env.empty

soit extra_pat =
  make_pat
    (Tpat_var (Ident.create "+", mknoloc "+"))
    Ctype.none Env.empty

soit rec omegas i =
  si i <= 0 alors [] sinon omega :: omegas (i-1)

soit omega_list l = List.map (fonc _ -> omega) l

soit zero = make_pat (Tpat_constant (Const_int 0)) Ctype.none Env.empty

(***********************)
(* Compatibility check *)
(***********************)

(* p and q compatible means, there exists V that matches both *)

soit is_absent tag row = Btype.row_field tag !row = Rabsent

soit is_absent_pat p = filtre p.pat_desc avec
| Tpat_variant (tag, _, row) -> is_absent tag row
| _ -> faux

soit const_compare x y =
  filtre x,y avec
  | Const_float f1, Const_float f2 ->
      Pervasives.compare (float_of_string f1) (float_of_string f2)
  | Const_string (s1, _), Const_string (s2, _) ->
      String.compare s1 s2
  | _, _ -> Pervasives.compare x y

soit records_args l1 l2 =
  (* Invariant: fields are already sorted by Typecore.type_label_a_list *)
  soit rec combine r1 r2 l1 l2 = filtre l1,l2 avec
  | [],[] -> List.rev r1, List.rev r2
  | [],(_,_,p2)::rem2 -> combine (omega::r1) (p2::r2) [] rem2
  | (_,_,p1)::rem1,[] -> combine (p1::r1) (omega::r2) rem1 []
  | (_,lbl1,p1)::rem1, ( _,lbl2,p2)::rem2 ->
      si lbl1.lbl_pos < lbl2.lbl_pos alors
        combine (p1::r1) (omega::r2) rem1 l2
      sinon si lbl1.lbl_pos > lbl2.lbl_pos alors
        combine (omega::r1) (p2::r2) l1 rem2
      sinon (* same label on both sides *)
        combine (p1::r1) (p2::r2) rem1 rem2 dans
  combine [] [] l1 l2


soit rec compat p q =
  filtre p.pat_desc,q.pat_desc avec
  | Tpat_alias (p,_,_),_      -> compat p q
  | _,Tpat_alias (q,_,_)      -> compat p q
  | (Tpat_any|Tpat_var _),_ -> vrai
  | _,(Tpat_any|Tpat_var _) -> vrai
  | Tpat_or (p1,p2,_),_     -> compat p1 q || compat p2 q
  | _,Tpat_or (q1,q2,_)     -> compat p q1 || compat p q2
  | Tpat_constant c1, Tpat_constant c2 -> const_compare c1 c2 = 0
  | Tpat_tuple ps, Tpat_tuple qs -> compats ps qs
  | Tpat_lazy p, Tpat_lazy q -> compat p q
  | Tpat_construct (_, c1,ps1), Tpat_construct (_, c2,ps2) ->
      c1.cstr_tag = c2.cstr_tag && compats ps1 ps2
  | Tpat_variant(l1,Some p1, r1), Tpat_variant(l2,Some p2,_) ->
      l1=l2 && compat p1 p2
  | Tpat_variant (l1,None,r1), Tpat_variant(l2,None,_) ->
      l1 = l2
  | Tpat_variant (_, None, _), Tpat_variant (_,Some _, _) -> faux
  | Tpat_variant (_, Some _, _), Tpat_variant (_, None, _) -> faux
  | Tpat_record (l1,_),Tpat_record (l2,_) ->
      soit ps,qs = records_args l1 l2 dans
      compats ps qs
  | Tpat_array ps, Tpat_array qs ->
      List.length ps = List.length qs &&
      compats ps qs
  | _,_  ->
      affirme faux

et compats ps qs = filtre ps,qs avec
| [], [] -> vrai
| p::ps, q::qs -> compat p q && compats ps qs
| _,_    -> affirme faux

(****************************************)
(* Utilities for retrieving constructor *)
(* and record label names               *)
(****************************************)

exception Empty (* Empty pattern *)

(* May need a clean copy, cf. PR#4745 *)
soit clean_copy ty =
  si ty.level = Btype.generic_level alors ty
  sinon Subst.type_expr Subst.identity ty

soit get_type_path ty tenv =
  soit ty = Ctype.repr (Ctype.expand_head tenv (clean_copy ty)) dans
  filtre ty.desc avec
  | Tconstr (path,_,_) -> path
  | _ -> fatal_error "Parmatch.get_type_path"

soit get_type_descr ty tenv =
  filtre (Ctype.repr ty).desc avec
  | Tconstr (path,_,_) -> Env.find_type path tenv
  | _ -> fatal_error "Parmatch.get_type_descr"

soit rec get_constr tag ty tenv =
  filtre get_type_descr ty tenv avec
  | {type_kind=Type_variant constr_list} ->
      Datarepr.find_constr_by_tag tag constr_list
  | {type_manifest = Some _} ->
      get_constr tag (Ctype.expand_head_once tenv (clean_copy ty)) tenv
  | _ -> fatal_error "Parmatch.get_constr"

soit find_label lbl lbls =
  essaie
    soit l = List.nth lbls lbl.lbl_pos dans
    l.Types.ld_id
  avec Failure "nth" -> Ident.create "*Label inconnu*"

soit rec get_record_labels ty tenv =
  filtre get_type_descr ty tenv avec
  | {type_kind = Type_record(lbls, rep)} -> lbls
  | {type_manifest = Some _} ->
      get_record_labels (Ctype.expand_head_once tenv (clean_copy ty)) tenv
  | _ -> fatal_error "Parmatch.get_record_labels"


(*************************************)
(* Values as patterns pretty printer *)
(*************************************)

ouvre Format
;;

soit get_constr_name tag ty tenv  = filtre tag avec
| Cstr_exception (path, _) -> Path.name path
| _ ->
  essaie
    soit cd = get_constr tag ty tenv dans Ident.name cd.cd_id
  avec
  | Datarepr.Constr_not_found -> "*Constructeur inconnu*"

soit is_cons tag v  = filtre get_constr_name tag v.pat_type v.pat_env avec
| "::" -> vrai
| _ -> faux

soit pretty_const c = filtre c avec
| Const_int i -> Printf.sprintf "%d" i
| Const_char c -> Printf.sprintf "%C" c
| Const_string (s, _) -> Printf.sprintf "%S" s
| Const_float f -> Printf.sprintf "%s" f
| Const_int32 i -> Printf.sprintf "%ldl" i
| Const_int64 i -> Printf.sprintf "%LdL" i
| Const_nativeint i -> Printf.sprintf "%ndn" i

soit rec pretty_val ppf v =
  filtre v.pat_extra avec
      (cstr, _loc, _attrs) :: rem ->
        début filtre cstr avec
          | Tpat_unpack ->
            fprintf ppf "@[(module %a)@]" pretty_val { v avec pat_extra = rem }
          | Tpat_constraint ctyp ->
            fprintf ppf "@[(%a : _)@]" pretty_val { v avec pat_extra = rem }
          | Tpat_type _ ->
            fprintf ppf "@[(# %a)@]" pretty_val { v avec pat_extra = rem }
        fin
    | [] ->
  filtre v.pat_desc avec
  | Tpat_any -> fprintf ppf "_"
  | Tpat_var (x,_) -> Ident.print ppf x
  | Tpat_constant c -> fprintf ppf "%s" (pretty_const c)
  | Tpat_tuple vs ->
      fprintf ppf "@[(%a)@]" (pretty_vals ",") vs
  | Tpat_construct (_, {cstr_tag=tag},[]) ->
      soit name = get_constr_name tag v.pat_type v.pat_env dans
      fprintf ppf "%s" name
  | Tpat_construct (_, {cstr_tag=tag},[w]) ->
      soit name = get_constr_name tag v.pat_type v.pat_env dans
      fprintf ppf "@[<2>%s@ %a@]" name pretty_arg w
  | Tpat_construct (_, {cstr_tag=tag},vs) ->
      soit name = get_constr_name tag v.pat_type v.pat_env dans
      début filtre (name, vs) avec
        ("::", [v1;v2]) ->
          fprintf ppf "@[%a::@,%a@]" pretty_car v1 pretty_cdr v2
      |  _ ->
          fprintf ppf "@[<2>%s@ @[(%a)@]@]" name (pretty_vals ",") vs
      fin
  | Tpat_variant (l, None, _) ->
      fprintf ppf "`%s" l
  | Tpat_variant (l, Some w, _) ->
      fprintf ppf "@[<2>`%s@ %a@]" l pretty_arg w
  | Tpat_record (lvs,_) ->
      fprintf ppf "@[{%a}@]"
        (pretty_lvals (get_record_labels v.pat_type v.pat_env))
        (List.filter
           (fonction
             | (_,_,{pat_desc=Tpat_any}) -> faux (* do not show lbl=_ *)
             | _ -> vrai) lvs)
  | Tpat_array vs ->
      fprintf ppf "@[[| %a |]@]" (pretty_vals " ;") vs
  | Tpat_lazy v ->
      fprintf ppf "@[<2>paresseux@ %a@]" pretty_arg v
  | Tpat_alias (v, x,_) ->
      fprintf ppf "@[(%a@ comme %a)@]" pretty_val v Ident.print x
  | Tpat_or (v,w,_)    ->
      fprintf ppf "@[(%a|@,%a)@]" pretty_or v pretty_or w

et pretty_car ppf v = filtre v.pat_desc avec
| Tpat_construct (_,{cstr_tag=tag}, [_ ; _])
    quand is_cons tag v ->
      fprintf ppf "(%a)" pretty_val v
| _ -> pretty_val ppf v

et pretty_cdr ppf v = filtre v.pat_desc avec
| Tpat_construct (_,{cstr_tag=tag}, [v1 ; v2])
    quand is_cons tag v ->
      fprintf ppf "%a::@,%a" pretty_car v1 pretty_cdr v2
| _ -> pretty_val ppf v

et pretty_arg ppf v = filtre v.pat_desc avec
| Tpat_construct (_,_,_::_) -> fprintf ppf "(%a)" pretty_val v
|  _ -> pretty_val ppf v

et pretty_or ppf v = filtre v.pat_desc avec
| Tpat_or (v,w,_) ->
    fprintf ppf "%a|@,%a" pretty_or v pretty_or w
| _ -> pretty_val ppf v

et pretty_vals sep ppf = fonction
  | [] -> ()
  | [v] -> pretty_val ppf v
  | v::vs ->
      fprintf ppf "%a%s@ %a" pretty_val v sep (pretty_vals sep) vs

et pretty_lvals lbls ppf = fonction
  | [] -> ()
  | [_,lbl,v] ->
      soit name = find_label lbl lbls dans
      fprintf ppf "%s=%a" (Ident.name name) pretty_val v
  | (_, lbl,v)::rest ->
      soit name = find_label lbl lbls dans
      fprintf ppf "%s=%a;@ %a"
        (Ident.name name) pretty_val v (pretty_lvals lbls) rest

soit top_pretty ppf v =
  fprintf ppf "@[%a@]@?" pretty_val v


soit pretty_pat p =
  top_pretty Format.str_formatter p ;
  prerr_string (Format.flush_str_formatter ())

type matrix = pattern list list

soit pretty_line ps =
  List.iter
    (fonc p ->
      top_pretty Format.str_formatter p ;
      prerr_string " <" ;
      prerr_string (Format.flush_str_formatter ()) ;
      prerr_string ">")
    ps

soit pretty_matrix (pss : matrix) =
  prerr_endline "début matrice" ;
  List.iter
    (fonc ps ->
      pretty_line ps ;
      prerr_endline "")
    pss ;
  prerr_endline "fin matrice"


(****************************)
(* Utilities for matching   *)
(****************************)

(* Check top matching *)
soit simple_match p1 p2 =
  filtre p1.pat_desc, p2.pat_desc avec
  | Tpat_construct(_, c1, _), Tpat_construct(_, c2, _) ->
      c1.cstr_tag = c2.cstr_tag
  | Tpat_variant(l1, _, _), Tpat_variant(l2, _, _) ->
      l1 = l2
  | Tpat_constant(c1), Tpat_constant(c2) -> const_compare c1 c2 = 0
  | Tpat_tuple _, Tpat_tuple _ -> vrai
  | Tpat_lazy _, Tpat_lazy _ -> vrai
  | Tpat_record _ , Tpat_record _ -> vrai
  | Tpat_array p1s, Tpat_array p2s -> List.length p1s = List.length p2s
  | _, (Tpat_any | Tpat_var(_)) -> vrai
  | _, _ -> faux




(* extract record fields as a whole *)
soit record_arg p = filtre p.pat_desc avec
| Tpat_any -> []
| Tpat_record (args,_) -> args
| _ -> fatal_error "Parmatch.as_record"


(* Raise Not_found when pos is not present in arg *)
soit get_field pos arg =
  soit _,_, p = List.find (fonc (_,lbl,_) -> pos = lbl.lbl_pos) arg dans
  p

soit extract_fields omegas arg =
  List.map
    (fonc (_,lbl,_) ->
      essaie
        get_field lbl.lbl_pos arg
      avec Not_found -> omega)
    omegas

soit all_record_args lbls = filtre lbls avec
| (_,{lbl_all=lbl_all},_)::_ ->
    soit t =
      Array.map
        (fonc lbl -> mknoloc (Longident.Lident "?temp?"), lbl,omega)
        lbl_all dans
    List.iter
      (fonc ((_, lbl,_) tel x) ->  t.(lbl.lbl_pos) <- x)
      lbls ;
    Array.to_list t
|  _ -> fatal_error "Parmatch.all_record_args"


(* Build argument list when p2 >= p1, where p1 is a simple pattern *)
soit rec simple_match_args p1 p2 = filtre p2.pat_desc avec
| Tpat_alias (p2,_,_) -> simple_match_args p1 p2
| Tpat_construct(_, cstr, args) -> args
| Tpat_variant(lab, Some arg, _) -> [arg]
| Tpat_tuple(args)  -> args
| Tpat_record(args,_) ->  extract_fields (record_arg p1) args
| Tpat_array(args) -> args
| Tpat_lazy arg -> [arg]
| (Tpat_any | Tpat_var(_)) ->
    début filtre p1.pat_desc avec
      Tpat_construct(_, _,args) -> omega_list args
    | Tpat_variant(_, Some _, _) -> [omega]
    | Tpat_tuple(args) -> omega_list args
    | Tpat_record(args,_) ->  omega_list args
    | Tpat_array(args) ->  omega_list args
    | Tpat_lazy _ -> [omega]
    | _ -> []
    fin
| _ -> []

(*
  Normalize a pattern ->
   all arguments are omega (simple pattern) and no more variables
*)

soit rec normalize_pat q = filtre q.pat_desc avec
  | Tpat_any | Tpat_constant _ -> q
  | Tpat_var _ -> make_pat Tpat_any q.pat_type q.pat_env
  | Tpat_alias (p,_,_) -> normalize_pat p
  | Tpat_tuple (args) ->
      make_pat (Tpat_tuple (omega_list args)) q.pat_type q.pat_env
  | Tpat_construct  (lid, c,args) ->
      make_pat
        (Tpat_construct (lid, c,omega_list args))
        q.pat_type q.pat_env
  | Tpat_variant (l, arg, row) ->
      make_pat (Tpat_variant (l, may_map (fonc _ -> omega) arg, row))
        q.pat_type q.pat_env
  | Tpat_array (args) ->
      make_pat (Tpat_array (omega_list args))  q.pat_type q.pat_env
  | Tpat_record (largs, closed) ->
      make_pat
        (Tpat_record (List.map (fonc (lid,lbl,_) ->
                                 lid, lbl,omega) largs, closed))
        q.pat_type q.pat_env
  | Tpat_lazy _ ->
      make_pat (Tpat_lazy omega) q.pat_type q.pat_env
  | Tpat_or _ -> fatal_error "Parmatch.normalize_pat"

(*
  Build normalized (cf. supra) discriminating pattern,
  in the non-data type case
*)

soit discr_pat q pss =

  soit rec acc_pat acc pss = filtre pss avec
    ({pat_desc = Tpat_alias (p,_,_)}::ps)::pss ->
        acc_pat acc ((p::ps)::pss)
  | ({pat_desc = Tpat_or (p1,p2,_)}::ps)::pss ->
        acc_pat acc ((p1::ps)::(p2::ps)::pss)
  | ({pat_desc = (Tpat_any | Tpat_var _)}::_)::pss ->
        acc_pat acc pss
  | (({pat_desc = Tpat_tuple _} tel p)::_)::_ -> normalize_pat p
  | (({pat_desc = Tpat_lazy _} tel p)::_)::_ -> normalize_pat p
  | (({pat_desc = Tpat_record (largs,closed)} tel p)::_)::pss ->
      soit new_omegas =
        List.fold_right
          (fonc (lid, lbl,_) r ->
            essaie
              soit _ = get_field lbl.lbl_pos r dans
              r
            avec Not_found ->
              (lid, lbl,omega)::r)
          largs (record_arg acc)
      dans
      acc_pat
        (make_pat (Tpat_record (new_omegas, closed)) p.pat_type p.pat_env)
        pss
  | _ -> acc dans

  filtre normalize_pat q avec
  | {pat_desc= (Tpat_any | Tpat_record _)} tel q -> acc_pat q pss
  | q -> q

(*
   In case a matching value is found, set actual arguments
   of the matching pattern.
*)

soit rec read_args xs r = filtre xs,r avec
| [],_ -> [],r
| _::xs, arg::rest ->
   soit args,rest = read_args xs rest dans
   arg::args,rest
| _,_ ->
    fatal_error "Parmatch.read_args"

soit do_set_args erase_mutable q r = filtre q avec
| {pat_desc = Tpat_tuple omegas} ->
    soit args,rest = read_args omegas r dans
    make_pat (Tpat_tuple args) q.pat_type q.pat_env::rest
| {pat_desc = Tpat_record (omegas,closed)} ->
    soit args,rest = read_args omegas r dans
    make_pat
      (Tpat_record
         (List.map2 (fonc (lid, lbl,_) arg ->
           si
             erase_mutable &&
             (filtre lbl.lbl_mut avec
             | Mutable -> vrai | Immutable -> faux)
           alors
             lid, lbl, omega
           sinon
             lid, lbl, arg)
            omegas args, closed))
      q.pat_type q.pat_env::
    rest
| {pat_desc = Tpat_construct (lid, c,omegas)} ->
    soit args,rest = read_args omegas r dans
    make_pat
      (Tpat_construct (lid, c,args))
      q.pat_type q.pat_env::
    rest
| {pat_desc = Tpat_variant (l, omega, row)} ->
    soit arg, rest =
      filtre omega, r avec
        Some _, a::r -> Some a, r
      | None, r -> None, r
      | _ -> affirme faux
    dans
    make_pat
      (Tpat_variant (l, arg, row)) q.pat_type q.pat_env::
    rest
| {pat_desc = Tpat_lazy omega} ->
    début filtre r avec
      arg::rest ->
        make_pat (Tpat_lazy arg) q.pat_type q.pat_env::rest
    | _ -> fatal_error "Parmatch.do_set_args (lazy)"
    fin
| {pat_desc = Tpat_array omegas} ->
    soit args,rest = read_args omegas r dans
    make_pat
      (Tpat_array args) q.pat_type q.pat_env::
    rest
| {pat_desc=Tpat_constant _|Tpat_any} ->
    q::r (* case any is used in matching.ml *)
| _ -> fatal_error "Parmatch.set_args"

soit set_args q r = do_set_args faux q r
et set_args_erase_mutable q r = do_set_args vrai q r

(* filter pss acording to pattern q *)
soit filter_one q pss =
  soit rec filter_rec = fonction
      ({pat_desc = Tpat_alias(p,_,_)}::ps)::pss ->
        filter_rec ((p::ps)::pss)
    | ({pat_desc = Tpat_or(p1,p2,_)}::ps)::pss ->
        filter_rec ((p1::ps)::(p2::ps)::pss)
    | (p::ps)::pss ->
        si simple_match q p
        alors (simple_match_args q p @ ps) :: filter_rec pss
        sinon filter_rec pss
    | _ -> [] dans
  filter_rec pss

(*
  Filter pss in the ``extra case''. This applies :
  - According to an extra constructor (datatype case, non-complete signature).
  - Acordinng to anything (all-variables case).
*)
soit filter_extra pss =
  soit rec filter_rec = fonction
      ({pat_desc = Tpat_alias(p,_,_)}::ps)::pss ->
        filter_rec ((p::ps)::pss)
    | ({pat_desc = Tpat_or(p1,p2,_)}::ps)::pss ->
        filter_rec ((p1::ps)::(p2::ps)::pss)
    | ({pat_desc = (Tpat_any | Tpat_var(_))} :: qs) :: pss ->
        qs :: filter_rec pss
    | _::pss  -> filter_rec pss
    | [] -> [] dans
  filter_rec pss

(*
  Pattern p0 is the discriminating pattern,
  returns [(q0,pss0) ; ... ; (qn,pssn)]
  where the qi's are simple patterns and the pssi's are
  matched matrices.

  NOTES
   * (qi,[]) is impossible.
   * In the case when matching is useless (all-variable case),
     returns []
*)

soit filter_all pat0 pss =

  soit rec insert q qs env =
    filtre env avec
      [] ->
        soit q0 = normalize_pat q dans
        [q0, [simple_match_args q0 q @ qs]]
    | ((q0,pss) tel c)::env ->
        si simple_match q0 q
        alors (q0, ((simple_match_args q0 q @ qs) :: pss)) :: env
        sinon c :: insert q qs env dans

  soit rec filter_rec env = fonction
    ({pat_desc = Tpat_alias(p,_,_)}::ps)::pss ->
      filter_rec env ((p::ps)::pss)
  | ({pat_desc = Tpat_or(p1,p2,_)}::ps)::pss ->
      filter_rec env ((p1::ps)::(p2::ps)::pss)
  | ({pat_desc = (Tpat_any | Tpat_var(_))}::_)::pss ->
      filter_rec env pss
  | (p::ps)::pss ->
      filter_rec (insert p ps env) pss
  | _ -> env

  et filter_omega env = fonction
    ({pat_desc = Tpat_alias(p,_,_)}::ps)::pss ->
      filter_omega env ((p::ps)::pss)
  | ({pat_desc = Tpat_or(p1,p2,_)}::ps)::pss ->
      filter_omega env ((p1::ps)::(p2::ps)::pss)
  | ({pat_desc = (Tpat_any | Tpat_var(_))}::ps)::pss ->
      filter_omega
        (List.map (fonc (q,qss) -> (q,(simple_match_args q omega @ ps) :: qss))
           env)
        pss
  | _::pss -> filter_omega env pss
  | [] -> env dans

  filter_omega
    (filter_rec
      (filtre pat0.pat_desc avec
        (Tpat_record(_) | Tpat_tuple(_) | Tpat_lazy(_)) -> [pat0,[]]
      | _ -> [])
      pss)
    pss

(* Variant related functions *)

soit rec set_last a = fonction
    [] -> []
  | [_] -> [a]
  | x::l -> x :: set_last a l

(* mark constructor lines for failure when they are incomplete *)
soit rec mark_partial = fonction
    ({pat_desc = Tpat_alias(p,_,_)}::ps)::pss ->
      mark_partial ((p::ps)::pss)
  | ({pat_desc = Tpat_or(p1,p2,_)}::ps)::pss ->
      mark_partial ((p1::ps)::(p2::ps)::pss)
  | ({pat_desc = (Tpat_any | Tpat_var(_))} :: _ tel ps) :: pss ->
      ps :: mark_partial pss
  | ps::pss  ->
      (set_last zero ps) :: mark_partial pss
  | [] -> []

soit close_variant env row =
  soit row = Btype.row_repr row dans
  soit nm =
    List.fold_left
      (fonc nm (tag,f) ->
        filtre Btype.row_field_repr f avec
        | Reither(_, _, faux, e) ->
            (* m=false means that this tag is not explicitly matched *)
            Btype.set_row_field e Rabsent;
            None
        | Rabsent | Reither (_, _, vrai, _) | Rpresent _ -> nm)
      row.row_name row.row_fields dans
  si not row.row_closed || nm != row.row_name alors début
    (* this unification cannot fail *)
    Ctype.unify env row.row_more
      (Btype.newgenty
         (Tvariant {row avec row_fields = []; row_more = Btype.newgenvar();
                    row_closed = vrai; row_name = nm}))
  fin

soit row_of_pat pat =
  filtre Ctype.expand_head pat.pat_env pat.pat_type avec
    {desc = Tvariant row} -> Btype.row_repr row
  | _ -> affirme faux

(*
  Check whether the first column of env makes up a complete signature or
  not.
*)

soit generalized_constructor x =
  filtre x avec
    ({pat_desc = Tpat_construct(_,c,_);pat_env=env},_) ->
      c.cstr_generalized
  | _ -> affirme faux

soit clean_env env =
  soit rec loop =
    fonction
      | [] -> []
      | x :: xs ->
          si generalized_constructor x alors loop xs sinon x :: loop xs
  dans
  loop env

soit full_match ignore_generalized closing env =  filtre env avec
| ({pat_desc = Tpat_construct (_,{cstr_tag=Cstr_exception _},_)},_)::_ ->
    faux
| ({pat_desc = Tpat_construct(_,c,_);pat_type=typ},_) :: _ ->
    si ignore_generalized alors
      (* remove generalized constructors;
         those cases will be handled separately *)
      soit env = clean_env env dans
      List.length env = c.cstr_normal
    sinon
      List.length env = c.cstr_consts + c.cstr_nonconsts

| ({pat_desc = Tpat_variant _} tel p,_) :: _ ->
    soit fields =
      List.map
        (fonction ({pat_desc = Tpat_variant (tag, _, _)}, _) -> tag
          | _ -> affirme faux)
        env
    dans
    soit row = row_of_pat p dans
    si closing && not (Btype.row_fixed row) alors
      (* closing=true, we are considering the variant as closed *)
      List.for_all
        (fonc (tag,f) ->
          filtre Btype.row_field_repr f avec
            Rabsent | Reither(_, _, faux, _) -> vrai
          | Reither (_, _, vrai, _)
              (* m=true, do not discard matched tags, rather warn *)
          | Rpresent _ -> List.mem tag fields)
        row.row_fields
    sinon
      row.row_closed &&
      List.for_all
        (fonc (tag,f) ->
          Btype.row_field_repr f = Rabsent || List.mem tag fields)
        row.row_fields
| ({pat_desc = Tpat_constant(Const_char _)},_) :: _ ->
    List.length env = 256
| ({pat_desc = Tpat_constant(_)},_) :: _ -> faux
| ({pat_desc = Tpat_tuple(_)},_) :: _ -> vrai
| ({pat_desc = Tpat_record(_)},_) :: _ -> vrai
| ({pat_desc = Tpat_array(_)},_) :: _ -> faux
| ({pat_desc = Tpat_lazy(_)},_) :: _ -> vrai
| _ -> fatal_error "Parmatch.full_match"

soit full_match_gadt env = filtre env avec
  | ({pat_desc = Tpat_construct(_,c,_);pat_type=typ},_) :: _ ->
    List.length env = c.cstr_consts + c.cstr_nonconsts
  | _ -> vrai

soit extendable_match env = filtre env avec
| ({pat_desc=Tpat_construct(_,{cstr_tag=(Cstr_constant _|Cstr_block _)},_)}
     tel p,_) :: _ ->
    soit path = get_type_path p.pat_type p.pat_env dans
    not
      (Path.same path Predef.path_bool ||
      Path.same path Predef.path_list ||
      Path.same path Predef.path_option)
| _ -> faux


soit should_extend ext env = filtre ext avec
| None -> faux
| Some ext -> filtre env avec
  | ({pat_desc =
      Tpat_construct(_, {cstr_tag=(Cstr_constant _|Cstr_block _)},_)}
     tel p, _) :: _ ->
      soit path = get_type_path p.pat_type p.pat_env dans
      Path.same path ext
  | _ -> faux

(* complement constructor tags *)
soit complete_tags nconsts nconstrs tags =
  soit seen_const = Array.create nconsts faux
  et seen_constr = Array.create nconstrs faux dans
  List.iter
    (fonction
      | Cstr_constant i -> seen_const.(i) <- vrai
      | Cstr_block i -> seen_constr.(i) <- vrai
      | _  -> affirme faux)
    tags ;
  soit r = ref [] dans
  pour i = 0 à nconsts-1 faire
    si not seen_const.(i) alors
      r := Cstr_constant i :: !r
  fait ;
  pour i = 0 à nconstrs-1 faire
    si not seen_constr.(i) alors
      r := Cstr_block i :: !r
  fait ;
  !r

(* build a pattern from a constructor list *)
soit pat_of_constr ex_pat cstr =
 {ex_pat avec pat_desc =
  Tpat_construct (mknoloc (Longident.Lident "?pat_of_constr?"),
                  cstr,omegas cstr.cstr_arity)}

soit rec pat_of_constrs ex_pat = fonction
| [] -> raise Empty
| [cstr] -> pat_of_constr ex_pat cstr
| cstr::rem ->
    {ex_pat avec
    pat_desc=
      Tpat_or
        (pat_of_constr ex_pat cstr,
         pat_of_constrs ex_pat rem, None)}

exception Not_an_adt

soit rec adt_path env ty =
  filtre get_type_descr ty env avec
  | {type_kind=Type_variant constr_list} ->
      début filtre (Ctype.repr ty).desc avec
      | Tconstr (path,_,_) ->
          path
      | _ -> affirme faux fin
  | {type_manifest = Some _} ->
      adt_path env (Ctype.expand_head_once env (clean_copy ty))
  | _ -> raise Not_an_adt
;;

soit rec map_filter f  =
  fonction
      [] -> []
    | x :: xs ->
        filtre f x avec
        | None -> map_filter f xs
        | Some y -> y :: map_filter f xs

(* Sends back a pattern that complements constructor tags all_tag *)
soit complete_constrs p all_tags =
  filtre p.pat_desc avec
  | Tpat_construct (_,c,_) ->
      début essaie
        soit not_tags = complete_tags c.cstr_consts c.cstr_nonconsts all_tags dans
        soit (constrs, _) =
          Env.find_type_descrs (adt_path p.pat_env p.pat_type) p.pat_env dans
        map_filter
          (fonc cnstr ->
            si List.mem cnstr.cstr_tag not_tags alors Some cnstr sinon None)
          constrs
      avec
      | Datarepr.Constr_not_found ->
          fatal_error "Parmatch.complete_constr: constr_not_found"
      fin
  | _ -> fatal_error "Parmatch.complete_constr"


(* Auxiliary for build_other *)

soit build_other_constant proj make first next p env =
  soit all = List.map (fonc (p, _) -> proj p.pat_desc) env dans
  soit rec try_const i =
    si List.mem i all
    alors try_const (next i)
    sinon make_pat (make i) p.pat_type p.pat_env
  dans try_const first

(*
  Builds a pattern that is incompatible with all patterns in
  in the first column of env
*)

soit build_other ext env =  filtre env avec
| ({pat_desc =
    Tpat_construct (lid, ({cstr_tag=Cstr_exception _} tel c),_)},_)
  ::_ ->
    make_pat
      (Tpat_construct
         (lid, {c avec
           cstr_tag=(Cstr_exception
            (Path.Pident (Ident.create "*exception*"), Location.none))},
          []))
      Ctype.none Env.empty
| ({pat_desc = Tpat_construct (_, _,_)} tel p,_) :: _ ->
    début filtre ext avec
    | Some ext quand Path.same ext (get_type_path p.pat_type p.pat_env) ->
        extra_pat
    | _ ->
        soit get_tag = fonction
          | {pat_desc = Tpat_construct (_,c,_)} -> c.cstr_tag
          | _ -> fatal_error "Parmatch.get_tag" dans
        soit all_tags =  List.map (fonc (p,_) -> get_tag p) env dans
        pat_of_constrs p (complete_constrs p all_tags)
    fin
| ({pat_desc = Tpat_variant (_,_,r)} tel p,_) :: _ ->
    soit tags =
      List.map
        (fonction ({pat_desc = Tpat_variant (tag, _, _)}, _) -> tag
                | _ -> affirme faux)
        env
    dans
    soit row = row_of_pat p dans
    soit make_other_pat tag const =
      soit arg = si const alors None sinon Some omega dans
      make_pat (Tpat_variant(tag, arg, r)) p.pat_type p.pat_env dans
    début filtre
      List.fold_left
        (fonc others (tag,f) ->
          si List.mem tag tags alors others sinon
          filtre Btype.row_field_repr f avec
            Rabsent (* | Reither _ *) -> others
          (* This one is called after erasing pattern info *)
          | Reither (c, _, _, _) -> make_other_pat tag c :: others
          | Rpresent arg -> make_other_pat tag (arg = None) :: others)
        [] row.row_fields
    avec
      [] ->
        make_other_pat "AnyExtraTag" vrai
    | pat::other_pats ->
        List.fold_left
          (fonc p_res pat ->
            make_pat (Tpat_or (pat, p_res, None)) p.pat_type p.pat_env)
          pat other_pats
    fin
| ({pat_desc = Tpat_constant(Const_char _)} tel p,_) :: _ ->
    soit all_chars =
      List.map
        (fonc (p,_) -> filtre p.pat_desc avec
        | Tpat_constant (Const_char c) -> c
        | _ -> affirme faux)
        env dans

    soit rec find_other i imax =
      si i > imax alors raise Not_found
      sinon
        soit ci = Char.chr i dans
        si List.mem ci all_chars alors
          find_other (i+1) imax
        sinon
          make_pat (Tpat_constant (Const_char ci)) p.pat_type p.pat_env dans
    soit rec try_chars = fonction
      | [] -> omega
      | (c1,c2) :: rest ->
          essaie
            find_other (Char.code c1) (Char.code c2)
          avec
          | Not_found -> try_chars rest dans

    try_chars
      [ 'a', 'z' ; 'A', 'Z' ; '0', '9' ;
        ' ', '~' ; Char.chr 0 , Char.chr 255]

| ({pat_desc=(Tpat_constant (Const_int _))} tel p,_) :: _ ->
    build_other_constant
      (fonction Tpat_constant(Const_int i) -> i | _ -> affirme faux)
      (fonction i -> Tpat_constant(Const_int i))
      0 succ p env
| ({pat_desc=(Tpat_constant (Const_int32 _))} tel p,_) :: _ ->
    build_other_constant
      (fonction Tpat_constant(Const_int32 i) -> i | _ -> affirme faux)
      (fonction i -> Tpat_constant(Const_int32 i))
      0l Int32.succ p env
| ({pat_desc=(Tpat_constant (Const_int64 _))} tel p,_) :: _ ->
    build_other_constant
      (fonction Tpat_constant(Const_int64 i) -> i | _ -> affirme faux)
      (fonction i -> Tpat_constant(Const_int64 i))
      0L Int64.succ p env
| ({pat_desc=(Tpat_constant (Const_nativeint _))} tel p,_) :: _ ->
    build_other_constant
      (fonction Tpat_constant(Const_nativeint i) -> i | _ -> affirme faux)
      (fonction i -> Tpat_constant(Const_nativeint i))
      0n Nativeint.succ p env
| ({pat_desc=(Tpat_constant (Const_string _))} tel p,_) :: _ ->
    build_other_constant
      (fonction Tpat_constant(Const_string (s, _)) -> String.length s
              | _ -> affirme faux)
      (fonction i -> Tpat_constant(Const_string(String.make i '*', None)))
      0 succ p env
| ({pat_desc=(Tpat_constant (Const_float _))} tel p,_) :: _ ->
    build_other_constant
      (fonction Tpat_constant(Const_float f) -> float_of_string f
              | _ -> affirme faux)
      (fonction f -> Tpat_constant(Const_float (string_of_float f)))
      0.0 (fonc f -> f +. 1.0) p env

| ({pat_desc = Tpat_array args} tel p,_)::_ ->
    soit all_lengths =
      List.map
        (fonc (p,_) -> filtre p.pat_desc avec
        | Tpat_array args -> List.length args
        | _ -> affirme faux)
        env dans
    soit rec try_arrays l =
      si List.mem l all_lengths alors try_arrays (l+1)
      sinon
        make_pat
          (Tpat_array (omegas l))
          p.pat_type p.pat_env dans
    try_arrays 0
| [] -> omega
| _ -> omega

soit build_other_gadt ext env =
  filtre env avec
    | ({pat_desc = Tpat_construct _} tel p,_) :: _ ->
        soit get_tag = fonction
          | {pat_desc = Tpat_construct (_,c,_)} -> c.cstr_tag
          | _ -> fatal_error "Parmatch.get_tag" dans
        soit all_tags =  List.map (fonc (p,_) -> get_tag p) env dans
        soit cnstrs  = complete_constrs p all_tags dans
        soit pats = List.map (pat_of_constr p) cnstrs dans
        (* List.iter (Format.eprintf "%a@." top_pretty) pats;
           Format.eprintf "@.@."; *)
        pats
    | _ -> affirme faux

(*
  Core function :
  Is the last row of pattern matrix pss + qs satisfiable ?
  That is :
    Does there exists at least one value vector, es such that :
     1- for all ps in pss ps # es (ps and es are not compatible)
     2- qs <= es                  (es matches qs)
*)

soit rec has_instance p = filtre p.pat_desc avec
  | Tpat_variant (l,_,r) quand is_absent l r -> faux
  | Tpat_any | Tpat_var _ | Tpat_constant _ | Tpat_variant (_,None,_) -> vrai
  | Tpat_alias (p,_,_) | Tpat_variant (_,Some p,_) -> has_instance p
  | Tpat_or (p1,p2,_) -> has_instance p1 || has_instance p2
  | Tpat_construct (_,_,ps) | Tpat_tuple ps | Tpat_array ps ->
      has_instances ps
  | Tpat_record (lps,_) -> has_instances (List.map (fonc (_,_,x) -> x) lps)
  | Tpat_lazy p
    -> has_instance p


et has_instances = fonction
  | [] -> vrai
  | q::rem -> has_instance q && has_instances rem

soit rec satisfiable pss qs = filtre pss avec
| [] -> has_instances qs
| _  ->
    filtre qs avec
    | [] -> faux
    | {pat_desc = Tpat_or(q1,q2,_)}::qs ->
        satisfiable pss (q1::qs) || satisfiable pss (q2::qs)
    | {pat_desc = Tpat_alias(q,_,_)}::qs ->
          satisfiable pss (q::qs)
    | {pat_desc = (Tpat_any | Tpat_var(_))}::qs ->
        soit q0 = discr_pat omega pss dans
        début filtre filter_all q0 pss avec
          (* first column of pss is made of variables only *)
        | [] -> satisfiable (filter_extra pss) qs
        | constrs  ->
            si full_match faux faux constrs alors
              List.exists
                (fonc (p,pss) ->
                  not (is_absent_pat p) &&
                  satisfiable pss (simple_match_args p omega @ qs))
                constrs
            sinon
              satisfiable (filter_extra pss) qs
        fin
    | {pat_desc=Tpat_variant (l,_,r)}::_ quand is_absent l r -> faux
    | q::qs ->
        soit q0 = discr_pat q pss dans
        satisfiable (filter_one q0 pss) (simple_match_args q0 q @ qs)

(*
  Now another satisfiable function that additionally
  supplies an example of a matching value.

  This function should be called for exhaustiveness check only.
*)

type 'a result =
  | Rnone           (* No matching value *)
  | Rsome de 'a     (* This matching value *)

soit rec orify_many =
  soit orify x y =
    make_pat (Tpat_or (x, y, None)) x.pat_type x.pat_env
  dans
  fonction
    | [] -> affirme faux
    | [x] -> x
    | x :: xs -> orify x (orify_many xs)

soit rec try_many  f = fonction
  | [] -> Rnone
  | (p,pss)::rest ->
      filtre f (p,pss) avec
      | Rnone -> try_many  f rest
      | r -> r

soit rappend r1 r2 =
  filtre r1, r2 avec
  | Rnone, _ -> r2
  | _, Rnone -> r1
  | Rsome l1, Rsome l2 -> Rsome (l1 @ l2)

soit rec try_many_gadt  f = fonction
  | [] -> Rnone
  | (p,pss)::rest ->
      rappend (f (p, pss)) (try_many_gadt f rest)

soit rec exhaust ext pss n = filtre pss avec
| []    ->  Rsome (omegas n)
| []::_ ->  Rnone
| pss   ->
    soit q0 = discr_pat omega pss dans
    début filtre filter_all q0 pss avec
          (* first column of pss is made of variables only *)
    | [] ->
        début filtre exhaust ext (filter_extra pss) (n-1) avec
        | Rsome r -> Rsome (q0::r)
        | r -> r
      fin
    | constrs ->
        soit try_non_omega (p,pss) =
          si is_absent_pat p alors
            Rnone
          sinon
            filtre
              exhaust
                ext pss (List.length (simple_match_args p omega) + n - 1)
            avec
            | Rsome r -> Rsome (set_args p r)
            | r       -> r dans
        si
          full_match vrai faux constrs && not (should_extend ext constrs)
        alors
          try_many try_non_omega constrs
        sinon
          (*
             D = filter_extra pss is the default matrix
             as it is included in pss, one can avoid
             recursive calls on specialized matrices,
             Essentially :
             * D exhaustive => pss exhaustive
             * D non-exhaustive => we have a non-filtered value
          *)
          soit r =  exhaust ext (filter_extra pss) (n-1) dans
          filtre r avec
          | Rnone -> Rnone
          | Rsome r ->
              essaie
                Rsome (build_other ext constrs::r)
              avec
      (* cannot occur, since constructors don't make a full signature *)
              | Empty -> fatal_error "Parmatch.exhaust"
    fin

soit combinations f lst lst' =
  soit rec iter2 x =
    fonction
        [] -> []
      | y :: ys ->
          f x y :: iter2 x ys
  dans
  soit rec iter =
    fonction
        [] -> []
      | x :: xs -> iter2 x lst' @ iter xs
  dans
  iter lst

(*
let print_pat pat =
  let rec string_of_pat pat =
    match pat.pat_desc with
        Tpat_var _ -> "v"
      | Tpat_any -> "_"
      | Tpat_alias (p, x) -> Printf.sprintf "(%s) as ?"  (string_of_pat p)
      | Tpat_constant n -> "0"
      | Tpat_construct (_, lid, _) ->
        Printf.sprintf "%s" (String.concat "." (Longident.flatten lid.txt))
      | Tpat_lazy p ->
        Printf.sprintf "(lazy %s)" (string_of_pat p)
      | Tpat_or (p1,p2,_) ->
        Printf.sprintf "(%s | %s)" (string_of_pat p1) (string_of_pat p2)
      | Tpat_tuple list ->
        Printf.sprintf "(%s)" (String.concat "," (List.map string_of_pat list))
      | Tpat_variant (_, _, _) -> "variant"
      | Tpat_record (_, _) -> "record"
      | Tpat_array _ -> "array"
  in
  Printf.fprintf stderr "PAT[%s]\n%!" (string_of_pat pat)
*)

(* strictly more powerful than exhaust; however, exhaust
   was kept for backwards compatibility *)
soit rec exhaust_gadt (ext:Path.t option) pss n = filtre pss avec
| []    ->  Rsome [omegas n]
| []::_ ->  Rnone
| pss   ->
    soit q0 = discr_pat omega pss dans
    début filtre filter_all q0 pss avec
          (* first column of pss is made of variables only *)
    | [] ->
        début filtre exhaust_gadt ext (filter_extra pss) (n-1) avec
        | Rsome r -> Rsome (List.map (fonc row -> q0::row) r)
        | r -> r
      fin
    | constrs ->
        soit try_non_omega (p,pss) =
          si is_absent_pat p alors
            Rnone
          sinon
            filtre
              exhaust_gadt
                ext pss (List.length (simple_match_args p omega) + n - 1)
            avec
            | Rsome r -> Rsome (List.map (fonc row ->  (set_args p row)) r)
            | r       -> r dans
        soit before = try_many_gadt try_non_omega constrs dans
        si
          full_match_gadt constrs && not (should_extend ext constrs)
        alors
          before
        sinon
          (*
            D = filter_extra pss is the default matrix
            as it is included in pss, one can avoid
            recursive calls on specialized matrices,
            Essentially :
           * D exhaustive => pss exhaustive
           * D non-exhaustive => we have a non-filtered value
           *)
          soit r =  exhaust_gadt ext (filter_extra pss) (n-1) dans
          filtre r avec
          | Rnone -> before
          | Rsome r ->
              essaie
                soit missing_trailing = build_other_gadt ext constrs dans
                soit dug =
                  combinations
                    (fonc head tail -> head :: tail)
                    missing_trailing
                    r
                dans
                filtre before avec
                | Rnone -> Rsome dug
                | Rsome x -> Rsome (x @ dug)
              avec
      (* cannot occur, since constructors don't make a full signature *)
              | Empty -> fatal_error "Parmatch.exhaust"
    fin

soit exhaust_gadt ext pss n =
  soit ret = exhaust_gadt ext pss n dans
  filtre ret avec
    Rnone -> Rnone
  | Rsome lst ->
      (* The following line is needed to compile stdlib/printf.ml *)
      si lst = [] alors Rsome (omegas n) sinon
      soit singletons =
        List.map
          (fonction
              [x] -> x
            | _ -> affirme faux)
          lst
      dans
      Rsome [orify_many singletons]

(*
   Another exhaustiveness check, enforcing variant typing.
   Note that it does not check exact exhaustiveness, but whether a
   matching could be made exhaustive by closing all variant types.
   When this is true of all other columns, the current column is left
   open (even if it means that the whole matching is not exhaustive as
   a result).
   When this is false for the matrix minus the current column, and the
   current column is composed of variant tags, we close the variant
   (even if it doesn't help in making the matching exhaustive).
*)

soit rec pressure_variants tdefs = fonction
  | []    -> faux
  | []::_ -> vrai
  | pss   ->
      soit q0 = discr_pat omega pss dans
      début filtre filter_all q0 pss avec
        [] -> pressure_variants tdefs (filter_extra pss)
      | constrs ->
          soit rec try_non_omega = fonction
              (p,pss) :: rem ->
                soit ok = pressure_variants tdefs pss dans
                try_non_omega rem && ok
            | [] -> vrai
          dans
          si full_match vrai (tdefs=None) constrs alors
            try_non_omega constrs
          sinon si tdefs = None alors
            pressure_variants None (filter_extra pss)
          sinon
            soit full = full_match vrai vrai constrs dans
            soit ok =
              si full alors try_non_omega constrs
              sinon try_non_omega (filter_all q0 (mark_partial pss))
            dans
            début filtre constrs, tdefs avec
              ({pat_desc=Tpat_variant _} tel p,_):: _, Some env ->
                soit row = row_of_pat p dans
                si Btype.row_fixed row
                || pressure_variants None (filter_extra pss) alors ()
                sinon close_variant env row
            | _ -> ()
            fin;
            ok
      fin


(* Yet another satisfiable fonction *)

(*
   This time every_satisfiable pss qs checks the
   utility of every expansion of qs.
   Expansion means expansion of or-patterns inside qs
*)

type answer =
  | Used                                (* Useful pattern *)
  | Unused                              (* Useless pattern *)
  | Upartial de Typedtree.pattern list  (* Mixed, with list of useless ones *)



(* this row type enable column processing inside the matrix
    - left  ->  elements not to be processed,
    - right ->  elements to be processed
*)
type 'a row = {no_ors : 'a list ; ors : 'a list ; active : 'a list}


soit pretty_row {ors=ors ; no_ors=no_ors; active=active} =
  pretty_line ors ; prerr_string " *" ;
  pretty_line no_ors ; prerr_string " *" ;
  pretty_line active

soit pretty_rows rs =
  prerr_endline "début matrice" ;
  List.iter
    (fonc r ->
      pretty_row r ;
      prerr_endline "")
    rs ;
  prerr_endline "fin matrice"

(* Initial build *)
soit make_row ps = {ors=[] ; no_ors=[]; active=ps}

soit make_rows pss = List.map make_row pss


(* Useful to detect and expand  or pats inside as pats *)
soit rec unalias p = filtre p.pat_desc avec
| Tpat_alias (p,_,_) -> unalias p
| _ -> p


soit is_var p = filtre (unalias p).pat_desc avec
| Tpat_any|Tpat_var _ -> vrai
| _                   -> faux

soit is_var_column rs =
  List.for_all
    (fonc r -> filtre r.active avec
    | p::_ -> is_var p
    | []   -> affirme faux)
    rs

(* Standard or-args for left-to-right matching *)
soit rec or_args p = filtre p.pat_desc avec
| Tpat_or (p1,p2,_) -> p1,p2
| Tpat_alias (p,_,_)  -> or_args p
| _                 -> affirme faux

(* Just remove current column *)
soit remove r = filtre r.active avec
| _::rem -> {r avec active=rem}
| []     -> affirme faux

soit remove_column rs = List.map remove rs

(* Current column has been processed *)
soit push_no_or r = filtre r.active avec
| p::rem -> { r avec no_ors = p::r.no_ors ; active=rem}
| [] -> affirme faux

soit push_or r = filtre r.active avec
| p::rem -> { r avec ors = p::r.ors ; active=rem}
| [] -> affirme faux

soit push_or_column rs = List.map push_or rs
et push_no_or_column rs = List.map push_no_or rs

(* Those are adaptations of the previous homonymous functions that
   work on the current column, instead of the first column
*)

soit discr_pat q rs =
  discr_pat q (List.map (fonc r -> r.active) rs)

soit filter_one q rs =
  soit rec filter_rec rs = filtre rs avec
  | [] -> []
  | r::rem ->
      filtre r.active avec
      | [] -> affirme faux
      | {pat_desc = Tpat_alias(p,_,_)}::ps ->
          filter_rec ({r avec active = p::ps}::rem)
      | {pat_desc = Tpat_or(p1,p2,_)}::ps ->
          filter_rec
            ({r avec active = p1::ps}::
             {r avec active = p2::ps}::
             rem)
      | p::ps ->
          si simple_match q p alors
            {r avec active=simple_match_args q p @ ps} :: filter_rec rem
          sinon
            filter_rec rem dans
  filter_rec rs


(* Back to normal matrices *)
soit make_vector r = r.no_ors

soit make_matrix rs = List.map make_vector rs


(* Standard union on answers *)
soit union_res r1 r2 = filtre r1, r2 avec
| (Unused,_)
| (_, Unused) -> Unused
| Used,_    -> r2
| _, Used   -> r1
| Upartial u1, Upartial u2 -> Upartial (u1@u2)

(* propose or pats for expansion *)
soit extract_elements qs =
  soit rec do_rec seen = fonction
    | [] -> []
    | q::rem ->
        {no_ors= List.rev_append seen rem @ qs.no_ors ;
        ors=[] ;
        active = [q]}::
        do_rec (q::seen) rem dans
  do_rec [] qs.ors

(* idem for matrices *)
soit transpose rs = filtre rs avec
| [] -> affirme faux
| r::rem ->
    soit i = List.map (fonc x -> [x]) r dans
    List.fold_left
      (List.map2 (fonc r x -> x::r))
      i rem

soit extract_columns pss qs = filtre pss avec
| [] -> List.map (fonc _ -> []) qs.ors
| _  ->
  soit rows = List.map extract_elements pss dans
  transpose rows

(* Core function
   The idea is to first look for or patterns (recursive case), then
   check or-patterns argument usefulness (terminal case)
*)

soit rec every_satisfiables pss qs = filtre qs.active avec
| []     ->
    (* qs is now partitionned,  check usefulness *)
    début filtre qs.ors avec
    | [] -> (* no or-patterns *)
        si satisfiable (make_matrix pss) (make_vector qs) alors
          Used
        sinon
          Unused
    | _  -> (* n or-patterns -> 2n expansions *)
        List.fold_right2
          (fonc pss qs r -> filtre r avec
          | Unused -> Unused
          | _ ->
              filtre qs.active avec
              | [q] ->
                  soit q1,q2 = or_args q dans
                  soit r_loc = every_both pss qs q1 q2 dans
                  union_res r r_loc
              | _   -> affirme faux)
          (extract_columns pss qs) (extract_elements qs)
          Used
    fin
| q::rem ->
    soit uq = unalias q dans
    début filtre uq.pat_desc avec
    | Tpat_any | Tpat_var _ ->
        si is_var_column pss alors
(* forget about ``all-variable''  columns now *)
          every_satisfiables (remove_column pss) (remove qs)
        sinon
(* otherwise this is direct food for satisfiable *)
          every_satisfiables (push_no_or_column pss) (push_no_or qs)
    | Tpat_or (q1,q2,_) ->
        si
          q1.pat_loc.Location.loc_ghost &&
          q2.pat_loc.Location.loc_ghost
        alors
(* syntactically generated or-pats should not be expanded *)
          every_satisfiables (push_no_or_column pss) (push_no_or qs)
        sinon
(* this is a real or-pattern *)
          every_satisfiables (push_or_column pss) (push_or qs)
    | Tpat_variant (l,_,r) quand is_absent l r -> (* Ah Jacques... *)
        Unused
    | _ ->
(* standard case, filter matrix *)
        soit q0 = discr_pat q pss dans
        every_satisfiables
          (filter_one q0 pss)
          {qs avec active=simple_match_args q0 q @ rem}
    fin

(*
  This function ``every_both'' performs the usefulness check
  of or-pat q1|q2.
  The trick is to call every_satisfied twice with
  current active columns restricted to q1 and q2,
  That way,
  - others orpats in qs.ors will not get expanded.
  - all matching work performed on qs.no_ors is not performed again.
  *)
et every_both pss qs q1 q2 =
  soit qs1 = {qs avec active=[q1]}
  et qs2 =  {qs avec active=[q2]} dans
  soit r1 = every_satisfiables pss qs1
  et r2 =  every_satisfiables (si compat q1 q2 alors qs1::pss sinon pss) qs2 dans
  filtre r1 avec
  | Unused ->
      début filtre r2 avec
      | Unused -> Unused
      | Used   -> Upartial [q1]
      | Upartial u2 -> Upartial (q1::u2)
      fin
  | Used ->
      début filtre r2 avec
      | Unused -> Upartial [q2]
      | _      -> r2
      fin
  | Upartial u1 ->
      début filtre r2 avec
      | Unused -> Upartial (u1@[q2])
      | Used   -> r1
      | Upartial u2 -> Upartial (u1 @ u2)
      fin




(* le_pat p q  means, forall V,  V matches q implies V matches p *)
soit rec le_pat p q =
  filtre (p.pat_desc, q.pat_desc) avec
  | (Tpat_var _|Tpat_any),_ -> vrai
  | Tpat_alias(p,_,_), _ -> le_pat p q
  | _, Tpat_alias(q,_,_) -> le_pat p q
  | Tpat_constant(c1), Tpat_constant(c2) -> const_compare c1 c2 = 0
  | Tpat_construct(_,c1,ps), Tpat_construct(_,c2,qs) ->
      c1.cstr_tag = c2.cstr_tag && le_pats ps qs
  | Tpat_variant(l1,Some p1,_), Tpat_variant(l2,Some p2,_) ->
      (l1 = l2 && le_pat p1 p2)
  | Tpat_variant(l1,None,r1), Tpat_variant(l2,None,_) ->
      l1 = l2
  | Tpat_variant(_,_,_), Tpat_variant(_,_,_) -> faux
  | Tpat_tuple(ps), Tpat_tuple(qs) -> le_pats ps qs
  | Tpat_lazy p, Tpat_lazy q -> le_pat p q
  | Tpat_record (l1,_), Tpat_record (l2,_) ->
      soit ps,qs = records_args l1 l2 dans
      le_pats ps qs
  | Tpat_array(ps), Tpat_array(qs) ->
      List.length ps = List.length qs && le_pats ps qs
(* In all other cases, enumeration is performed *)
  | _,_  -> not (satisfiable [[p]] [q])

et le_pats ps qs =
  filtre ps,qs avec
    p::ps, q::qs -> le_pat p q && le_pats ps qs
  | _, _         -> vrai

soit get_mins le ps =
  soit rec select_rec r = fonction
      [] -> r
    | p::ps ->
        si List.exists (fonc p0 -> le p0 p) ps
        alors select_rec r ps
        sinon select_rec (p::r) ps dans
  select_rec [] (select_rec [] ps)

(*
  lub p q is a pattern that matches all values matched by p and q
  may raise Empty, when p and q and not compatible
*)

soit rec lub p q = filtre p.pat_desc,q.pat_desc avec
| Tpat_alias (p,_,_),_      -> lub p q
| _,Tpat_alias (q,_,_)      -> lub p q
| (Tpat_any|Tpat_var _),_ -> q
| _,(Tpat_any|Tpat_var _) -> p
| Tpat_or (p1,p2,_),_     -> orlub p1 p2 q
| _,Tpat_or (q1,q2,_)     -> orlub q1 q2 p (* Thanks god, lub is commutative *)
| Tpat_constant c1, Tpat_constant c2 quand const_compare c1 c2 = 0 -> p
| Tpat_tuple ps, Tpat_tuple qs ->
    soit rs = lubs ps qs dans
    make_pat (Tpat_tuple rs) p.pat_type p.pat_env
| Tpat_lazy p, Tpat_lazy q ->
    soit r = lub p q dans
    make_pat (Tpat_lazy r) p.pat_type p.pat_env
| Tpat_construct (lid, c1,ps1), Tpat_construct (_,c2,ps2)
      quand  c1.cstr_tag = c2.cstr_tag  ->
        soit rs = lubs ps1 ps2 dans
        make_pat (Tpat_construct (lid, c1,rs))
          p.pat_type p.pat_env
| Tpat_variant(l1,Some p1,row), Tpat_variant(l2,Some p2,_)
          quand  l1=l2 ->
            soit r=lub p1 p2 dans
            make_pat (Tpat_variant (l1,Some r,row)) p.pat_type p.pat_env
| Tpat_variant (l1,None,row), Tpat_variant(l2,None,_)
              quand l1 = l2 -> p
| Tpat_record (l1,closed),Tpat_record (l2,_) ->
    soit rs = record_lubs l1 l2 dans
    make_pat (Tpat_record (rs, closed)) p.pat_type p.pat_env
| Tpat_array ps, Tpat_array qs
      quand List.length ps = List.length qs ->
        soit rs = lubs ps qs dans
        make_pat (Tpat_array rs) p.pat_type p.pat_env
| _,_  ->
    raise Empty

et orlub p1 p2 q =
  essaie
    soit r1 = lub p1 q dans
    essaie
      {q avec pat_desc=(Tpat_or (r1,lub p2 q,None))}
  avec
  | Empty -> r1
avec
| Empty -> lub p2 q

et record_lubs l1 l2 =
  soit rec lub_rec l1 l2 = filtre l1,l2 avec
  | [],_ -> l2
  | _,[] -> l1
  | (lid1, lbl1,p1)::rem1, (lid2, lbl2,p2)::rem2 ->
      si lbl1.lbl_pos < lbl2.lbl_pos alors
        (lid1, lbl1,p1)::lub_rec rem1 l2
      sinon si lbl2.lbl_pos < lbl1.lbl_pos  alors
        (lid2, lbl2,p2)::lub_rec l1 rem2
      sinon
        (lid1, lbl1,lub p1 p2)::lub_rec rem1 rem2 dans
  lub_rec l1 l2

et lubs ps qs = filtre ps,qs avec
| p::ps, q::qs -> lub p q :: lubs ps qs
| _,_ -> []


(******************************)
(* Exported variant closing   *)
(******************************)

(* Apply pressure to variants *)

soit pressure_variants tdefs patl =
  soit pss = List.map (fonc p -> [p;omega]) patl dans
  ignore (pressure_variants (Some tdefs) pss)

(*****************************)
(* Utilities for diagnostics *)
(*****************************)

(*
  Build up a working pattern matrix by forgetting
  about guarded patterns
*)

soit rec initial_matrix = fonction
    [] -> []
  | {c_guard=Some _} :: rem -> initial_matrix rem
  | {c_guard=None; c_lhs=p} :: rem -> [p] :: initial_matrix rem

(******************************************)
(* Look for a row that matches some value *)
(******************************************)

(*
  Useful for seeing if the example of
  non-matched value can indeed be matched
  (by a guarded clause)
*)



exception NoGuard

soit rec initial_all no_guard = fonction
  | [] ->
      si no_guard alors
        raise NoGuard
      sinon
        []
  | {c_lhs=pat; c_guard; _} :: rem ->
      ([pat], pat.pat_loc) :: initial_all (no_guard && c_guard = None) rem


soit rec do_filter_var = fonction
  | (_::ps,loc)::rem -> (ps,loc)::do_filter_var rem
  | _ -> []

soit do_filter_one q pss =
  soit rec filter_rec = fonction
    | ({pat_desc = Tpat_alias(p,_,_)}::ps,loc)::pss ->
        filter_rec ((p::ps,loc)::pss)
    | ({pat_desc = Tpat_or(p1,p2,_)}::ps,loc)::pss ->
        filter_rec ((p1::ps,loc)::(p2::ps,loc)::pss)
    | (p::ps,loc)::pss ->
        si simple_match q p
        alors (simple_match_args q p @ ps, loc) :: filter_rec pss
        sinon filter_rec pss
    | _ -> [] dans
  filter_rec pss

soit rec do_match pss qs = filtre qs avec
| [] ->
    début filtre pss  avec
    | ([],loc)::_ -> Some loc
    | _ -> None
    fin
| q::qs -> filtre q avec
  | {pat_desc = Tpat_or (q1,q2,_)} ->
      début filtre do_match pss (q1::qs) avec
      | None -> do_match pss (q2::qs)
      | r -> r
      fin
  | {pat_desc = Tpat_any} ->
      do_match (do_filter_var pss) qs
  | _ ->
      soit q0 = normalize_pat q dans
      do_match (do_filter_one q0 pss) (simple_match_args q0 q @ qs)


soit check_partial_all v casel =
  essaie
    soit pss = initial_all vrai casel dans
    do_match pss [v]
  avec
  | NoGuard -> None

(************************)
(* Exhaustiveness check *)
(************************)


  soit rec get_first f =
    fonction
      | [] -> None
      | x :: xs ->
          filtre f x avec
          | None -> get_first f xs
          | x -> x


(* conversion from Typedtree.pattern to Parsetree.pattern list *)
module Conv = struct
  ouvre Parsetree
  soit mkpat desc = Ast_helper.Pat.mk desc

  soit rec select : 'a list list -> 'a list list =
    fonction
      | xs :: [] -> List.map (fonc y -> [y]) xs
      | (x::xs)::ys ->
          List.map
            (fonc lst -> x :: lst)
            (select ys)
          @
            select (xs::ys)
      | _ -> []

  soit name_counter = ref 0
  soit fresh name =
    soit current = !name_counter dans
    name_counter := !name_counter + 1;
    "#$" ^ name ^ string_of_int current

  soit conv (typed: Typedtree.pattern) :
      Parsetree.pattern list *
      (string, Types.constructor_description) Hashtbl.t *
      (string, Types.label_description) Hashtbl.t
      =
    soit constrs = Hashtbl.create 0 dans
    soit labels = Hashtbl.create 0 dans
    soit rec loop pat =
      filtre pat.pat_desc avec
        Tpat_or (a,b,_) ->
          loop a @ loop b
      | Tpat_any | Tpat_constant _ | Tpat_var _ ->
          [mkpat Ppat_any]
      | Tpat_alias (p,_,_) -> loop p
      | Tpat_tuple lst ->
          soit results = select (List.map loop lst) dans
          List.map
            (fonc lst -> mkpat (Ppat_tuple lst))
            results
      | Tpat_construct (cstr_lid, cstr,lst) ->
          soit id = fresh cstr.cstr_name dans
          soit lid = { cstr_lid avec txt = Longident.Lident id } dans
          Hashtbl.add constrs id cstr;
          soit results = select (List.map loop lst) dans
          début filtre lst avec
            [] ->
              [mkpat (Ppat_construct(lid, None))]
          | _ ->
              List.map
                (fonc lst ->
                  soit arg =
                    filtre lst avec
                      [] -> affirme faux
                    | [x] -> Some x
                    | _ -> Some (mkpat (Ppat_tuple lst))
                  dans
                  mkpat (Ppat_construct(lid, arg)))
                results
          fin
      | Tpat_variant(label,p_opt,row_desc) ->
          début filtre p_opt avec
          | None ->
              [mkpat (Ppat_variant(label, None))]
          | Some p ->
              soit results = loop p dans
              List.map
                (fonc p ->
                  mkpat (Ppat_variant(label, Some p)))
                results
          fin
      | Tpat_record (subpatterns, _closed_flag) ->
          soit pats =
            select
              (List.map (fonc (_,_,x) -> loop x) subpatterns)
          dans
          soit label_idents =
            List.map
              (fonc (_,lbl,_) ->
                soit id = fresh lbl.lbl_name dans
                Hashtbl.add labels id lbl;
                Longident.Lident id)
              subpatterns
          dans
          List.map
            (fonc lst ->
              soit lst = List.map2 (fonc lid pat ->
                (mknoloc lid, pat)
              )  label_idents lst dans
              mkpat (Ppat_record (lst, Open)))
            pats
      | Tpat_array lst ->
          soit results = select (List.map loop lst) dans
          List.map (fonc lst -> mkpat (Ppat_array lst)) results
      | Tpat_lazy p ->
          soit results = loop p dans
          List.map (fonc p -> mkpat (Ppat_lazy p)) results
    dans
    soit ps = loop typed dans
    (ps, constrs, labels)
fin


soit do_check_partial ?pred exhaust loc casel pss = filtre pss avec
| [] ->
        (*
          This can occur
          - For empty matches generated by ocamlp4 (no warning)
          - when all patterns have guards (then, casel <> [])
          (specific warning)
          Then match MUST be considered non-exhaustive,
          otherwise compilation of PM is broken.
          *)
    début filtre casel avec
    | [] -> ()
    | _  -> Location.prerr_warning loc Warnings.All_clauses_guarded
    fin ;
    Partial
| ps::_  ->
    début filtre exhaust None pss (List.length ps) avec
    | Rnone -> Total
    | Rsome [u] ->
        soit v =
          filtre pred avec
          | Some pred ->
              soit (patterns,constrs,labels) = Conv.conv u dans
(*              Hashtbl.iter (fun s (path, _) ->
                Printf.fprintf stderr "CONV: %s -> %s \n%!" s (Path.name path))
                constrs
              ; *)
              get_first (pred constrs labels) patterns
          | None -> Some u
        dans
        début filtre v avec
          None -> Total
        | Some v ->
            soit errmsg =
              essaie
                soit buf = Buffer.create 16 dans
                soit fmt = formatter_of_buffer buf dans
                top_pretty fmt v;
                début filtre check_partial_all v casel avec
                | None -> ()
                | Some _ ->
                    (* This is 'Some loc', where loc is the location of
                       a possibly matching clause.
                       Forget about loc, because printing two locations
                       is a pain in the top-level *)
                    Buffer.add_string buf
                      "\n(Cependant, des clauses gardées peuvent filtrer cette valeur.)"
                fin ;
                Buffer.contents buf
              avec _ ->
                "" dans
            Location.prerr_warning loc (Warnings.Partial_match errmsg) ;
            Partial fin
    | _ ->
        fatal_error "Parmatch.check_partial"
    fin

soit do_check_partial_normal loc casel pss =
  do_check_partial exhaust loc casel pss

soit do_check_partial_gadt pred loc casel pss =
  do_check_partial ~pred exhaust_gadt loc casel pss



(*****************)
(* Fragile check *)
(*****************)

(* Collect all data types in a pattern *)

soit rec add_path path = fonction
  | [] -> [path]
  | x::rem tel paths ->
      si Path.same path x alors paths
      sinon x::add_path path rem

soit extendable_path path =
  not
    (Path.same path Predef.path_bool ||
    Path.same path Predef.path_list ||
    Path.same path Predef.path_unit ||
    Path.same path Predef.path_option)

soit rec collect_paths_from_pat r p = filtre p.pat_desc avec
| Tpat_construct(_, {cstr_tag=(Cstr_constant _|Cstr_block _)},ps) ->
    soit path =  get_type_path p.pat_type p.pat_env dans
    List.fold_left
      collect_paths_from_pat
      (si extendable_path path alors add_path path r sinon r)
      ps
| Tpat_any|Tpat_var _|Tpat_constant _| Tpat_variant (_,None,_) -> r
| Tpat_tuple ps | Tpat_array ps
| Tpat_construct (_, {cstr_tag=Cstr_exception _}, ps)->
    List.fold_left collect_paths_from_pat r ps
| Tpat_record (lps,_) ->
    List.fold_left
      (fonc r (_, _, p) -> collect_paths_from_pat r p)
      r lps
| Tpat_variant (_, Some p, _) | Tpat_alias (p,_,_) -> collect_paths_from_pat r p
| Tpat_or (p1,p2,_) ->
    collect_paths_from_pat (collect_paths_from_pat r p1) p2
| Tpat_lazy p
    ->
    collect_paths_from_pat r p


(*
  Actual fragile check
   1. Collect data types in the patterns of the match.
   2. One exhautivity check per datatype, considering that
      the type is extended.
*)

soit do_check_fragile_param exhaust loc casel pss =
  soit exts =
    List.fold_left
      (fonc r c -> collect_paths_from_pat r c.c_lhs)
      [] casel dans
  filtre exts avec
  | [] -> ()
  | _ -> filtre pss avec
    | [] -> ()
    | ps::_ ->
        List.iter
          (fonc ext ->
            filtre exhaust (Some ext) pss (List.length ps) avec
            | Rnone ->
                Location.prerr_warning
                  loc
                  (Warnings.Fragile_match (Path.name ext))
            | Rsome _ -> ())
          exts

soit do_check_fragile_normal = do_check_fragile_param exhaust
soit do_check_fragile_gadt = do_check_fragile_param exhaust_gadt

(********************************)
(* Exported unused clause check *)
(********************************)

soit check_unused tdefs casel =
  si Warnings.is_active Warnings.Unused_match alors
    soit rec do_rec pref = fonction
      | [] -> ()
      | {c_lhs=q; c_guard} :: rem ->
          soit qs = [q] dans
            début essaie
              soit pss =
                  get_mins le_pats (List.filter (compats qs) pref) dans
              soit r = every_satisfiables (make_rows pss) (make_row qs) dans
              filtre r avec
              | Unused ->
                  Location.prerr_warning
                    q.pat_loc Warnings.Unused_match
              | Upartial ps ->
                  List.iter
                    (fonc p ->
                      Location.prerr_warning
                        p.pat_loc Warnings.Unused_pat)
                    ps
              | Used -> ()
            avec Empty | Not_an_adt | Not_found | NoGuard -> affirme faux
            fin ;

          si c_guard <> None alors
            do_rec pref rem
          sinon
            do_rec ([q]::pref) rem dans

    do_rec [] casel

(*********************************)
(* Exported irrefutability tests *)
(*********************************)

soit irrefutable pat = le_pat pat omega

(* An inactive pattern is a pattern whose matching needs only
   trivial computations (tag/equality tests).
   Patterns containing (lazy _) subpatterns are active. *)

soit rec inactive pat = filtre pat avec
| Tpat_lazy _ ->
    faux
| Tpat_any | Tpat_var _ | Tpat_constant _ | Tpat_variant (_, None, _) ->
    vrai
| Tpat_tuple ps | Tpat_construct (_, _, ps) | Tpat_array ps ->
    List.for_all (fonc p -> inactive p.pat_desc) ps
| Tpat_alias (p,_,_) | Tpat_variant (_, Some p, _) ->
    inactive p.pat_desc
| Tpat_record (ldps,_) ->
    List.exists (fonc (_, _, p) -> inactive p.pat_desc) ldps
| Tpat_or (p,q,_) ->
    inactive p.pat_desc && inactive q.pat_desc

(* A `fluid' pattern is both irrefutable and inactive *)

soit fluid pat =  irrefutable pat && inactive pat.pat_desc








(********************************)
(* Exported exhustiveness check *)
(********************************)

(*
   Fragile check is performed when required and
   on exhaustive matches only.
*)

soit check_partial_param do_check_partial do_check_fragile loc casel =
    si Warnings.is_active (Warnings.Partial_match "") alors début
      soit pss = initial_matrix casel dans
      soit pss = get_mins le_pats pss dans
      soit total = do_check_partial loc casel pss dans
      si
        total = Total && Warnings.is_active (Warnings.Fragile_match "")
      alors début
        do_check_fragile loc casel pss
      fin ;
      total
    fin sinon
      Partial

soit check_partial =
    check_partial_param
      do_check_partial_normal
      do_check_fragile_normal

soit check_partial_gadt pred loc casel =
  (*ignores GADT constructors *)
  soit first_check = check_partial loc casel dans
  filtre first_check avec
  | Partial -> Partial
  | Total ->
      (* checks for missing GADT constructors *)
      (* let casel =
        match casel with [] -> [] | a :: l -> a :: l @ [a] in *)
      check_partial_param (do_check_partial_gadt pred)
        do_check_fragile_gadt loc casel
