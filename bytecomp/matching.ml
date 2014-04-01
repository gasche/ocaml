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

(* Compilation of pattern matching *)

ouvre Misc
ouvre Asttypes
ouvre Primitive
ouvre Types
ouvre Typedtree
ouvre Lambda
ouvre Parmatch
ouvre Printf

soit dbg = faux

(*  See Peyton-Jones, ``The Implementation of functional programming
    languages'', chapter 5. *)
(*
  Bon, au commencement du monde c'etait vrai.
  Now, see Lefessant-Maranget ``Optimizing Pattern-Matching'' ICFP'2001
*)


(*
   Many functions on the various data structures of the algorithm :
     - Pattern matrices.
     - Default environments: mapping from matrices to exit numbers.
     - Contexts:  matrices whose column are partitioned into
       left and right.
     - Jump summaries: mapping from exit numbers to contexts
*)

type matrix = pattern list list

soit add_omega_column pss = List.map (fonc ps -> omega::ps) pss

type ctx = {left:pattern list ; right:pattern list}

soit pretty_ctx ctx =
  List.iter
    (fonc {left=left ; right=right} ->
      prerr_string "LEFT:" ;
      pretty_line left ;
      prerr_string " RIGHT:" ;
      pretty_line right ;
      prerr_endline "")
    ctx

soit le_ctx c1 c2 =
  le_pats c1.left c2.left &&
  le_pats c1.right c2.right

soit lshift {left=left ; right=right} = filtre right avec
| x::xs -> {left=x::left ; right=xs}
| _ ->  affirme faux

soit lforget {left=left ; right=right} = filtre right avec
| x::xs -> {left=omega::left ; right=xs}
|  _ -> affirme faux

soit rec small_enough n = fonction
  | [] -> vrai
  | _::rem ->
      si n <= 0 alors faux
      sinon small_enough (n-1) rem

soit ctx_lshift ctx =
  si small_enough 31 ctx alors
    List.map lshift ctx
  sinon (* Context pruning *) début
    get_mins le_ctx (List.map lforget ctx)
  fin

soit  rshift {left=left ; right=right} = filtre left avec
| p::ps -> {left=ps ; right=p::right}
| _ -> affirme faux

soit ctx_rshift ctx = List.map rshift ctx

soit rec nchars n ps =
  si n <= 0 alors [],ps
  sinon filtre ps avec
  | p::rem ->
    soit chars, cdrs = nchars (n-1) rem dans
    p::chars,cdrs
  | _ -> affirme faux

soit  rshift_num n {left=left ; right=right} =
  soit shifted,left = nchars n left dans
  {left=left ; right = shifted@right}

soit ctx_rshift_num n ctx = List.map (rshift_num n) ctx

(* Recombination of contexts (eg: (_,_)::p1::p2::rem ->  (p1,p2)::rem)
  All mutable fields are replaced by '_', since side-effects in
  guards can alter these fields *)

soit combine {left=left ; right=right} = filtre left avec
| p::ps -> {left=ps ; right=set_args_erase_mutable p right}
| _ -> affirme faux

soit ctx_combine ctx = List.map combine ctx

soit ncols = fonction
  | [] -> 0
  | ps::_ -> List.length ps


exception NoMatch
exception OrPat

soit filter_matrix matcher pss =

  soit rec filter_rec = fonction
    | (p::ps)::rem ->
        début filtre p.pat_desc avec
        | Tpat_alias (p,_,_) ->
            filter_rec ((p::ps)::rem)
        | Tpat_var _ ->
            filter_rec ((omega::ps)::rem)
        | _ ->
            début
              soit rem = filter_rec rem dans
              essaie
                matcher p ps::rem
              avec
              | NoMatch -> rem
              | OrPat   ->
                filtre p.pat_desc avec
                | Tpat_or (p1,p2,_) -> filter_rec [(p1::ps) ;(p2::ps)]@rem
                | _ -> affirme faux
            fin
        fin
    | [] -> []
    | _ ->
        pretty_matrix pss ;
        fatal_error "Matching.filter_matrix" dans
  filter_rec pss

soit make_default matcher env =
  soit rec make_rec = fonction
    | [] -> []
    | ([[]],i)::_ -> [[[]],i]
    | (pss,i)::rem ->
        soit rem = make_rec rem dans
        filtre filter_matrix matcher pss avec
        | [] -> rem
        | ([]::_) -> ([[]],i)::rem
        | pss -> (pss,i)::rem dans
  make_rec env

soit ctx_matcher p =
  soit p = normalize_pat p dans
  filtre p.pat_desc avec
  | Tpat_construct (_, cstr,omegas) ->
      début filtre cstr.cstr_tag avec
      | Cstr_exception _ -> (* exception matching *)
          soit nargs = List.length omegas dans
          (fonc q rem -> filtre q.pat_desc avec
          | Tpat_construct (_, cstr',args)
            quand List.length args = nargs ->
                p,args @ rem
          | Tpat_any -> p,omegas @ rem
          | _ -> raise NoMatch)
      | _ ->
          (fonc q rem -> filtre q.pat_desc avec
          | Tpat_construct (_, cstr',args)
            quand cstr.cstr_tag=cstr'.cstr_tag ->
              p,args @ rem
          | Tpat_any -> p,omegas @ rem
          | _ -> raise NoMatch)
      fin
  | Tpat_constant cst ->
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_constant cst' quand const_compare cst cst' = 0 ->
          p,rem
      | Tpat_any -> p,rem
      | _ -> raise NoMatch)
  | Tpat_variant (lab,Some omega,_) ->
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_variant (lab',Some arg,_) quand lab=lab' ->
          p,arg::rem
      | Tpat_any -> p,omega::rem
      | _ -> raise NoMatch)
  | Tpat_variant (lab,None,_) ->
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_variant (lab',None,_) quand lab=lab' ->
          p,rem
      | Tpat_any -> p,rem
      | _ -> raise NoMatch)
  | Tpat_array omegas ->
      soit len = List.length omegas dans
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_array args quand List.length args=len ->
          p,args @ rem
      | Tpat_any -> p, omegas @ rem
      | _ -> raise NoMatch)
  | Tpat_tuple omegas ->
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_tuple args -> p,args @ rem
      | _          -> p, omegas @ rem)
  | Tpat_record (l,_) -> (* Records are normalized *)
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_record (l',_) ->
          soit l' = all_record_args l' dans
          p, List.fold_right (fonc (_, _,p) r -> p::r) l' rem
      | _ -> p,List.fold_right (fonc (_, _,p) r -> p::r) l rem)
  | Tpat_lazy omega ->
      (fonc q rem -> filtre q.pat_desc avec
      | Tpat_lazy arg -> p, (arg::rem)
      | _          -> p, (omega::rem))
 | _ -> fatal_error "Matching.ctx_matcher"




soit filter_ctx q ctx =

  soit matcher = ctx_matcher q dans

  soit rec filter_rec = fonction
    | ({right=p::ps} tel l)::rem ->
        début filtre p.pat_desc avec
        | Tpat_or (p1,p2,_) ->
            filter_rec ({l avec right=p1::ps}::{l avec right=p2::ps}::rem)
        | Tpat_alias (p,_,_) ->
            filter_rec ({l avec right=p::ps}::rem)
        | Tpat_var _ ->
            filter_rec ({l avec right=omega::ps}::rem)
        | _ ->
            début soit rem = filter_rec rem dans
            essaie
              soit to_left, right = matcher p ps dans
              {left=to_left::l.left ; right=right}::rem
            avec
            | NoMatch -> rem
            fin
        fin
    | [] -> []
    | _ ->  fatal_error "Matching.filter_ctx" dans

  filter_rec ctx

soit select_columns pss ctx =
  soit n = ncols pss dans
  List.fold_right
    (fonc ps r ->
      List.fold_right
        (fonc {left=left ; right=right} r ->
          soit transfert, right = nchars n right dans
          essaie
            {left = lubs transfert ps @ left ; right=right}::r
          avec
          | Empty -> r)
        ctx r)
    pss []

soit ctx_lub p ctx =
  List.fold_right
    (fonc {left=left ; right=right} r ->
      filtre right avec
      | q::rem ->
          début essaie
            {left=left ; right = lub p q::rem}::r
          avec
          | Empty -> r
          fin
      | _ -> fatal_error "Matching.ctx_lub")
    ctx []

soit ctx_match ctx pss =
  List.exists
    (fonc {right=qs} ->
      List.exists
        (fonc ps -> compats qs ps)
        pss)
    ctx

type jumps = (int * ctx list) list

soit pretty_jumps (env : jumps) = filtre env avec
| [] -> ()
| _ ->
    List.iter
      (fonc (i,ctx) ->
        Printf.fprintf stderr "jump for %d\n" i ;
        pretty_ctx ctx)
      env


soit rec jumps_extract i = fonction
  | [] -> [],[]
  | (j,pss) tel x::rem tel all ->
      si i=j alors pss,rem
      sinon si j < i alors [],all
      sinon
        soit r,rem = jumps_extract i rem dans
        r,(x::rem)

soit rec jumps_remove i = fonction
  | [] -> []
  | (j,_)::rem quand i=j -> rem
  | x::rem -> x::jumps_remove i rem

soit jumps_empty = []
et jumps_is_empty = fonction
  |  [] -> vrai
  |  _ -> faux

soit jumps_singleton i = fonction
  | []  -> []
  | ctx ->  [i,ctx]

soit jumps_add i pss jumps = filtre pss avec
| [] -> jumps
| _  ->
    soit rec add = fonction
      | [] -> [i,pss]
      | (j,qss) tel x::rem tel all ->
          si j > i alors x::add rem
      sinon si j < i alors (i,pss)::all
      sinon (i,(get_mins le_ctx (pss@qss)))::rem dans
    add jumps


soit rec jumps_union (env1:(int*ctx list)list) env2 = filtre env1,env2 avec
| [],_ -> env2
| _,[] -> env1
| ((i1,pss1) tel x1::rem1), ((i2,pss2) tel x2::rem2) ->
    si i1=i2 alors
      (i1,get_mins le_ctx (pss1@pss2))::jumps_union rem1 rem2
    sinon si i1 > i2 alors
      x1::jumps_union rem1 env2
    sinon
      x2::jumps_union env1 rem2


soit rec merge = fonction
  | env1::env2::rem ->  jumps_union env1 env2::merge rem
  | envs -> envs

soit rec jumps_unions envs = filtre envs avec
  | [] -> []
  | [env] -> env
  | _ -> jumps_unions (merge envs)

soit jumps_map f env =
  List.map
    (fonc (i,pss) -> i,f pss)
    env

(* Pattern matching before any compilation *)

type pattern_matching =
  { modifiable cases : (pattern list * lambda) list;
    args : (lambda * let_kind) list ;
    default : (matrix * int) list}

(* Pattern matching after application of both the or-pat rule and the
   mixture rule *)

type pm_or_compiled =
  {body : pattern_matching ;
   handlers : (matrix * int * Ident.t list * pattern_matching) list ;
   or_matrix : matrix ; }

type pm_half_compiled =
  | PmOr de pm_or_compiled
  | PmVar de pm_var_compiled
  | Pm de pattern_matching

et pm_var_compiled =
    {inside : pm_half_compiled ; var_arg : lambda ; }

type pm_half_compiled_info =
    {me : pm_half_compiled ;
     matrix : matrix ;
     top_default : (matrix * int) list ; }

soit pretty_cases cases =
  List.iter
    (fonc ((ps),l) ->
      List.iter
        (fonc p ->
          Parmatch.top_pretty Format.str_formatter p ;
          prerr_string " " ;
          prerr_string (Format.flush_str_formatter ()))
        ps ;
(*
      prerr_string " -> " ;
      Printlambda.lambda Format.str_formatter l ;
      prerr_string (Format.flush_str_formatter ()) ;
*)
      prerr_endline "")
    cases

soit pretty_def def =
  prerr_endline "+++++ Defaults +++++" ;
  List.iter
    (fonc (pss,i) ->
      Printf.fprintf stderr "Matrix for %d\n"  i ;
      pretty_matrix pss)
    def ;
  prerr_endline "+++++++++++++++++++++"

soit pretty_pm pm = pretty_cases pm.cases


soit rec pretty_precompiled = fonction
  | Pm pm ->
      prerr_endline "++++ PM ++++" ;
      pretty_pm pm
  | PmVar x ->
      prerr_endline "++++ VAR ++++" ;
      pretty_precompiled x.inside
  | PmOr x ->
      prerr_endline "++++ OR ++++" ;
      pretty_pm x.body ;
      pretty_matrix x.or_matrix ;
      List.iter
        (fonc (_,i,_,pm) ->
          eprintf "++ Handler %d ++\n" i ;
          pretty_pm pm)
        x.handlers

soit pretty_precompiled_res first nexts =
  pretty_precompiled first ;
  List.iter
    (fonc (e, pmh) ->
      eprintf "** DEFAULT %d **\n" e ;
      pretty_precompiled pmh)
    nexts



(* A slight attempt to identify semantically equivalent lambda-expressions,
   We could have used Lambda.same, but our goal here is also to
   find alpha-equivalent (simple) terms *)
exception Not_simple

soit rec raw_rec env : lambda -> lambda = fonction
  | Llet(Alias,x,ex, body) -> raw_rec ((x,raw_rec env ex)::env) body
  | Lvar id tel l ->
      début essaie List.assoc id env avec
      | Not_found -> l
      fin
  | Lprim (Pfield i,args) ->
      Lprim (Pfield i, List.map (raw_rec env) args)
  | Lconst  (Const_base (Const_string _)) ->
      raise Not_simple (* do not share strings *)
  | Lconst _ tel l -> l
  | Lstaticraise (i,args) ->
        Lstaticraise (i, List.map (raw_rec env) args)
  | _ -> raise Not_simple

soit raw_action l = essaie raw_rec [] l avec Not_simple -> l

soit same_actions = fonction
  | [] -> None
  | [_,act] -> Some act
  | (_,act0) :: rem ->
      essaie
        soit raw_act0 = raw_rec [] act0 dans
        soit rec s_rec = fonction
          | [] -> Some act0
          | (_,act)::rem ->
              si raw_act0 = raw_rec [] act alors
                s_rec rem
              sinon
                None dans
        s_rec rem
      avec
      | Not_simple -> None

soit equal_action act1 act2 =
  essaie
    soit raw1 = raw_rec [] act1
    et raw2 = raw_rec [] act2 dans
    raw1 = raw2
  avec
  | Not_simple -> faux

(* Test for swapping two clauses *)

soit up_ok_action act1 act2 =
  essaie
    soit raw1 = raw_rec [] act1
    et raw2 = raw_rec [] act2 dans
    filtre raw1, raw2 avec
    | Lstaticraise (i1,[]), Lstaticraise (i2,[]) -> i1=i2
    | _,_ -> raw1 = raw2
  avec
  | Not_simple -> faux

(* Nothing is kown about exeception patterns, because of potential rebind *)
soit rec exc_inside p = filtre p.pat_desc avec
  | Tpat_construct (_,{cstr_tag=Cstr_exception _},_) -> vrai
  | Tpat_any|Tpat_constant _|Tpat_var _
  | Tpat_construct (_,_,[])
  | Tpat_variant (_,None,_)
    -> faux
  | Tpat_construct (_,_,ps)
  | Tpat_tuple ps
  | Tpat_array ps
      -> exc_insides ps
  | Tpat_variant (_, Some q,_)
  | Tpat_alias (q,_,_)
  | Tpat_lazy q
    -> exc_inside q
  | Tpat_record (lps,_) ->
      List.exists (fonc (_,_,p) -> exc_inside p) lps
  | Tpat_or (p1,p2,_) -> exc_inside p1 || exc_inside p2

et exc_insides ps = List.exists exc_inside ps

soit up_ok (ps,act_p) l =
  si exc_insides ps alors filtre l avec [] -> vrai | _::_ -> faux
  sinon
    List.for_all
      (fonc (qs,act_q) ->
        up_ok_action act_p act_q ||
        not (Parmatch.compats ps qs))
      l


(*
   Simplify fonction normalize the first column of the match
     - records are expanded so that they posses all fields
     - aliases are removed and replaced by bindings in actions.
   However or-patterns are simplified differently,
     - aliases are not removed
     - or patterns (_|p) are changed into _
*)

exception Var de pattern

soit simplify_or p =
  soit rec simpl_rec p = filtre p avec
    | {pat_desc = Tpat_any|Tpat_var _} -> raise (Var p)
    | {pat_desc = Tpat_alias (q,id,s)} ->
        début essaie
          {p avec pat_desc = Tpat_alias (simpl_rec q,id,s)}
        avec
        | Var q -> raise (Var {p avec pat_desc = Tpat_alias (q,id,s)})
        fin
    | {pat_desc = Tpat_or (p1,p2,o)} ->
        soit q1 = simpl_rec p1 dans
        début essaie
          soit q2 = simpl_rec p2 dans
          {p avec pat_desc = Tpat_or (q1, q2, o)}
        avec
        | Var q2 -> raise (Var {p avec pat_desc = Tpat_or (q1, q2, o)})
        fin
    | {pat_desc = Tpat_record (lbls,closed)} ->
        soit all_lbls = all_record_args lbls dans
        {p avec pat_desc=Tpat_record (all_lbls, closed)}
    | _ -> p dans
  essaie
    simpl_rec p
  avec
  | Var p -> p

soit simplify_cases args cls = filtre args avec
| [] -> affirme faux
| (arg,_)::_ ->
    soit rec simplify = fonction
      | [] -> []
      | ((pat :: patl, action) tel cl) :: rem ->
          début filtre pat.pat_desc avec
          | Tpat_var (id, _) ->
              (omega :: patl, bind Alias id arg action) ::
              simplify rem
          | Tpat_any ->
              cl :: simplify rem
          | Tpat_alias(p, id,_) ->
              simplify ((p :: patl, bind Alias id arg action) :: rem)
          | Tpat_record ([],_) ->
              (omega :: patl, action)::
              simplify rem
          | Tpat_record (lbls, closed) ->
              soit all_lbls = all_record_args lbls dans
              soit full_pat =
                {pat avec pat_desc=Tpat_record (all_lbls, closed)} dans
              (full_pat::patl,action)::
              simplify rem
          | Tpat_or _ ->
              soit pat_simple  = simplify_or pat dans
              début filtre pat_simple.pat_desc avec
              | Tpat_or _ ->
                  (pat_simple :: patl, action) ::
                  simplify rem
              | _ ->
                  simplify ((pat_simple::patl,action) :: rem)
              fin
          | _ -> cl :: simplify rem
          fin
      | _ -> affirme faux dans

    simplify cls



(* Once matchings are simplified one easily finds
   their nature *)

soit rec what_is_cases cases = filtre cases avec
| ({pat_desc=Tpat_any} :: _, _) :: rem -> what_is_cases rem
| (({pat_desc=(Tpat_var _|Tpat_or (_,_,_)|Tpat_alias (_,_,_))}::_),_)::_
  -> affirme faux (* applies to simplified matchings only *)
| (p::_,_)::_ -> p
| [] -> omega
| _ -> affirme faux



(* A few operation on default environments *)
soit as_matrix cases = get_mins le_pats (List.map (fonc (ps,_) -> ps) cases)

(* For exception matching, record no imformation in matrix *)
soit as_matrix_omega cases =
  get_mins le_pats
    (List.map
       (fonc (ps,_) ->
         filtre ps avec
         | [] -> affirme faux
         | _::ps -> omega::ps)
       cases)

soit cons_default matrix raise_num default =
  filtre matrix avec
  | [] -> default
  | _ -> (matrix,raise_num)::default

soit default_compat p def =
  List.fold_right
    (fonc (pss,i) r ->
      soit qss =
        List.fold_right
          (fonc qs r -> filtre qs avec
            | q::rem quand Parmatch.compat p q -> rem::r
            | _ -> r)
          pss [] dans
      filtre qss avec
      | [] -> r
      | _  -> (qss,i)::r)
    def []

(* Or-pattern expansion, variables are a complication w.r.t. the article *)
soit rec extract_vars r p = filtre p.pat_desc avec
| Tpat_var (id, _) -> IdentSet.add id r
| Tpat_alias (p, id,_ ) ->
    extract_vars (IdentSet.add id r) p
| Tpat_tuple pats ->
    List.fold_left extract_vars r pats
| Tpat_record (lpats,_) ->
    List.fold_left
      (fonc r (_, _, p) -> extract_vars r p)
      r lpats
| Tpat_construct (_, _, pats) ->
    List.fold_left extract_vars r pats
| Tpat_array pats ->
    List.fold_left extract_vars r pats
| Tpat_variant (_,Some p, _) -> extract_vars r p
| Tpat_lazy p -> extract_vars r p
| Tpat_or (p,_,_) -> extract_vars r p
| Tpat_constant _|Tpat_any|Tpat_variant (_,None,_) -> r

exception Cannot_flatten

soit mk_alpha_env arg aliases ids =
  List.map
    (fonc id -> id,
      si List.mem id aliases alors
        filtre arg avec
        | Some v -> v
        | _      -> raise Cannot_flatten
      sinon
        Ident.create (Ident.name id))
    ids

soit rec explode_or_pat arg patl mk_action rem vars aliases = fonction
  | {pat_desc = Tpat_or (p1,p2,_)} ->
      explode_or_pat
        arg patl mk_action
        (explode_or_pat arg patl mk_action rem vars aliases p2)
        vars aliases p1
  | {pat_desc = Tpat_alias (p,id, _)} ->
      explode_or_pat arg patl mk_action rem vars (id::aliases) p
  | {pat_desc = Tpat_var (x, _)} ->
      soit env = mk_alpha_env arg (x::aliases) vars dans
      (omega::patl,mk_action (List.map snd env))::rem
  | p ->
      soit env = mk_alpha_env arg aliases vars dans
      (alpha_pat env p::patl,mk_action (List.map snd env))::rem

soit pm_free_variables {cases=cases} =
  List.fold_right
    (fonc (_,act) r -> IdentSet.union (free_variables act) r)
    cases IdentSet.empty


(* Basic grouping predicates *)
soit pat_as_constr = fonction
  | {pat_desc=Tpat_construct (_, cstr,_)} -> cstr
  | _ -> fatal_error "Matching.pat_as_constr"

soit group_constant = fonction
  | {pat_desc= Tpat_constant _} -> vrai
  | _                           -> faux

et group_constructor = fonction
  | {pat_desc = Tpat_construct (_,_,_)} -> vrai
  | _ -> faux

et group_variant = fonction
  | {pat_desc = Tpat_variant (_, _, _)} -> vrai
  | _ -> faux

et group_var = fonction
  | {pat_desc=Tpat_any} -> vrai
  | _ -> faux

et group_tuple = fonction
  | {pat_desc = (Tpat_tuple _|Tpat_any)} -> vrai
  | _ -> faux

et group_record = fonction
  | {pat_desc = (Tpat_record _|Tpat_any)} -> vrai
  | _ -> faux

et group_array = fonction
  | {pat_desc=Tpat_array _} -> vrai
  | _ -> faux

et group_lazy = fonction
  | {pat_desc = Tpat_lazy _} -> vrai
  | _ -> faux

soit get_group p = filtre p.pat_desc avec
| Tpat_any -> group_var
| Tpat_constant _ -> group_constant
| Tpat_construct _ -> group_constructor
| Tpat_tuple _ -> group_tuple
| Tpat_record _ -> group_record
| Tpat_array _ -> group_array
| Tpat_variant (_,_,_) -> group_variant
| Tpat_lazy _ -> group_lazy
|  _ -> fatal_error "Matching.get_group"



soit is_or p = filtre p.pat_desc avec
| Tpat_or _ -> vrai
| _ -> faux

(* Conditions for appending to the Or matrix *)
soit conda p q = not (compat p q)
et condb act ps qs =  not (is_guarded act) && Parmatch.le_pats qs ps

soit or_ok p ps l =
  List.for_all
    (fonction
      | ({pat_desc=Tpat_or _} tel q::qs,act) ->
          conda p q || condb act ps qs
      | _ -> vrai)
    l

(* Insert or append a pattern in the Or matrix *)

soit equiv_pat p q = le_pat p q && le_pat q p

soit rec get_equiv p l = filtre l avec
  | (q::_,_) tel cl::rem ->
      si equiv_pat p q alors
        soit others,rem = get_equiv p rem dans
        cl::others,rem
      sinon
        [],l
  | _ -> [],l


soit insert_or_append p ps act ors no =
  soit rec attempt seen = fonction
    | (q::qs,act_q) tel cl::rem ->
        si is_or q alors début
          si compat p q alors
            si
              IdentSet.is_empty (extract_vars IdentSet.empty p) &&
              IdentSet.is_empty (extract_vars IdentSet.empty q) &&
              equiv_pat p q
            alors (* attempt insert, for equivalent orpats with no variables *)
              soit _, not_e = get_equiv q rem dans
              si
                or_ok p ps not_e && (* check append condition for head of O *)
                List.for_all        (* check insert condition for tail of O *)
                  (fonc cl -> filtre cl avec
                  | (q::_,_) -> not (compat p q)
                  | _        -> affirme faux)
                  seen
              alors (* insert *)
                List.rev_append seen ((p::ps,act)::cl::rem), no
              sinon (* fail to insert or append *)
                ors,(p::ps,act)::no
            sinon si condb act_q ps qs alors (* check condition (b) for append *)
              attempt (cl::seen) rem
            sinon
              ors,(p::ps,act)::no
          sinon (* p # q, go on with append/insert *)
            attempt (cl::seen) rem
        fin sinon (* q is not a or-pat, go on with append/insert *)
          attempt (cl::seen) rem
    | _  -> (* [] in fact *)
        (p::ps,act)::ors,no dans (* success in appending *)
  attempt [] ors

(* Reconstruct default information from half_compiled  pm list *)

soit rec rebuild_matrix pmh = filtre pmh avec
  | Pm pm -> as_matrix pm.cases
  | PmOr {or_matrix=m} -> m
  | PmVar x -> add_omega_column  (rebuild_matrix x.inside)

soit rec rebuild_default nexts def = filtre nexts avec
| [] -> def
| (e, pmh)::rem ->
    (add_omega_column (rebuild_matrix pmh), e)::
    rebuild_default rem def

soit rebuild_nexts arg nexts k =
  List.fold_right
    (fonc (e, pm) k -> (e, PmVar {inside=pm ; var_arg=arg})::k)
    nexts k


(*
  Split a matching.
    Splitting is first directed by or-patterns, then by
    tests (e.g. constructors)/variable transitions.

    The approach is greedy, every split function attempt to
    raise rows as much as possible in the top matrix,
    then splitting applies again to the remaining rows.

    Some precompilation of or-patterns and
    variable pattern occurs. Mostly this means that bindings
    are performed now,  being replaced by let-bindings
    in actions (cf. simplify_cases).

    Additionally, if the match argument is a variable, matchings whose
    first column is made of variables only are splitted further
    (cf. precompile_var).

*)


soit rec split_or argo cls args def =

  soit cls = simplify_cases args cls dans

  soit rec do_split before ors no = fonction
    | [] ->
        cons_next
          (List.rev before) (List.rev ors) (List.rev no)
    | ((p::ps,act) tel cl)::rem ->
        si up_ok cl no alors
          si is_or p alors
            soit ors, no = insert_or_append p ps act ors no dans
            do_split before ors no rem
          sinon début
            si up_ok cl ors alors
              do_split (cl::before) ors no rem
            sinon si or_ok p ps ors alors
              do_split before (cl::ors) no rem
            sinon
              do_split before ors (cl::no) rem
          fin
        sinon
          do_split before ors (cl::no) rem
    | _ -> affirme faux

  et cons_next yes yesor = fonction
    | [] ->
        precompile_or argo yes yesor args def []
    | rem ->
        soit {me=next ; matrix=matrix ; top_default=def},nexts =
          do_split [] [] [] rem dans
        soit idef = next_raise_count () dans
        precompile_or
          argo yes yesor args
          (cons_default matrix idef def)
          ((idef,next)::nexts) dans

  do_split [] [] [] cls

(* Ultra-naive spliting, close to semantics,
   used for exception, as potential rebind prevents any kind of
   optimisation *)

et split_naive cls args def k =

  soit rec split_exc cstr0 yes = fonction
    | [] ->
        soit yes = List.rev yes dans
        { me = Pm {cases=yes; args=args; default=def;} ;
          matrix = as_matrix_omega yes ;
          top_default=def},
        k
    | (p::_,_ tel cl)::rem ->
        si group_constructor p alors
          soit cstr = pat_as_constr p dans
          si cstr = cstr0 alors split_exc cstr0 (cl::yes) rem
          sinon
            soit yes = List.rev yes dans
            soit {me=next ; matrix=matrix ; top_default=def}, nexts =
              split_exc cstr [cl] rem dans
            soit idef = next_raise_count () dans
            soit def = cons_default matrix idef def dans
            { me = Pm {cases=yes; args=args; default=def} ;
              matrix = as_matrix_omega yes ;
              top_default = def; },
            (idef,next)::nexts
        sinon
          soit yes = List.rev yes dans
          soit {me=next ; matrix=matrix ; top_default=def}, nexts =
              split_noexc [cl] rem dans
            soit idef = next_raise_count () dans
            soit def = cons_default matrix idef def dans
            { me = Pm {cases=yes; args=args; default=def} ;
              matrix = as_matrix_omega yes ;
              top_default = def; },
            (idef,next)::nexts
    | _ -> affirme faux

  et split_noexc yes = fonction
    | [] -> precompile_var args (List.rev yes) def k
    | (p::_,_ tel cl)::rem ->
        si group_constructor p alors
          soit yes= List.rev yes dans
          soit {me=next; matrix=matrix; top_default=def;},nexts =
            split_exc (pat_as_constr p) [cl] rem dans
          soit idef = next_raise_count () dans
          precompile_var
            args yes
            (cons_default matrix idef def)
            ((idef,next)::nexts)
        sinon split_noexc (cl::yes) rem
    | _ -> affirme faux dans

  filtre cls avec
  | [] -> affirme faux
  | (p::_,_ tel cl)::rem ->
      si group_constructor p alors
        split_exc (pat_as_constr p) [cl] rem
      sinon 
        split_noexc [cl] rem
  | _ -> affirme faux

et split_constr cls args def k =
  soit ex_pat = what_is_cases cls dans
  filtre ex_pat.pat_desc avec
  | Tpat_any -> precompile_var args cls def k
  | Tpat_construct (_,{cstr_tag=Cstr_exception _},_) ->
      split_naive cls args def k
  | _ ->

      soit group = get_group ex_pat dans

      soit rec split_ex yes no = fonction
        | [] ->
            soit yes = List.rev yes et no = List.rev no dans
            début filtre no avec
            | [] ->
                {me = Pm {cases=yes ; args=args ; default=def} ;
                  matrix = as_matrix yes ;
                  top_default = def},
                k
            | cl::rem ->
                début filtre yes avec
                | [] ->
                    (* Could not success in raising up a constr matching up *)
                    split_noex [cl] [] rem
                | _ ->
                    soit {me=next ; matrix=matrix ; top_default=def}, nexts =
                      split_noex [cl] [] rem dans
                    soit idef = next_raise_count () dans
                    soit def = cons_default matrix idef def dans
                    {me = Pm {cases=yes ; args=args ; default=def} ;
                      matrix = as_matrix yes ;
                      top_default = def },
                    (idef, next)::nexts
                fin
            fin
        | (p::_,_) tel cl::rem ->
            si group p && up_ok cl no alors
              split_ex (cl::yes) no rem
            sinon
              split_ex yes (cl::no) rem
        | _ -> affirme faux

      et split_noex yes no = fonction
        | [] ->
            soit yes = List.rev yes et no = List.rev no dans
            début filtre no avec
            | [] -> precompile_var args yes def k
            | cl::rem ->
                soit {me=next ; matrix=matrix ; top_default=def}, nexts =
                  split_ex [cl] [] rem dans
                soit idef = next_raise_count () dans
                precompile_var
                  args yes
                  (cons_default matrix idef def)
                  ((idef,next)::nexts)
            fin
        | [ps,_ tel cl]
            quand List.for_all group_var ps && yes <> [] ->
       (* This enables an extra division in some frequent case :
          last row is made of variables only *)
              split_noex yes (cl::no) []
        | (p::_,_) tel cl::rem ->
            si not (group p) && up_ok cl no alors
              split_noex (cl::yes) no rem
            sinon
              split_noex yes (cl::no) rem
        | _ -> affirme faux dans

      filtre cls avec
      | ((p::_,_) tel cl)::rem ->
          si group p alors split_ex [cl] [] rem
          sinon split_noex [cl] [] rem
      | _ ->  affirme faux

et precompile_var  args cls def k = filtre args avec
| []  -> affirme faux
| _::((Lvar v tel av,_) tel arg)::rargs ->
    début filtre cls avec
    | [ps,_] -> (* as splitted as it can *)
        dont_precompile_var args cls def k
    | _ ->
(* Precompile *)
        soit var_cls =
          List.map
            (fonc (ps,act) -> filtre ps avec
            | _::ps -> ps,act | _     -> affirme faux)
            cls
        et var_def = make_default (fonc _ rem -> rem) def dans
        soit {me=first ; matrix=matrix}, nexts =
          split_or (Some v) var_cls (arg::rargs) var_def dans

(* Compute top information *)
        filtre nexts avec
        | [] -> (* If you need *)
            dont_precompile_var args cls def k
        | _  ->
            soit rfirst =
              {me = PmVar {inside=first ; var_arg = av} ;
                matrix = add_omega_column matrix ;
                top_default = rebuild_default nexts def ; }
            et rnexts = rebuild_nexts av nexts k dans
            rfirst, rnexts
    fin
|  _ ->
    dont_precompile_var args cls def k

et dont_precompile_var args cls def k =
  {me =  Pm {cases = cls ; args = args ; default = def } ;
    matrix=as_matrix cls ;
    top_default=def},k

et is_exc p = filtre p.pat_desc avec
| Tpat_or (p1,p2,_) -> is_exc p1 || is_exc p2
| Tpat_alias (p,v,_) -> is_exc p
| Tpat_construct (_,{cstr_tag = Cstr_exception _},_) -> vrai
| _ -> faux

et precompile_or argo cls ors args def k = filtre ors avec
| [] -> split_constr cls args def k
| _  ->
    soit rec do_cases = fonction
      | ({pat_desc=Tpat_or _} tel orp::patl, action)::rem ->
          soit do_opt = not (is_exc orp) dans
          soit others,rem =
            si do_opt alors get_equiv orp rem
            sinon [],rem dans
          soit orpm =
            {cases =
              (patl, action)::
              List.map
                (fonction
                  | (_::ps,action) -> ps,action
                  | _ -> affirme faux)
                others ;
              args = (filtre args avec _::r -> r | _ -> affirme faux) ;
              default = default_compat (si do_opt alors orp sinon omega) def} dans
          soit vars =
            IdentSet.elements
              (IdentSet.inter
                 (extract_vars IdentSet.empty orp)
                 (pm_free_variables orpm)) dans
          soit or_num = next_raise_count () dans
          soit new_patl = Parmatch.omega_list patl dans

          soit mk_new_action vs =
            Lstaticraise
              (or_num, List.map (fonc v -> Lvar v) vs) dans

          soit do_optrec,body,handlers = do_cases rem dans
          do_opt && do_optrec,
          explode_or_pat
            argo new_patl mk_new_action body vars [] orp,
          soit mat = si do_opt alors [[orp]] sinon [[omega]] dans
          ((mat, or_num, vars , orpm):: handlers)
      | cl::rem ->
          soit b,new_ord,new_to_catch = do_cases rem dans
          b,cl::new_ord,new_to_catch
      | [] -> vrai,[],[] dans

    soit do_opt,end_body, handlers = do_cases ors dans
    soit matrix = (si do_opt alors as_matrix sinon as_matrix_omega) (cls@ors)
    et body = {cases=cls@end_body ; args=args ; default=def} dans
    {me = PmOr {body=body ; handlers=handlers ; or_matrix=matrix} ;
      matrix=matrix ;
      top_default=def},
    k

soit split_precompile argo pm =
  soit {me=next}, nexts = split_or argo pm.cases pm.args pm.default  dans
  si dbg && (nexts <> [] || (filtre next avec PmOr _ -> vrai | _ -> faux))
  alors début
    prerr_endline "** SPLIT **" ;
    pretty_pm pm ;
    pretty_precompiled_res  next nexts
  fin ;
  next, nexts


(* General divide functions *)

soit add_line patl_action pm = pm.cases <- patl_action :: pm.cases; pm

type cell =
  {pm : pattern_matching ;
  ctx : ctx list ;
  pat : pattern}

soit add make_matching_fun division eq_key key patl_action args =
  essaie
    soit (_,cell) = List.find (fonc (k,_) -> eq_key key k) division dans
    cell.pm.cases <- patl_action :: cell.pm.cases;
    division
  avec Not_found ->
    soit cell = make_matching_fun args dans
    cell.pm.cases <- [patl_action] ;
    (key, cell) :: division


soit divide make eq_key get_key get_args ctx pm =

  soit rec divide_rec = fonction
    | (p::patl,action) :: rem ->
        soit this_match = divide_rec rem dans
        add
          (make p pm.default ctx)
          this_match eq_key (get_key p) (get_args p patl,action) pm.args
    | _ -> [] dans

  divide_rec pm.cases


soit divide_line make_ctx make get_args pat ctx pm =
  soit rec divide_rec = fonction
    | (p::patl,action) :: rem ->
        soit this_match = divide_rec rem dans
        add_line (get_args p patl, action) this_match
    | _ -> make pm.default pm.args dans

  {pm = divide_rec pm.cases ;
  ctx=make_ctx ctx ;
  pat=pat}



(* Then come various functions,
   There is one set of functions per matching style
   (constants, constructors etc.)

   - matcher function are arguments to make_default (for defaukt handlers)
   They may raise NoMatch or OrPat and perform the full
   matching (selection + arguments).


   - get_args and get_key are for the compiled matrices, note that
   selection and geting arguments are separed.

   - make_ _matching combines the previous functions for produicing
   new  ``pattern_matching'' records.
*)



soit rec matcher_const cst p rem = filtre p.pat_desc avec
| Tpat_or (p1,p2,_) ->
    début essaie
      matcher_const cst p1 rem avec
    | NoMatch -> matcher_const cst p2 rem
    fin
| Tpat_constant c1 quand const_compare c1 cst = 0 -> rem
| Tpat_any    -> rem
| _ -> raise NoMatch

soit get_key_constant caller = fonction
  | {pat_desc= Tpat_constant cst} -> cst
  | p ->
      prerr_endline ("BAD: "^caller) ;
      pretty_pat p ;
      affirme faux

soit get_args_constant _ rem = rem

soit make_constant_matching p def ctx = fonction
    [] -> fatal_error "Matching.make_constant_matching"
  | (_ :: argl) ->
      soit def =
        make_default
          (matcher_const (get_key_constant "make" p)) def
      et ctx =
        filter_ctx p  ctx dans
      {pm = {cases = []; args = argl ; default = def} ;
        ctx = ctx ;
        pat = normalize_pat p}




soit divide_constant ctx m =
  divide
    make_constant_matching
    (fonc c d -> const_compare c d = 0) (get_key_constant "divide")
    get_args_constant
    ctx m

(* Matching against a constructor *)


soit make_field_args binding_kind arg first_pos last_pos argl =
  soit rec make_args pos =
    si pos > last_pos
    alors argl
    sinon (Lprim(Pfield pos, [arg]), binding_kind) :: make_args (pos + 1)
  dans make_args first_pos

soit get_key_constr = fonction
  | {pat_desc=Tpat_construct (_, cstr,_)} -> cstr.cstr_tag
  | _ -> affirme faux

soit get_args_constr p rem = filtre p avec
| {pat_desc=Tpat_construct (_, _, args)} -> args @ rem
| _ -> affirme faux

soit matcher_constr cstr = filtre cstr.cstr_arity avec
| 0 ->
    soit rec matcher_rec q rem = filtre q.pat_desc avec
    | Tpat_or (p1,p2,_) ->
        début
          essaie
            matcher_rec p1 rem
          avec
          | NoMatch -> matcher_rec p2 rem
        fin
    | Tpat_construct (_, cstr1, []) quand cstr.cstr_tag = cstr1.cstr_tag ->
        rem
    | Tpat_any -> rem
    | _ -> raise NoMatch dans
    matcher_rec
| 1 ->
    soit rec matcher_rec q rem = filtre q.pat_desc avec
    | Tpat_or (p1,p2,_) ->
        soit r1 = essaie Some (matcher_rec p1 rem) avec NoMatch -> None
        et r2 = essaie Some (matcher_rec p2 rem) avec NoMatch -> None dans
        début filtre r1,r2 avec
        | None, None -> raise NoMatch
        | Some r1, None -> r1
        | None, Some r2 -> r2
        | Some (a1::rem1), Some (a2::_) ->
            {a1 avec
             pat_loc = Location.none ;
             pat_desc = Tpat_or (a1, a2, None)}::
            rem
        | _, _ -> affirme faux
        fin
    | Tpat_construct (_, cstr1, [arg])
      quand cstr.cstr_tag = cstr1.cstr_tag -> arg::rem
    | Tpat_any -> omega::rem
    | _ -> raise NoMatch dans
    matcher_rec
| _ ->
    fonc q rem -> filtre q.pat_desc avec
    | Tpat_or (_,_,_) -> raise OrPat
    | Tpat_construct (_, cstr1, args)
      quand cstr.cstr_tag = cstr1.cstr_tag -> args @ rem
    | Tpat_any -> Parmatch.omegas cstr.cstr_arity @ rem
    | _        -> raise NoMatch

soit make_constr_matching p def ctx = fonction
    [] -> fatal_error "Matching.make_constr_matching"
  | ((arg, mut) :: argl) ->
      soit cstr = pat_as_constr p dans
      soit newargs =
        filtre cstr.cstr_tag avec
          Cstr_constant _ | Cstr_block _ ->
            make_field_args Alias arg 0 (cstr.cstr_arity - 1) argl
        | Cstr_exception _ ->
            make_field_args Alias arg 1 cstr.cstr_arity argl dans
      {pm=
        {cases = []; args = newargs;
          default = make_default (matcher_constr cstr) def} ;
        ctx =  filter_ctx p ctx ;
        pat=normalize_pat p}


soit divide_constructor ctx pm =
  divide
    make_constr_matching
    (=) get_key_constr get_args_constr
    ctx pm

(* Matching against a variant *)

soit rec matcher_variant_const lab p rem = filtre p.pat_desc avec
| Tpat_or (p1, p2, _) ->
    début
      essaie
        matcher_variant_const lab p1 rem
      avec
      | NoMatch -> matcher_variant_const lab p2 rem
    fin
| Tpat_variant (lab1,_,_) quand lab1=lab -> rem
| Tpat_any -> rem
| _   -> raise NoMatch


soit make_variant_matching_constant p lab def ctx = fonction
    [] -> fatal_error "Matching.make_variant_matching_constant"
  | ((arg, mut) :: argl) ->
      soit def = make_default (matcher_variant_const lab) def
      et ctx = filter_ctx p ctx dans
      {pm={ cases = []; args = argl ; default=def} ;
        ctx=ctx ;
        pat = normalize_pat p}

soit matcher_variant_nonconst lab p rem = filtre p.pat_desc avec
| Tpat_or (_,_,_) -> raise OrPat
| Tpat_variant (lab1,Some arg,_) quand lab1=lab -> arg::rem
| Tpat_any -> omega::rem
| _   -> raise NoMatch


soit make_variant_matching_nonconst p lab def ctx = fonction
    [] -> fatal_error "Matching.make_variant_matching_nonconst"
  | ((arg, mut) :: argl) ->
      soit def = make_default (matcher_variant_nonconst lab) def
      et ctx = filter_ctx p ctx dans
      {pm=
        {cases = []; args = (Lprim(Pfield 1, [arg]), Alias) :: argl;
          default=def} ;
        ctx=ctx ;
        pat = normalize_pat p}

soit get_key_variant p = filtre p.pat_desc avec
| Tpat_variant(lab, Some _ , _) ->  Cstr_block (Btype.hash_variant lab)
| Tpat_variant(lab, None , _) -> Cstr_constant (Btype.hash_variant lab)
|  _ -> affirme faux

soit divide_variant row ctx {cases = cl; args = al; default=def} =
  soit row = Btype.row_repr row dans
  soit rec divide = fonction
      ({pat_desc = Tpat_variant(lab, pato, _)} tel p:: patl, action) :: rem ->
        soit variants = divide rem dans
        si essaie Btype.row_field_repr (List.assoc lab row.row_fields) = Rabsent
        avec Not_found -> vrai
        alors
          variants
        sinon début
          soit tag = Btype.hash_variant lab dans
          filtre pato avec
            None ->
              add (make_variant_matching_constant p lab def ctx) variants
                (=) (Cstr_constant tag) (patl, action) al
          | Some pat ->
              add (make_variant_matching_nonconst p lab def ctx) variants
                (=) (Cstr_block tag) (pat :: patl, action) al
        fin
    | cl -> []
  dans
  divide cl

(*
  Three ``no-test'' cases
  *)

(* Matching against a variable *)

soit get_args_var _ rem = rem


soit make_var_matching def = fonction
  | [] ->  fatal_error "Matching.make_var_matching"
  | _::argl ->
      {cases=[] ;
        args = argl ;
        default= make_default get_args_var def}

soit divide_var ctx pm =
  divide_line ctx_lshift make_var_matching get_args_var omega ctx pm

(* Matching and forcing a lazy value *)

soit get_arg_lazy p rem = filtre p avec
| {pat_desc = Tpat_any} -> omega :: rem
| {pat_desc = Tpat_lazy arg} -> arg :: rem
| _ ->  affirme faux

soit matcher_lazy p rem = filtre p.pat_desc avec
| Tpat_or (_,_,_)     -> raise OrPat
| Tpat_var _          -> get_arg_lazy omega rem
| _                   -> get_arg_lazy p rem

(* Inlining the tag tests before calling the primitive that works on
   lazy blocks. This is alse used in translcore.ml.
   No call other than Obj.tag when the value has been forced before.
*)

soit prim_obj_tag =
  {prim_name = "caml_obj_tag";
   prim_arity = 1; prim_alloc = faux;
   prim_native_name = "";
   prim_native_float = faux}

soit get_mod_field modname field =
  paresseux (
    essaie
      soit mod_ident = Ident.create_persistent modname dans
      soit env = Env.open_pers_signature modname Env.initial dans
      soit p = essaie
        filtre Env.lookup_value (Longident.Lident field) env avec
        | (Path.Pdot(_,_,i), _) -> i
        | _ -> fatal_error ("Primitive "^modname^"."^field^" introuvable.")
      avec Not_found ->
        fatal_error ("Primitive "^modname^"."^field^" introuvable.")
      dans
      Lprim(Pfield p, [Lprim(Pgetglobal mod_ident, [])])
    avec Not_found -> fatal_error ("Module "^modname^" non disponible.")
  )

soit code_force_lazy_block =
  get_mod_field "CamlinternalLazy" "force_lazy_block"
;;

(* inline_lazy_force inlines the beginning of the code of Lazy.force. When
   the value argument is tagged as:
   - forward, take field 0
   - lazy, call the primitive that forces (without testing again the tag)
   - anything else, return it

   Using Lswitch below relies on the fact that the GC does not shortcut
   Forward(val_out_of_heap).
*)

soit inline_lazy_force_cond arg loc =
  soit idarg = Ident.create "lzarg" dans
  soit varg = Lvar idarg dans
  soit tag = Ident.create "tag" dans
  soit force_fun = Lazy.force code_force_lazy_block dans
  Llet(Strict, idarg, arg,
       Llet(Alias, tag, Lprim(Pccall prim_obj_tag, [varg]),
            Lifthenelse(
              (* if (tag == Obj.forward_tag) then varg.(0) else ... *)
              Lprim(Pintcomp Ceq,
                    [Lvar tag; Lconst(Const_base(Const_int Obj.forward_tag))]),
              Lprim(Pfield 0, [varg]),
              Lifthenelse(
                (* ... if (tag == Obj.lazy_tag) then Lazy.force varg else ... *)
                Lprim(Pintcomp Ceq,
                      [Lvar tag; Lconst(Const_base(Const_int Obj.lazy_tag))]),
                Lapply(force_fun, [varg], loc),
                (* ... arg *)
                  varg))))

soit inline_lazy_force_switch arg loc =
  soit idarg = Ident.create "lzarg" dans
  soit varg = Lvar idarg dans
  soit force_fun = Lazy.force code_force_lazy_block dans
  Llet(Strict, idarg, arg,
       Lifthenelse(
         Lprim(Pisint, [varg]), varg,
         (Lswitch
            (varg,
             { sw_numconsts = 0; sw_consts = [];
               sw_numblocks = 256;  (* PR#6033 - tag ranges from 0 to 255 *)
               sw_blocks =
                 [ (Obj.forward_tag, Lprim(Pfield 0, [varg]));
                   (Obj.lazy_tag,
                    Lapply(force_fun, [varg], loc)) ];
               sw_failaction = Some varg } ))))

soit inline_lazy_force arg loc =
  si !Clflags.native_code alors
    (* Lswitch generates compact and efficient native code *)
    inline_lazy_force_switch arg loc
  sinon
    (* generating bytecode: Lswitch would generate too many rather big
       tables (~ 250 elts); conditionals are better *)
    inline_lazy_force_cond arg loc

soit make_lazy_matching def = fonction
    [] -> fatal_error "Matching.make_lazy_matching"
  | (arg,mut) :: argl ->
      { cases = [];
        args =
          (inline_lazy_force arg Location.none, Strict) :: argl;
        default = make_default matcher_lazy def }

soit divide_lazy p ctx pm =
  divide_line
    (filter_ctx p)
    make_lazy_matching
    get_arg_lazy
    p ctx pm

(* Matching against a tuple pattern *)


soit get_args_tuple arity p rem = filtre p avec
| {pat_desc = Tpat_any} -> omegas arity @ rem
| {pat_desc = Tpat_tuple args} ->
    args @ rem
| _ ->  affirme faux

soit matcher_tuple arity p rem = filtre p.pat_desc avec
| Tpat_or (_,_,_)     -> raise OrPat
| Tpat_var _          -> get_args_tuple arity omega rem
| _                   ->  get_args_tuple arity p rem

soit make_tuple_matching arity def = fonction
    [] -> fatal_error "Matching.make_tuple_matching"
  | (arg, mut) :: argl ->
      soit rec make_args pos =
        si pos >= arity
        alors argl
        sinon (Lprim(Pfield pos, [arg]), Alias) :: make_args (pos + 1) dans
      {cases = []; args = make_args 0 ;
        default=make_default (matcher_tuple arity) def}


soit divide_tuple arity p ctx pm =
  divide_line
    (filter_ctx p)
    (make_tuple_matching arity)
    (get_args_tuple  arity) p ctx pm

(* Matching against a record pattern *)


soit record_matching_line num_fields lbl_pat_list =
  soit patv = Array.create num_fields omega dans
  List.iter (fonc (_, lbl, pat) -> patv.(lbl.lbl_pos) <- pat) lbl_pat_list;
  Array.to_list patv

soit get_args_record num_fields p rem = filtre p avec
| {pat_desc=Tpat_any} ->
    record_matching_line num_fields [] @ rem
| {pat_desc=Tpat_record (lbl_pat_list,_)} ->
    record_matching_line num_fields lbl_pat_list @ rem
| _ -> affirme faux

soit matcher_record num_fields p rem = filtre p.pat_desc avec
| Tpat_or (_,_,_) -> raise OrPat
| Tpat_var _      -> get_args_record num_fields omega rem
| _               -> get_args_record num_fields p rem

soit make_record_matching all_labels def = fonction
    [] -> fatal_error "Matching.make_record_matching"
  | ((arg, mut) :: argl) ->
      soit rec make_args pos =
        si pos >= Array.length all_labels alors argl sinon début
          soit lbl = all_labels.(pos) dans
          soit access =
            filtre lbl.lbl_repres avec
              Record_regular -> Pfield lbl.lbl_pos
            | Record_float -> Pfloatfield lbl.lbl_pos dans
          soit str =
            filtre lbl.lbl_mut avec
              Immutable -> Alias
            | Mutable -> StrictOpt dans
          (Lprim(access, [arg]), str) :: make_args(pos + 1)
        fin dans
      soit nfields = Array.length all_labels dans
      soit def= make_default (matcher_record nfields) def dans
      {cases = []; args = make_args 0 ; default = def}


soit divide_record all_labels p ctx pm =
  soit get_args = get_args_record (Array.length all_labels) dans
  divide_line
    (filter_ctx p)
    (make_record_matching all_labels)
    get_args
    p ctx pm

(* Matching against an array pattern *)

soit get_key_array = fonction
  | {pat_desc=Tpat_array patl} -> List.length patl
  | _ -> affirme faux

soit get_args_array p rem = filtre p avec
| {pat_desc=Tpat_array patl} -> patl@rem
| _ -> affirme faux

soit matcher_array len p rem = filtre p.pat_desc avec
| Tpat_or (_,_,_) -> raise OrPat
| Tpat_array args quand List.length args=len -> args @ rem
| Tpat_any -> Parmatch.omegas len @ rem
| _ -> raise NoMatch

soit make_array_matching kind p def ctx = fonction
  | [] -> fatal_error "Matching.make_array_matching"
  | ((arg, mut) :: argl) ->
      soit len = get_key_array p dans
      soit rec make_args pos =
        si pos >= len
        alors argl
        sinon (Lprim(Parrayrefu kind, [arg; Lconst(Const_base(Const_int pos))]),
              StrictOpt) :: make_args (pos + 1) dans
      soit def = make_default (matcher_array len) def
      et ctx = filter_ctx p ctx dans
      {pm={cases = []; args = make_args 0 ; default = def} ;
        ctx=ctx ;
        pat = normalize_pat p}

soit divide_array kind ctx pm =
  divide
    (make_array_matching kind)
    (=) get_key_array get_args_array ctx pm

(*
   Specific string test sequence
   Will be called by the bytecode compiler, from bytegen.ml.   
   The strategy is first dichotomic search (we perform 3-way tests
   with compare_string), then sequence of equality tests
   when there are less then T=strings_test_threshold static strings to match.

  Increasing T entails (slightly) less code, decreasing T
  (slightly) favors runtime speed.
  T=8 looks a decent tradeoff.
*)

(* Utlities *)

soit strings_test_threshold = 8

soit prim_string_notequal =
  Pccall{prim_name = "caml_string_notequal";
         prim_arity = 2; prim_alloc = faux;
         prim_native_name = ""; prim_native_float = faux}

soit prim_string_compare =
  Pccall{prim_name = "caml_string_compare";
         prim_arity = 2; prim_alloc = faux;
         prim_native_name = ""; prim_native_float = faux}

soit bind_sw arg k = filtre arg avec
| Lvar _ -> k arg
| _ ->
    soit id = Ident.create "switch" dans
    Llet (Strict,id,arg,k (Lvar id))
    
  
(* Sequential equality tests *)

soit make_test_sequence arg sw d =
  bind_sw arg
    (fonc arg ->
      List.fold_right
        (fonc (s,lam) k ->
          Lifthenelse
            (Lprim
               (prim_string_notequal,
                [arg; Lconst (Const_immstring s)]),
             k,lam))
        sw d)

soit catch_sw d k = filtre d avec
| Lstaticraise (_,[]) -> k d
| _ ->
    soit e = next_raise_count () dans
    Lstaticcatch (k (Lstaticraise (e,[])),(e,[]),d)

soit rec split k xs = filtre xs avec
| [] -> affirme faux
| x0::xs ->
    si k <= 1 alors [],x0,xs
    sinon
      soit xs,y0,ys = split (k-2) xs dans
      x0::xs,y0,ys

soit zero_lam  = Lconst (Const_base (Const_int 0))

soit tree_way_test arg lt eq gt =
  Lifthenelse
    (Lprim (Pintcomp Clt,[arg;zero_lam]),lt,
     Lifthenelse(Lprim (Pintcomp Clt,[zero_lam;arg]),gt,eq))

(* Dichotomic tree *)

soit rec do_make_tree arg sw d =
  soit len = List.length sw dans
  si len <= strings_test_threshold alors make_test_sequence arg sw d
  sinon
    soit lt,(s,act),gt = split len sw dans
    bind_sw
      (Lprim
         (prim_string_compare,
          [arg; Lconst (Const_immstring s)];))
      (fonc r ->
        tree_way_test r
          (do_make_tree arg lt d)
          act
          (do_make_tree arg gt d))
           
(* Entry point *)
soit expand_stringswitch arg sw d =
  bind_sw arg (fonc arg -> catch_sw d (fonc d -> do_make_tree arg sw d))

(*************************************)
(* To combine sub-matchings together *)
(*************************************)

(* Note: dichotomic search requires sorted input with no duplicates *)
soit rec uniq_lambda_list sw = filtre sw avec
  | []|[_] -> sw
  | (c1,_ tel p1)::((c2,_)::sw2 tel sw1) ->
      si const_compare c1 c2 = 0 alors uniq_lambda_list (p1::sw2)
      sinon p1::uniq_lambda_list sw1

soit sort_lambda_list l =
  soit l =
    List.stable_sort (fonc (x,_) (y,_) -> const_compare x y) l dans
  uniq_lambda_list l

soit rec cut n l =
  si n = 0 alors [],l
  sinon filtre l avec
    [] -> raise (Invalid_argument "cut")
  | a::l -> soit l1,l2 = cut (n-1) l dans a::l1, l2

soit rec do_tests_fail fail tst arg = fonction
  | [] -> fail
  | (c, act)::rem ->
      Lifthenelse
        (Lprim (tst, [arg ; Lconst (Const_base c)]),
         do_tests_fail fail tst arg rem,
         act)

soit rec do_tests_nofail tst arg = fonction
  | [] -> fatal_error "Matching.do_tests_nofail"
  | [_,act] -> act
  | (c,act)::rem ->
      Lifthenelse
        (Lprim (tst, [arg ; Lconst (Const_base c)]),
         do_tests_nofail tst arg rem,
         act)

soit make_test_sequence fail tst lt_tst arg const_lambda_list =
  soit rec make_test_sequence const_lambda_list =
    si List.length const_lambda_list >= 4 && lt_tst <> Pignore alors
      split_sequence const_lambda_list
    sinon filtre fail avec
    | None -> do_tests_nofail tst arg const_lambda_list
    | Some fail -> do_tests_fail fail tst arg const_lambda_list

  et split_sequence const_lambda_list =
    soit list1, list2 =
      cut (List.length const_lambda_list / 2) const_lambda_list dans
    Lifthenelse(Lprim(lt_tst,[arg; Lconst(Const_base (fst(List.hd list2)))]),
                make_test_sequence list1, make_test_sequence list2)
  dans make_test_sequence (sort_lambda_list const_lambda_list)


soit make_offset x arg = si x=0 alors arg sinon Lprim(Poffsetint(x), [arg])

soit rec explode_inter offset i j act k =
  si i <= j alors
    explode_inter offset i (j-1) act ((j-offset,act)::k)
  sinon
    k

soit max_vals cases acts =
  soit vals = Array.create (Array.length acts) 0 dans
  pour i=Array.length cases-1 descendant_jusqu'a 0 faire
    soit l,h,act = cases.(i) dans
    vals.(act) <- h - l + 1 + vals.(act)
  fait ;
  soit max = ref 0 dans
  pour i = Array.length vals-1 descendant_jusqu'a 0 faire
    si vals.(i) >= vals.(!max) alors
      max := i
  fait ;
  si vals.(!max) > 1 alors
    !max
  sinon
    -1

soit as_int_list cases acts =
  soit default = max_vals cases acts dans
  soit min_key,_,_ = cases.(0)
  et _,max_key,_ = cases.(Array.length cases-1) dans

  soit rec do_rec i k =
    si i >= 0 alors
      soit low, high, act =  cases.(i) dans
      si act = default alors
        do_rec (i-1) k
      sinon
        do_rec (i-1) (explode_inter min_key low high acts.(act) k)
    sinon
      k dans
  min_key, max_key,do_rec (Array.length cases-1) [],
  (si default >= 0 alors Some acts.(default) sinon None)


soit make_switch_offset arg min_key max_key int_lambda_list default  =
  soit numcases = max_key - min_key + 1 dans
  soit cases =
    List.map (fonc (key, l) -> (key - min_key, l)) int_lambda_list dans
  soit offsetarg = make_offset (-min_key) arg dans
  Lswitch(offsetarg,
          {sw_numconsts = numcases; sw_consts = cases;
            sw_numblocks = 0; sw_blocks = [];
            sw_failaction = default})

soit make_switch_switcher arg cases acts =
  soit l = ref [] dans
  pour i = Array.length cases-1 descendant_jusqu'a 0 faire
    l := (i,acts.(cases.(i))) ::  !l
  fait ;
  Lswitch(arg,
          {sw_numconsts = Array.length cases ; sw_consts = !l ;
            sw_numblocks = 0 ; sw_blocks =  []  ;
            sw_failaction = None})

soit full sw =
  List.length sw.sw_consts = sw.sw_numconsts &&
  List.length sw.sw_blocks = sw.sw_numblocks

soit make_switch (arg,sw) = filtre sw.sw_failaction avec
| None ->
    soit t = Hashtbl.create 17 dans
    soit seen l = filtre l avec
    | Lstaticraise (i,[]) ->
        soit old = essaie Hashtbl.find t i avec Not_found -> 0 dans
        Hashtbl.replace t i (old+1)
    | _ -> () dans
    List.iter (fonc (_,lam) -> seen lam) sw.sw_consts ;
    List.iter (fonc (_,lam) -> seen lam) sw.sw_blocks ;
    soit i_max = ref (-1)
    et max = ref (-1) dans
    Hashtbl.iter
      (fonc i c ->
        si c > !max alors début
          i_max := i ;
          max := c
        fin) t ;
    si !i_max >= 0 alors
      soit default = !i_max dans
      soit rec remove = fonction
        | [] -> []
        | (_,Lstaticraise (j,[]))::rem quand j=default ->
            remove rem
        | x::rem -> x::remove rem dans
      Lswitch
        (arg,
         {sw avec
sw_consts = remove sw.sw_consts ;
sw_blocks = remove sw.sw_blocks ;
sw_failaction = Some (Lstaticraise (default,[]))})
    sinon
      Lswitch (arg,sw)
| _ -> Lswitch (arg,sw)

module SArg = struct
  type primitive = Lambda.primitive

  soit eqint = Pintcomp Ceq
  soit neint = Pintcomp Cneq
  soit leint = Pintcomp Cle
  soit ltint = Pintcomp Clt
  soit geint = Pintcomp Cge
  soit gtint = Pintcomp Cgt

  type act = Lambda.lambda

  soit make_prim p args = Lprim (p,args)
  soit make_offset arg n = filtre n avec
  | 0 -> arg
  | _ -> Lprim (Poffsetint n,[arg])
  soit bind arg body =
    soit newvar,newarg = filtre arg avec
    | Lvar v -> v,arg
    | _      ->
        soit newvar = Ident.create "switcher" dans
        newvar,Lvar newvar dans
    bind Alias newvar arg (body newarg)

  soit make_isout h arg = Lprim (Pisout, [h ; arg])
  soit make_isin h arg = Lprim (Pnot,[make_isout h arg])
  soit make_if cond ifso ifnot = Lifthenelse (cond, ifso, ifnot)
  soit make_switch = make_switch_switcher
fin

module Switcher = Switch.Make(SArg)
ouvre Switch

soit lambda_of_int i =  Lconst (Const_base (Const_int i))

soit rec last def = fonction
  | [] -> def
  | [x,_] -> x
  | _::rem -> last def rem

soit get_edges low high l = filtre l avec
| [] -> low, high
| (x,_)::_ -> x, last high l


soit as_interval_canfail fail low high l =
  soit store = mk_store equal_action dans
  soit rec nofail_rec cur_low cur_high cur_act = fonction
    | [] ->
        si cur_high = high alors
          [cur_low,cur_high,cur_act]
        sinon
          [(cur_low,cur_high,cur_act) ; (cur_high+1,high, 0)]
    | ((i,act_i)::rem) tel all ->
        soit act_index = store.act_store act_i dans
        si cur_high+1= i alors
          si act_index=cur_act alors
            nofail_rec cur_low i cur_act rem
          sinon si act_index=0 alors
            (cur_low,i-1, cur_act)::fail_rec i i rem
          sinon
            (cur_low, i-1, cur_act)::nofail_rec i i act_index rem
        sinon
          (cur_low, cur_high, cur_act)::
          fail_rec ((cur_high+1)) (cur_high+1) all

  et fail_rec cur_low cur_high = fonction
    | [] -> [(cur_low, cur_high, 0)]
    | (i,act_i)::rem ->
        soit index = store.act_store act_i dans
        si index=0 alors fail_rec cur_low i rem
        sinon
          (cur_low,i-1,0)::
          nofail_rec i i index rem dans

  soit init_rec = fonction
    | [] -> []
    | (i,act_i)::rem ->
        soit index = store.act_store act_i dans
        si index=0 alors
          fail_rec low i rem
        sinon
          si low < i alors
            (low,i-1,0)::nofail_rec i i index rem
          sinon
            nofail_rec i i index rem dans

  ignore (store.act_store fail) ; (* fail has action index 0 *)
  soit r = init_rec l dans
  Array.of_list r,  store.act_get ()

soit as_interval_nofail l =
  soit store = mk_store equal_action dans

  soit rec i_rec cur_low cur_high cur_act = fonction
    | [] ->
        [cur_low, cur_high, cur_act]
    | (i,act)::rem ->
        soit act_index = store.act_store act dans
        si act_index = cur_act alors
          i_rec cur_low i cur_act rem
        sinon
          (cur_low, cur_high, cur_act)::
          i_rec i i act_index rem dans
  soit inters = filtre l avec
  | (i,act)::rem ->
      soit act_index = store.act_store act dans
      i_rec i i act_index rem
  | _ -> affirme faux dans

  Array.of_list inters, store.act_get ()


soit sort_int_lambda_list l =
  List.sort
    (fonc (i1,_) (i2,_) ->
      si i1 < i2 alors -1
      sinon si i2 < i1 alors 1
      sinon 0)
    l

soit as_interval fail low high l =
  soit l = sort_int_lambda_list l dans
  get_edges low high l,
  (filtre fail avec
  | None -> as_interval_nofail l
  | Some act -> as_interval_canfail act low high l)

soit call_switcher konst fail arg low high int_lambda_list =
  soit edges, (cases, actions) =
    as_interval fail low high int_lambda_list dans
  Switcher.zyva edges konst arg cases actions


soit exists_ctx ok ctx =
  List.exists
    (fonction
      | {right=p::_} -> ok p
      | _ -> affirme faux)
    ctx

soit rec list_as_pat = fonction
  | [] -> fatal_error "Matching.list_as_pat"
  | [pat] -> pat
  | pat::rem ->
      {pat avec pat_desc = Tpat_or (pat,list_as_pat rem,None)}


soit rec pat_as_list k = fonction
  | {pat_desc=Tpat_or (p1,p2,_)} ->
      pat_as_list (pat_as_list k p2) p1
  | p -> p::k

(* Extracting interesting patterns *)
exception All

soit rec extract_pat seen k p = filtre p.pat_desc avec
| Tpat_or (p1,p2,_) ->
    soit k1,seen1 = extract_pat seen k p1 dans
    extract_pat seen1 k1 p2
| Tpat_alias (p,_,_) ->
    extract_pat  seen k p
| Tpat_var _|Tpat_any ->
    raise All
| _ ->
    soit q = normalize_pat p dans
    si  List.exists (compat q) seen alors
      k, seen
    sinon
      q::k, q::seen

soit extract_mat seen pss =
  soit r,_ =
    List.fold_left
      (fonc (k,seen) ps -> filtre ps avec
      | p::_ -> extract_pat seen k p
      | _ -> affirme faux)
      ([],seen)
      pss dans
  r



soit complete_pats_constrs = fonction
  | p::_ tel pats ->
      List.map
        (pat_of_constr p)
        (complete_constrs p (List.map get_key_constr pats))
  | _ -> affirme faux


soit mk_res get_key env last_choice idef cant_fail ctx =

  soit env,fail,jumps_fail = filtre last_choice avec
  | [] ->
      env, None, jumps_empty
  | [p] quand group_var p ->
      env,
      Some (Lstaticraise (idef,[])),
      jumps_singleton idef ctx
  | _ ->
      (idef,cant_fail,last_choice)::env,
      None, jumps_empty dans
  soit klist,jumps =
    List.fold_right
      (fonc (i,cant_fail,pats) (klist,jumps) ->
        soit act = Lstaticraise (i,[])
        et pat = list_as_pat pats dans
        soit klist =
          List.fold_right
            (fonc pat klist -> (get_key pat,act)::klist)
            pats klist
        et ctx = si cant_fail alors ctx sinon ctx_lub pat ctx dans
        klist,jumps_add i ctx jumps)
      env ([],jumps_fail) dans
  fail, klist, jumps


(*
     Following two ``failaction'' function compute n, the trap handler
    to jump to in case of failure of elementary tests
*)

soit mk_failaction_neg partial ctx def = filtre partial avec
| Partial ->
    début filtre def avec
    | (_,idef)::_ ->
        Some (Lstaticraise (idef,[])),[],jumps_singleton idef ctx
    | _ ->
       (* Act as Total, this means
          If no appropriate default matrix exists,
          then this switch cannot fail *)
        None, [], jumps_empty
    fin
| Total ->
    None, [], jumps_empty



(* Conforme a l'article et plus simple qu'avant *)
et mk_failaction_pos partial seen ctx defs  =
  si dbg alors début
    prerr_endline "**POS**" ;
    pretty_def defs ;
    ()
  fin ;
  soit rec scan_def env to_test defs = filtre to_test,defs avec
  | ([],_)|(_,[]) ->
      List.fold_left
        (fonc  (klist,jumps) (pats,i)->
          soit action = Lstaticraise (i,[]) dans
          soit klist =
            List.fold_right
              (fonc pat r -> (get_key_constr pat,action)::r)
              pats klist
          et jumps =
            jumps_add i (ctx_lub (list_as_pat pats) ctx) jumps dans
          klist,jumps)
        ([],jumps_empty) env
  | _,(pss,idef)::rem ->
      soit now, later =
        List.partition
          (fonc (p,p_ctx) -> ctx_match p_ctx pss) to_test dans
      filtre now avec
      | [] -> scan_def env to_test rem
      | _  -> scan_def ((List.map fst now,idef)::env) later rem dans

  scan_def
    []
    (List.map
       (fonc pat -> pat, ctx_lub pat ctx)
       (complete_pats_constrs seen))
    defs


soit combine_constant arg cst partial ctx def
    (const_lambda_list, total, pats) =
  soit fail, to_add, local_jumps =
    mk_failaction_neg partial ctx def dans
  soit const_lambda_list = to_add@const_lambda_list dans
  soit lambda1 =
    filtre cst avec
    | Const_int _ ->
        soit int_lambda_list =
          List.map (fonction Const_int n, l -> n,l | _ -> affirme faux)
            const_lambda_list dans
        call_switcher
          lambda_of_int fail arg min_int max_int int_lambda_list
    | Const_char _ ->
        soit int_lambda_list =
          List.map (fonction Const_char c, l -> (Char.code c, l)
            | _ -> affirme faux)
            const_lambda_list dans
        call_switcher
          (fonc i -> Lconst (Const_base (Const_int i)))
          fail arg 0 255 int_lambda_list
    | Const_string _ ->
(* Note as the bytecode compiler may resort to dichotmic search,
   the clauses of strinswitch  are sorted with duplicate removed.
   This partly applies to the native code compiler, which requires
   no duplicates *)   
        soit fail,const_lambda_list = filtre fail avec
        | Some fail -> fail,sort_lambda_list const_lambda_list
        | None ->
            soit cls,(_,lst) = Misc.split_last const_lambda_list dans
            lst,sort_lambda_list cls dans
        soit sw =
          List.map
            (fonc (c,act) -> filtre c avec
            | Const_string (s,_) -> s,act
            | _ -> affirme faux)
            const_lambda_list dans
        Lstringswitch (arg,sw,fail)
    | Const_float _ ->
        make_test_sequence
          fail
          (Pfloatcomp Cneq) (Pfloatcomp Clt)
          arg const_lambda_list
    | Const_int32 _ ->
        make_test_sequence
          fail
          (Pbintcomp(Pint32, Cneq)) (Pbintcomp(Pint32, Clt))
          arg const_lambda_list
    | Const_int64 _ ->
        make_test_sequence
          fail
          (Pbintcomp(Pint64, Cneq)) (Pbintcomp(Pint64, Clt))
          arg const_lambda_list
    | Const_nativeint _ ->
        make_test_sequence
          fail
          (Pbintcomp(Pnativeint, Cneq)) (Pbintcomp(Pnativeint, Clt))
          arg const_lambda_list
  dans lambda1,jumps_union local_jumps total



soit split_cases tag_lambda_list =
  soit rec split_rec = fonction
      [] -> ([], [])
    | (cstr, act) :: rem ->
        soit (consts, nonconsts) = split_rec rem dans
        filtre cstr avec
          Cstr_constant n -> ((n, act) :: consts, nonconsts)
        | Cstr_block n    -> (consts, (n, act) :: nonconsts)
        | _ -> affirme faux dans
  soit const, nonconst = split_rec tag_lambda_list dans
  sort_int_lambda_list const,
  sort_int_lambda_list nonconst


soit combine_constructor arg ex_pat cstr partial ctx def
    (tag_lambda_list, total1, pats) =
  si cstr.cstr_consts < 0 alors début
    (* Special cases for exceptions *)
    soit fail, to_add, local_jumps =
      mk_failaction_neg partial ctx def dans
    soit tag_lambda_list = to_add@tag_lambda_list dans
    soit lambda1 =
      soit default, tests =
        filtre fail avec
        | None ->
            début filtre tag_lambda_list avec
            | (_, act)::rem -> act,rem
            | _ -> affirme faux
            fin
        | Some fail -> fail, tag_lambda_list dans
      List.fold_right
        (fonc (ex, act) rem ->
           affirme(ex = cstr.cstr_tag);
          filtre ex avec
          | Cstr_exception (path, _) ->
              soit slot =
                si cstr.cstr_arity = 0 alors arg
                sinon Lprim(Pfield 0, [arg])
              dans
              Lifthenelse(Lprim(Pintcomp Ceq,
                                [slot;
                                 transl_path ~loc:ex_pat.pat_loc
                                   ex_pat.pat_env path]),
                          act, rem)
          | _ -> affirme faux)
        tests default dans
    lambda1, jumps_union local_jumps total1
  fin sinon début
    (* Regular concrete type *)
    soit ncases = List.length tag_lambda_list
    et nconstrs =  cstr.cstr_consts + cstr.cstr_nonconsts dans
    soit sig_complete = ncases = nconstrs dans
    soit fails,local_jumps =
      si sig_complete alors [],jumps_empty
      sinon
        mk_failaction_pos partial pats ctx def dans

    soit tag_lambda_list = fails @ tag_lambda_list dans
    soit (consts, nonconsts) = split_cases tag_lambda_list dans
    soit lambda1 =
      filtre same_actions tag_lambda_list avec
      | Some act -> act
      | _ ->
          filtre
            (cstr.cstr_consts, cstr.cstr_nonconsts, consts, nonconsts)
          avec
          | (1, 1, [0, act1], [0, act2]) ->
              Lifthenelse(arg, act2, act1)
          | (n,_,_,[])  ->
              call_switcher
                (fonc i -> Lconst (Const_base (Const_int i)))
                None arg 0 (n-1) consts
          | (n, _, _, _) ->
              filtre same_actions nonconsts avec
              | None ->
                  make_switch(arg, {sw_numconsts = cstr.cstr_consts;
                                     sw_consts = consts;
                                     sw_numblocks = cstr.cstr_nonconsts;
                                     sw_blocks = nonconsts;
                                     sw_failaction = None})
              | Some act ->
                  Lifthenelse
                    (Lprim (Pisint, [arg]),
                     call_switcher
                       (fonc i -> Lconst (Const_base (Const_int i)))
                       None arg
                       0 (n-1) consts,
                     act) dans
    lambda1, jumps_union local_jumps total1
  fin

soit make_test_sequence_variant_constant fail arg int_lambda_list =
  soit _, (cases, actions) =
    as_interval fail min_int max_int int_lambda_list dans
  Switcher.test_sequence
    (fonc i -> Lconst (Const_base (Const_int i))) arg cases actions

soit call_switcher_variant_constant fail arg int_lambda_list =
  call_switcher
    (fonc i -> Lconst (Const_base (Const_int i)))
    fail arg min_int max_int int_lambda_list


soit call_switcher_variant_constr fail arg int_lambda_list =
  soit v = Ident.create "variant" dans
  Llet(Alias, v, Lprim(Pfield 0, [arg]),
       call_switcher
         (fonc i -> Lconst (Const_base (Const_int i)))
         fail (Lvar v) min_int max_int int_lambda_list)

soit combine_variant row arg partial ctx def (tag_lambda_list, total1, pats) =
  soit row = Btype.row_repr row dans
  soit num_constr = ref 0 dans
  si row.row_closed alors
    List.iter
      (fonc (_, f) ->
        filtre Btype.row_field_repr f avec
          Rabsent | Reither(vrai, _::_, _, _) -> ()
        | _ -> incr num_constr)
      row.row_fields
  sinon
    num_constr := max_int;
  soit test_int_or_block arg if_int if_block =
    Lifthenelse(Lprim (Pisint, [arg]), if_int, if_block) dans
  soit sig_complete =  List.length tag_lambda_list = !num_constr
  et one_action = same_actions tag_lambda_list dans
  soit fail, to_add, local_jumps =
    si
      sig_complete  || (filtre partial avec Total -> vrai | _ -> faux)
    alors
      None, [], jumps_empty
    sinon
      mk_failaction_neg partial ctx def dans
  soit tag_lambda_list = to_add@tag_lambda_list dans
  soit (consts, nonconsts) = split_cases tag_lambda_list dans
  soit lambda1 = filtre fail, one_action avec
  | None, Some act -> act
  | _,_ ->
      filtre (consts, nonconsts) avec
      | ([n, act1], [m, act2]) quand fail=None ->
          test_int_or_block arg act1 act2
      | (_, []) -> (* One can compare integers and pointers *)
          make_test_sequence_variant_constant fail arg consts
      | ([], _) ->
          soit lam = call_switcher_variant_constr
              fail arg nonconsts dans
          (* One must not dereference integers *)
          début filtre fail avec
          | None -> lam
          | Some fail -> test_int_or_block arg fail lam
          fin
      | (_, _) ->
          soit lam_const =
            call_switcher_variant_constant
              fail arg consts
          et lam_nonconst =
            call_switcher_variant_constr
              fail arg nonconsts dans
          test_int_or_block arg lam_const lam_nonconst
  dans
  lambda1, jumps_union local_jumps total1


soit combine_array arg kind partial ctx def
    (len_lambda_list, total1, pats)  =
  soit fail, to_add, local_jumps = mk_failaction_neg partial  ctx def dans
  soit len_lambda_list = to_add @ len_lambda_list dans
  soit lambda1 =
    soit newvar = Ident.create "len" dans
    soit switch =
      call_switcher
        lambda_of_int
        fail (Lvar newvar)
        0 max_int len_lambda_list dans
    bind
      Alias newvar (Lprim(Parraylength kind, [arg])) switch dans
  lambda1, jumps_union local_jumps total1

(* Insertion of debugging events *)

soit rec event_branch repr lam =
  début filtre lam, repr avec
    (_, None) ->
      lam
  | (Levent(lam', ev), Some r) ->
      incr r;
      Levent(lam', {lev_loc = ev.lev_loc;
                    lev_kind = ev.lev_kind;
                    lev_repr = repr;
                    lev_env = ev.lev_env})
  | (Llet(str, id, lam, body), _) ->
      Llet(str, id, lam, event_branch repr body)
  | Lstaticraise _,_ -> lam
  | (_, Some r) ->
      Printlambda.lambda Format.str_formatter lam ;
      fatal_error
        ("Matching.event_branch: "^Format.flush_str_formatter ())
  fin


(*
   This exception is raised when the compiler cannot produce code
   because control cannot reach the compiled clause,

   Unused is raised initialy in compile_test.

   compile_list (for compiling switch results) catch Unused

   comp_match_handlers (for compililing splitted matches)
   may reraise Unused


*)

exception Unused

soit compile_list compile_fun division =

  soit rec c_rec totals = fonction
  | [] -> [], jumps_unions totals, []
  | (key, cell) :: rem ->
      début filtre cell.ctx avec
      | [] -> c_rec totals rem
      | _  ->
          essaie
            soit (lambda1, total1) = compile_fun cell.ctx cell.pm dans
            soit c_rem, total, new_pats =
              c_rec
                (jumps_map ctx_combine total1::totals) rem dans
            ((key,lambda1)::c_rem), total, (cell.pat::new_pats)
          avec
          | Unused -> c_rec totals rem
      fin dans
  c_rec [] division


soit compile_orhandlers compile_fun lambda1 total1 ctx to_catch =
  soit rec do_rec r total_r = fonction
    | [] -> r,total_r
    | (mat,i,vars,pm)::rem ->
        début essaie
          soit ctx = select_columns mat ctx dans
          soit handler_i, total_i = compile_fun ctx pm dans
          filtre raw_action r avec
          | Lstaticraise (j,args) ->
              si i=j alors
                List.fold_right2 (bind Alias) vars args handler_i,
                jumps_map (ctx_rshift_num (ncols mat)) total_i
              sinon
                do_rec r total_r rem
          | _ ->
              do_rec
                (Lstaticcatch (r,(i,vars), handler_i))
                (jumps_union
                   (jumps_remove i total_r)
                   (jumps_map (ctx_rshift_num (ncols mat)) total_i))
              rem
        avec
        | Unused ->
            do_rec (Lstaticcatch (r, (i,vars), lambda_unit)) total_r rem
        fin dans
  do_rec lambda1 total1 to_catch


soit compile_test compile_fun partial divide combine ctx to_match =
  soit division = divide ctx to_match dans
  soit c_div = compile_list compile_fun division dans
  filtre c_div avec
  | [],_,_ ->
     début filtre mk_failaction_neg partial ctx to_match.default avec
     | None,_,_ -> raise Unused
     | Some l,_,total -> l,total
     fin
  | _ ->
      combine ctx to_match.default c_div

(* Attempt to avoid some useless bindings by lowering them *)

(* Approximation of v present in lam *)
soit rec approx_present v = fonction
  | Lconst _ -> faux
  | Lstaticraise (_,args) ->
      List.exists (fonc lam -> approx_present v lam) args
  | Lprim (_,args) ->
      List.exists (fonc lam -> approx_present v lam) args
  | Llet (Alias, _, l1, l2) ->
      approx_present v l1 || approx_present v l2
  | Lvar vv -> Ident.same v vv
  | _ -> vrai

soit string_of_lam lam =
  Printlambda.lambda Format.str_formatter lam ;
  Format.flush_str_formatter ()

soit rec lower_bind v arg lam = filtre lam avec
| Lifthenelse (cond, ifso, ifnot) ->
    soit pcond = approx_present v cond
    et pso = approx_present v ifso
    et pnot = approx_present v ifnot dans
    début filtre pcond, pso, pnot avec
    | faux, faux, faux -> lam
    | faux, vrai, faux ->
        Lifthenelse (cond, lower_bind v arg ifso, ifnot)
    | faux, faux, vrai ->
        Lifthenelse (cond, ifso, lower_bind v arg ifnot)
    | _,_,_ -> bind Alias v arg lam
    fin
| Lswitch (ls,({sw_consts=[i,act] ; sw_blocks = []} tel sw))
    quand not (approx_present v ls) ->
      Lswitch (ls, {sw avec sw_consts = [i,lower_bind v arg act]})
| Lswitch (ls,({sw_consts=[] ; sw_blocks = [i,act]} tel sw))
    quand not (approx_present v ls) ->
      Lswitch (ls, {sw avec sw_blocks = [i,lower_bind v arg act]})
| Llet (Alias, vv, lv, l) ->
    si approx_present v lv alors
      bind Alias v arg lam
    sinon
      Llet (Alias, vv, lv, lower_bind v arg l)
| _ ->
    bind Alias v arg lam

soit bind_check str v arg lam = filtre str,arg avec
| _, Lvar _ ->bind str v arg lam
| Alias,_ -> lower_bind v arg lam
| _,_     -> bind str v arg lam

soit comp_exit ctx m = filtre m.default avec
| (_,i)::_ -> Lstaticraise (i,[]), jumps_singleton i ctx
| _        -> fatal_error "Matching.comp_exit"



soit rec comp_match_handlers comp_fun partial ctx arg first_match next_matchs =
  filtre next_matchs avec
  | [] -> comp_fun partial ctx arg first_match
  | rem ->
      soit rec c_rec body total_body = fonction
        | [] -> body, total_body
        (* Hum, -1 meant never taken
        | (-1,pm)::rem -> c_rec body total_body rem *)
        | (i,pm)::rem ->
            soit ctx_i,total_rem = jumps_extract i total_body dans
            début filtre ctx_i avec
            | [] -> c_rec body total_body rem
            | _ ->
                essaie
                  soit li,total_i =
                    comp_fun
                      (filtre rem avec [] -> partial | _ -> Partial)
                      ctx_i arg pm dans
                  c_rec
                    (Lstaticcatch (body,(i,[]),li))
                    (jumps_union total_i total_rem)
                    rem
                avec
                | Unused ->
                    c_rec (Lstaticcatch (body,(i,[]),lambda_unit))
                      total_rem  rem
            fin dans
   essaie
      soit first_lam,total = comp_fun Partial ctx arg first_match dans
      c_rec first_lam total rem
   avec Unused -> filtre next_matchs avec
   | [] -> raise Unused
   | (_,x)::xs ->  comp_match_handlers comp_fun partial ctx arg x xs

(* To find reasonable names for variables *)

soit rec name_pattern default = fonction
    (pat :: patl, action) :: rem ->
      début filtre pat.pat_desc avec
        Tpat_var (id, _) -> id
      | Tpat_alias(p, id, _) -> id
      | _ -> name_pattern default rem
      fin
  | _ -> Ident.create default

soit arg_to_var arg cls = filtre arg avec
| Lvar v -> v,arg
| _ ->
    soit v = name_pattern "match" cls dans
    v,Lvar v


(*
  The main compilation function.
   Input:
      repr=used for inserting debug events
      partial=exhaustiveness information from Parmatch
      ctx=a context
      m=a pattern matching

   Output: a lambda term, a jump summary {..., exit number -> context, .. }
*)

soit rec compile_match repr partial ctx m = filtre m avec
| { cases = [] } -> comp_exit ctx m
| { cases = ([], action) :: rem } ->
    si is_guarded action alors début
      soit (lambda, total) =
        compile_match None partial ctx { m avec cases = rem } dans
      event_branch repr (patch_guarded lambda action), total
    fin sinon
      (event_branch repr action, jumps_empty)
| { args = (arg, str)::argl } ->
    soit v,newarg = arg_to_var arg m.cases dans
    soit first_match,rem =
      split_precompile (Some v)
        { m avec args = (newarg, Alias) :: argl } dans
    soit (lam, total) =
      comp_match_handlers
        ((si dbg alors do_compile_matching_pr sinon do_compile_matching) repr)
        partial ctx newarg first_match rem dans
    bind_check str v arg lam, total
| _ -> affirme faux


(* verbose version of do_compile_matching, for debug *)

et do_compile_matching_pr repr partial ctx arg x =
  prerr_string "COMPILE: " ;
  prerr_endline (filtre partial avec Partial -> "Partial" | Total -> "Total") ;
  prerr_endline "MATCH" ;
  pretty_precompiled x ;
  prerr_endline "CTX" ;
  pretty_ctx ctx ;
  soit (_, jumps) tel r =  do_compile_matching repr partial ctx arg x dans
  prerr_endline "JUMPS" ;
  pretty_jumps jumps ;
  r

et do_compile_matching repr partial ctx arg pmh = filtre pmh avec
| Pm pm ->
  soit pat = what_is_cases pm.cases dans
  début filtre pat.pat_desc avec
  | Tpat_any ->
      compile_no_test
        divide_var ctx_rshift repr partial ctx pm
  | Tpat_tuple patl ->
      compile_no_test
        (divide_tuple (List.length patl) (normalize_pat pat)) ctx_combine
        repr partial ctx pm
  | Tpat_record ((_, lbl,_)::_,_) ->
      compile_no_test
        (divide_record lbl.lbl_all (normalize_pat pat))
        ctx_combine repr partial ctx pm
  | Tpat_constant cst ->
      compile_test
        (compile_match repr partial) partial
        divide_constant
        (combine_constant arg cst partial)
        ctx pm
  | Tpat_construct (_, cstr, _) ->
      compile_test
        (compile_match repr partial) partial
        divide_constructor (combine_constructor arg pat cstr partial)
        ctx pm
  | Tpat_array _ ->
      soit kind = Typeopt.array_pattern_kind pat dans
      compile_test (compile_match repr partial) partial
        (divide_array kind) (combine_array arg kind partial)
        ctx pm
  | Tpat_lazy _ ->
      compile_no_test
        (divide_lazy (normalize_pat pat))
        ctx_combine repr partial ctx pm
  | Tpat_variant(lab, _, row) ->
      compile_test (compile_match repr partial) partial
        (divide_variant !row)
        (combine_variant !row arg partial)
        ctx pm
  | _ -> affirme faux
  fin
| PmVar {inside=pmh ; var_arg=arg} ->
    soit lam, total =
      do_compile_matching repr partial (ctx_lshift ctx) arg pmh dans
    lam, jumps_map ctx_rshift total
| PmOr {body=body ; handlers=handlers} ->
    soit lam, total = compile_match repr partial ctx body dans
    compile_orhandlers (compile_match repr partial) lam total ctx handlers

et compile_no_test divide up_ctx repr partial ctx to_match =
  soit {pm=this_match ; ctx=this_ctx } = divide ctx to_match dans
  soit lambda,total = compile_match repr partial this_ctx this_match dans
  lambda, jumps_map up_ctx total




(* The entry points *)

(*
   If there is a guard in a matching or a lazy pattern,
   then set exhaustiveness info to Partial.
   (because of side effects, assume the worst).

   Notice that exhaustiveness information is trusted by the compiler,
   that is, a match flagged as Total should not fail at runtime.
   More specifically, for instance if match y with x::_ -> x uis flagged
   total (as it happens during JoCaml compilation) then y cannot be []
   at runtime. As a consequence, the static Total exhaustiveness information
   have to to be downgraded to Partial, in the dubious cases where guards
   or lazy pattern execute arbitrary code that may perform side effects
   and change the subject values.
LM:
   Lazy pattern was PR #5992, initial patch by lwp25.
   I have  generalized teh patch, so as to also find mutable fields.
*)

soit find_in_pat pred =
  soit rec find_rec p =
    pred p.pat_desc ||
    début filtre p.pat_desc avec
    | Tpat_alias (p,_,_) | Tpat_variant (_,Some p,_) | Tpat_lazy p ->
        find_rec p
    | Tpat_tuple ps|Tpat_construct (_,_,ps) | Tpat_array ps ->
        List.exists find_rec ps
    | Tpat_record (lpats,_) ->
        List.exists
          (fonc (_, _, p) -> find_rec p)
          lpats
    | Tpat_or (p,q,_) ->
        find_rec p || find_rec q
    | Tpat_constant _ | Tpat_var _
    | Tpat_any | Tpat_variant (_,None,_) -> faux
  fin dans
  find_rec

soit is_lazy_pat = fonction
  | Tpat_lazy _ -> vrai
  | Tpat_alias _ | Tpat_variant _ | Tpat_record _
  | Tpat_tuple _|Tpat_construct _ | Tpat_array _
  | Tpat_or _ | Tpat_constant _ | Tpat_var _ | Tpat_any
      -> faux

soit is_lazy p = find_in_pat is_lazy_pat p

soit have_mutable_field p = filtre p avec
| Tpat_record (lps,_) ->
    List.exists
      (fonc (_,lbl,_) ->
        filtre lbl.Types.lbl_mut avec
        | Mutable -> vrai
        | Immutable -> faux)
      lps
| Tpat_alias _ | Tpat_variant _ | Tpat_lazy _
| Tpat_tuple _|Tpat_construct _ | Tpat_array _
| Tpat_or _
| Tpat_constant _ | Tpat_var _ | Tpat_any
  -> faux

soit is_mutable p = find_in_pat have_mutable_field p

(* Downgrade Total when
   1. Matching accesses some mutable fields;
   2. And there are  guards or lazy patterns.
*)

soit check_partial is_mutable is_lazy pat_act_list = fonction
  | Partial -> Partial
  | Total ->
      si
        List.exists
          (fonc (pats, lam) ->
            is_mutable pats && (is_guarded lam || is_lazy pats))
          pat_act_list
      alors Partial
      sinon Total

soit check_partial_list =
  check_partial (List.exists is_mutable) (List.exists is_lazy)
soit check_partial = check_partial is_mutable is_lazy

(* have toplevel handler when appropriate *)

soit start_ctx n = [{left=[] ; right = omegas n}]

soit check_total total lambda i handler_fun =
  si jumps_is_empty total alors
    lambda
  sinon début
    Lstaticcatch(lambda, (i,[]), handler_fun())
  fin

soit compile_matching loc repr handler_fun arg pat_act_list partial =
  soit partial = check_partial pat_act_list partial dans
  filtre partial avec
  | Partial ->
      soit raise_num = next_raise_count () dans
      soit pm =
        { cases = List.map (fonc (pat, act) -> ([pat], act)) pat_act_list;
          args = [arg, Strict] ;
          default = [[[omega]],raise_num]} dans
      début essaie
        soit (lambda, total) = compile_match repr partial (start_ctx 1) pm dans
        check_total total lambda raise_num handler_fun
      avec
      | Unused -> affirme faux (* ; handler_fun() *)
      fin
  | Total ->
      soit pm =
        { cases = List.map (fonc (pat, act) -> ([pat], act)) pat_act_list;
          args = [arg, Strict] ;
          default = []} dans
      soit (lambda, total) = compile_match repr partial (start_ctx 1) pm dans
      affirme (jumps_is_empty total) ;
      lambda


soit partial_function loc () =
  (* [Location.get_pos_info] is too expensive *)
  soit (fname, line, char) = Location.get_pos_info loc.Location.loc_start dans
  Lprim(Praise Raise_regular, [Lprim(Pmakeblock(0, Immutable),
          [transl_normal_path Predef.path_match_failure;
           Lconst(Const_block(0,
              [Const_base(Const_string (fname, None));
               Const_base(Const_int line);
               Const_base(Const_int char)]))])])

soit for_function loc repr param pat_act_list partial =
  compile_matching loc repr (partial_function loc) param pat_act_list partial

(* In the following two cases, exhaustiveness info is not available! *)
soit for_trywith param pat_act_list =
  compile_matching Location.none None
    (fonc () -> Lprim(Praise Raise_reraise, [param]))
    param pat_act_list Partial

soit for_let loc param pat body =
  compile_matching loc None (partial_function loc) param [pat, body] Partial

(* Handling of tupled functions and matchings *)

(* Easy case since variables are available *)
soit for_tupled_function loc paraml pats_act_list partial =
  soit partial = check_partial_list pats_act_list partial dans
  soit raise_num = next_raise_count () dans
  soit omegas = [List.map (fonc _ -> omega) paraml] dans
  soit pm =
    { cases = pats_act_list;
      args = List.map (fonc id -> (Lvar id, Strict)) paraml ;
      default = [omegas,raise_num]
    } dans
  essaie
    soit (lambda, total) = compile_match None partial
        (start_ctx (List.length paraml)) pm dans
    check_total total lambda raise_num (partial_function loc)
  avec
  | Unused -> partial_function loc ()



soit flatten_pattern size p = filtre p.pat_desc avec
| Tpat_tuple args -> args
| Tpat_any -> omegas size
| _ -> raise Cannot_flatten

soit rec flatten_pat_line size p k = filtre p.pat_desc avec
| Tpat_any ->  omegas size::k
| Tpat_tuple args -> args::k
| Tpat_or (p1,p2,_) ->  flatten_pat_line size p1 (flatten_pat_line size p2 k)
| Tpat_alias (p,_,_) -> (* Note: if this 'as' pat is here, then this is a
                           useless binding, solves PR #3780 *)
    flatten_pat_line size p k
| _ -> fatal_error "Matching.flatten_pat_line"

soit flatten_cases size cases =
  List.map
    (fonc (ps,action) -> filtre ps avec
    | [p] -> flatten_pattern size p,action
    | _ -> fatal_error "Matching.flatten_case")
    cases

soit flatten_matrix size pss =
  List.fold_right
    (fonc ps r -> filtre ps avec
    | [p] -> flatten_pat_line size p r
    | _   -> fatal_error "Matching.flatten_matrix")
    pss []

soit flatten_def size def =
  List.map
    (fonc (pss,i) -> flatten_matrix size pss,i)
    def

soit flatten_pm size args pm =
    {args = args ; cases = flatten_cases size pm.cases ;
     default = flatten_def size pm.default}


soit flatten_precompiled size args  pmh = filtre pmh avec
| Pm pm -> Pm (flatten_pm size args pm)
| PmOr {body=b ; handlers=hs ; or_matrix=m} ->
    PmOr
      {body=flatten_pm size args b ;
       handlers=
         List.map
          (fonc (mat,i,vars,pm) -> flatten_matrix size mat,i,vars,pm)
          hs ;
       or_matrix=flatten_matrix size m ;}
| PmVar _ -> affirme faux

(*
   compiled_flattened is a ``comp_fun'' argument to comp_match_handlers.
   Hence it needs a fourth argument, which it ignores
*)

soit compile_flattened repr partial ctx _ pmh = filtre pmh avec
| Pm pm -> compile_match repr partial ctx pm
| PmOr {body=b ; handlers=hs} ->
    soit lam, total = compile_match repr partial ctx b dans
    compile_orhandlers (compile_match repr partial) lam total ctx hs
| PmVar _ -> affirme faux

soit do_for_multiple_match loc paraml pat_act_list partial =
  soit repr = None dans
  soit partial = check_partial pat_act_list partial dans
  soit raise_num,pm1 =
    filtre partial avec
    | Partial ->
        soit raise_num = next_raise_count () dans
        raise_num,
        { cases = List.map (fonc (pat, act) -> ([pat], act)) pat_act_list;
          args = [Lprim(Pmakeblock(0, Immutable), paraml), Strict] ;
          default = [[[omega]],raise_num] }
    | _ ->
        -1,
        { cases = List.map (fonc (pat, act) -> ([pat], act)) pat_act_list;
          args = [Lprim(Pmakeblock(0, Immutable), paraml), Strict] ;
          default = [] } dans

  essaie
    essaie
(* Once for checking that compilation is possible *)
      soit next, nexts = split_precompile None pm1 dans

      soit size = List.length paraml
      et idl = List.map (fonc _ -> Ident.create "match") paraml dans
      soit args =  List.map (fonc id -> Lvar id, Alias) idl dans

      soit flat_next = flatten_precompiled size args next
      et flat_nexts =
        List.map
          (fonc (e,pm) ->  e,flatten_precompiled size args pm)
          nexts dans

      soit lam, total =
        comp_match_handlers
          (compile_flattened repr)
          partial (start_ctx size) () flat_next flat_nexts dans
      List.fold_right2 (bind Strict) idl paraml
        (filtre partial avec
        | Partial ->
            check_total total lam raise_num (partial_function loc)
        | Total ->
            affirme (jumps_is_empty total) ;
            lam)
    avec Cannot_flatten ->
      soit (lambda, total) = compile_match None partial (start_ctx 1) pm1 dans
      début filtre partial avec
      | Partial ->
          check_total total lambda raise_num (partial_function loc)
      | Total ->
          affirme (jumps_is_empty total) ;
          lambda
      fin
  avec Unused ->
    affirme faux (* ; partial_function loc () *)

(* #PR4828: Believe it or not, the 'paraml' argument below
   may not be side effect free. *)

soit arg_to_var arg cls = filtre arg avec
| Lvar v -> v,arg
| _ ->
    soit v = name_pattern "match" cls dans
    v,Lvar v


soit param_to_var param = filtre param avec
| Lvar v -> v,None
| _ -> Ident.create "match",Some param

soit bind_opt (v,eo) k = filtre eo avec
| None -> k
| Some e ->  Lambda.bind Strict v e k

soit for_multiple_match loc paraml pat_act_list partial =
  soit v_paraml = List.map param_to_var paraml dans
  soit paraml = List.map (fonc (v,_) -> Lvar v) v_paraml dans
  List.fold_right bind_opt v_paraml
    (do_for_multiple_match loc paraml pat_act_list partial)
