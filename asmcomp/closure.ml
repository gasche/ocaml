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

(* Introduction of closures, uncurrying, recognition of direct calls *)

ouvre Misc
ouvre Asttypes
ouvre Primitive
ouvre Lambda
ouvre Switch
ouvre Clambda

(* Auxiliaries for compiling functions *)

soit rec split_list n l =
  si n <= 0 alors ([], l) sinon début
    filtre l avec
      [] -> fatal_error "Closure.split_list"
    | a::l -> soit (l1, l2) = split_list (n-1) l dans (a::l1, l2)
  fin

soit rec build_closure_env env_param pos = fonction
    [] -> Tbl.empty
  | id :: rem ->
      Tbl.add id (Uprim(Pfield pos, [Uvar env_param], Debuginfo.none))
              (build_closure_env env_param (pos+1) rem)

(* Auxiliary for accessing globals.  We change the name of the global
   to the name of the corresponding asm symbol.  This is done here
   and no longer in Cmmgen so that approximations stored in .cmx files
   contain the right names if the -for-pack option is active. *)

soit getglobal id =
  Uprim(Pgetglobal (Ident.create_persistent (Compilenv.symbol_for_global id)),
        [], Debuginfo.none)

(* Check if a variable occurs in a [clambda] term. *)

soit occurs_var var u =
  soit rec occurs = fonction
      Uvar v -> v = var
    | Uconst _ -> faux
    | Udirect_apply(lbl, args, _) -> List.exists occurs args
    | Ugeneric_apply(funct, args, _) -> occurs funct || List.exists occurs args
    | Uclosure(fundecls, clos) -> List.exists occurs clos
    | Uoffset(u, ofs) -> occurs u
    | Ulet(id, def, body) -> occurs def || occurs body
    | Uletrec(decls, body) ->
        List.exists (fonc (id, u) -> occurs u) decls || occurs body
    | Uprim(p, args, _) -> List.exists occurs args
    | Uswitch(arg, s) ->
        occurs arg ||
        occurs_array s.us_actions_consts || occurs_array s.us_actions_blocks
    | Ustringswitch(arg,sw,d) ->
        occurs arg ||
        List.exists (fonc (_,e) -> occurs e) sw ||
        occurs d
    | Ustaticfail (_, args) -> List.exists occurs args
    | Ucatch(_, _, body, hdlr) -> occurs body || occurs hdlr
    | Utrywith(body, exn, hdlr) -> occurs body || occurs hdlr
    | Uifthenelse(cond, ifso, ifnot) ->
        occurs cond || occurs ifso || occurs ifnot
    | Usequence(u1, u2) -> occurs u1 || occurs u2
    | Uwhile(cond, body) -> occurs cond || occurs body
    | Ufor(id, lo, hi, dir, body) -> occurs lo || occurs hi || occurs body
    | Uassign(id, u) -> id = var || occurs u
    | Usend(_, met, obj, args, _) ->
        occurs met || occurs obj || List.exists occurs args
  et occurs_array a =
    essaie
      pour i = 0 à Array.length a - 1 faire
        si occurs a.(i) alors raise Exit
      fait;
      faux
    avec Exit ->
      vrai
  dans occurs u

(* Split a function with default parameters into a wrapper and an
   inner function.  The wrapper fills in missing optional parameters
   with their default value and tail-calls the inner function.  The
   wrapper can then hopefully be inlined on most call sites to avoid
   the overhead associated with boxing an optional argument with a
   'Some' constructor, only to deconstruct it immediately in the
   function's body. *)

soit split_default_wrapper fun_id kind params body =
  soit rec aux map = fonction
    | Llet(Strict, id, (Lifthenelse(Lvar optparam, _, _) tel def), rest) quand
        Ident.name optparam = "*opt*" && List.mem optparam params
          && not (List.mem_assoc optparam map)
      ->
        soit wrapper_body, inner = aux ((optparam, id) :: map) rest dans
        Llet(Strict, id, def, wrapper_body), inner
    | _ quand map = [] -> raise Exit
    | body ->
        (* Check that those *opt* identifiers don't appear in the remaining
           body. This should not appear, but let's be on the safe side. *)
        soit fv = Lambda.free_variables body dans
        List.iter (fonc (id, _) -> si IdentSet.mem id fv alors raise Exit) map;

        soit inner_id = Ident.create (Ident.name fun_id ^ "_inner") dans
        soit map_param p = essaie List.assoc p map avec Not_found -> p dans
        soit args = List.map (fonc p -> Lvar (map_param p)) params dans
        soit wrapper_body = Lapply (Lvar inner_id, args, Location.none) dans

        soit inner_params = List.map map_param params dans
        soit new_ids = List.map Ident.rename inner_params dans
        soit subst = List.fold_left2
            (fonc s id new_id ->
               Ident.add id (Lvar new_id) s)
            Ident.empty inner_params new_ids
        dans
        soit body = Lambda.subst_lambda subst body dans
        soit inner_fun = Lfunction(Curried, new_ids, body) dans
        (wrapper_body, (inner_id, inner_fun))
  dans
  essaie
    soit wrapper_body, inner = aux [] body dans
    [(fun_id, Lfunction(kind, params, wrapper_body)); inner]
  avec Exit ->
    [(fun_id, Lfunction(kind, params, body))]


(* Determine whether the estimated size of a clambda term is below
   some threshold *)

soit prim_size prim args =
  filtre prim avec
    Pidentity -> 0
  | Pgetglobal id -> 1
  | Psetglobal id -> 1
  | Pmakeblock(tag, mut) -> 5 + List.length args
  | Pfield f -> 1
  | Psetfield(f, isptr) -> si isptr alors 4 sinon 1
  | Pfloatfield f -> 1
  | Psetfloatfield f -> 1
  | Pduprecord _ -> 10 + List.length args
  | Pccall p -> (si p.prim_alloc alors 10 sinon 4) + List.length args
  | Praise _ -> 4
  | Pstringlength -> 5
  | Pstringrefs | Pstringsets -> 6
  | Pmakearray kind -> 5 + List.length args
  | Parraylength kind -> si kind = Pgenarray alors 6 sinon 2
  | Parrayrefu kind -> si kind = Pgenarray alors 12 sinon 2
  | Parraysetu kind -> si kind = Pgenarray alors 16 sinon 4
  | Parrayrefs kind -> si kind = Pgenarray alors 18 sinon 8
  | Parraysets kind -> si kind = Pgenarray alors 22 sinon 10
  | Pbittest -> 3
  | Pbigarrayref(_, ndims, _, _) -> 4 + ndims * 6
  | Pbigarrayset(_, ndims, _, _) -> 4 + ndims * 6
  | _ -> 2 (* arithmetic and comparisons *)

(* Very raw approximation of switch cost *)

soit lambda_smaller lam threshold =
  soit size = ref 0 dans
  soit rec lambda_size lam =
    si !size > threshold alors raise Exit;
    filtre lam avec
      Uvar v -> ()
    | Uconst _ -> incr size
    | Udirect_apply(fn, args, _) ->
        size := !size + 4; lambda_list_size args
    | Ugeneric_apply(fn, args, _) ->
        size := !size + 6; lambda_size fn; lambda_list_size args
    | Uclosure(defs, vars) ->
        raise Exit (* inlining would duplicate function definitions *)
    | Uoffset(lam, ofs) ->
        incr size; lambda_size lam
    | Ulet(id, lam, body) ->
        lambda_size lam; lambda_size body
    | Uletrec(bindings, body) ->
        raise Exit (* usually too large *)
    | Uprim(prim, args, _) ->
        size := !size + prim_size prim args;
        lambda_list_size args
    | Uswitch(lam, cases) ->
        si Array.length cases.us_actions_consts > 1 alors size := !size + 5 ;
        si Array.length cases.us_actions_blocks > 1 alors size := !size + 5 ;
        lambda_size lam;
        lambda_array_size cases.us_actions_consts ;
        lambda_array_size cases.us_actions_blocks
    | Ustringswitch (lam,sw,d) ->
        lambda_size lam ;
       (* as ifthenelse *)
        List.iter
          (fonc (_,lam) ->
            size := !size+2 ;
            lambda_size lam)
          sw ;
        lambda_size d
    | Ustaticfail (_,args) -> lambda_list_size args
    | Ucatch(_, _, body, handler) ->
        incr size; lambda_size body; lambda_size handler
    | Utrywith(body, id, handler) ->
        size := !size + 8; lambda_size body; lambda_size handler
    | Uifthenelse(cond, ifso, ifnot) ->
        size := !size + 2;
        lambda_size cond; lambda_size ifso; lambda_size ifnot
    | Usequence(lam1, lam2) ->
        lambda_size lam1; lambda_size lam2
    | Uwhile(cond, body) ->
        size := !size + 2; lambda_size cond; lambda_size body
    | Ufor(id, low, high, dir, body) ->
        size := !size + 4; lambda_size low; lambda_size high; lambda_size body
    | Uassign(id, lam) ->
        incr size;  lambda_size lam
    | Usend(_, met, obj, args, _) ->
        size := !size + 8;
        lambda_size met; lambda_size obj; lambda_list_size args
  et lambda_list_size l = List.iter lambda_size l
  et lambda_array_size a = Array.iter lambda_size a dans
  essaie
    lambda_size lam; !size <= threshold
  avec Exit ->
    faux

(* Check if a clambda term is ``pure'',
   that is without side-effects *and* not containing function definitions *)

soit rec is_pure_clambda = fonction
    Uvar v -> vrai
  | Uconst _ -> vrai
  | Uprim((Psetglobal _ | Psetfield _ | Psetfloatfield _ | Pduprecord _ |
           Pccall _ | Praise _ | Poffsetref _ | Pstringsetu | Pstringsets |
           Parraysetu _ | Parraysets _ | Pbigarrayset _), _, _) -> faux
  | Uprim(p, args, _) -> List.for_all is_pure_clambda args
  | _ -> faux

(* Simplify primitive operations on integers *)

soit make_const c = (Uconst c, Value_const c)

soit make_const_int n = make_const (Uconst_int n)
soit make_const_ptr n = make_const (Uconst_ptr n)
soit make_const_bool b = make_const_ptr(si b alors 1 sinon 0)
soit make_comparison cmp (x: int) (y: int) =
  make_const_bool
    (filtre cmp avec
       Ceq -> x = y
     | Cneq -> x <> y
     | Clt -> x < y
     | Cgt -> x > y
     | Cle -> x <= y
     | Cge -> x >= y)

soit simplif_int_prim_pure p (args, approxs) dbg =
  filtre approxs avec
    [Value_const (Uconst_int x)] ->
      début filtre p avec
        Pidentity -> make_const_int x
      | Pnegint -> make_const_int (-x)
      | Pbswap16 ->
         make_const_int (((x etl 0xff) dgl 8) oul
                         ((x etl 0xff00) ddl 8))
      | Poffsetint y -> make_const_int (x + y)
      | _ -> (Uprim(p, args, dbg), Value_unknown)
      fin
  | [Value_const (Uconst_int x); Value_const (Uconst_int y)] ->
      début filtre p avec
        Paddint -> make_const_int(x + y)
      | Psubint -> make_const_int(x - y)
      | Pmulint -> make_const_int(x * y)
      | Pdivint quand y <> 0 -> make_const_int(x / y)
      | Pmodint quand y <> 0 -> make_const_int(x mod y)
      | Pandint -> make_const_int(x etl y)
      | Porint -> make_const_int(x oul y)
      | Pxorint -> make_const_int(x ouxl y)
      | Plslint -> make_const_int(x dgl y)
      | Plsrint -> make_const_int(x ddl y)
      | Pasrint -> make_const_int(x dda y)
      | Pintcomp cmp -> make_comparison cmp x y
      | _ -> (Uprim(p, args, dbg), Value_unknown)
      fin
  | [Value_const (Uconst_ptr x)] ->
      début filtre p avec
        Pidentity -> make_const_ptr x
      | Pnot -> make_const_bool(x = 0)
      | Pisint -> make_const_bool vrai
      | Pctconst c ->
          début
            filtre c avec
            | Big_endian -> make_const_bool Arch.big_endian
            | Word_size -> make_const_int (8*Arch.size_int)
            | Ostype_unix -> make_const_bool (Sys.os_type = "Unix")
            | Ostype_win32 -> make_const_bool (Sys.os_type = "Win32")
            | Ostype_cygwin -> make_const_bool (Sys.os_type = "Cygwin")
          fin
      | _ -> (Uprim(p, args, dbg), Value_unknown)
      fin
  | [Value_const (Uconst_ptr x); Value_const (Uconst_ptr y)] ->
      début filtre p avec
        Psequand -> make_const_bool(x <> 0 && y <> 0)
      | Psequor  -> make_const_bool(x <> 0 || y <> 0)
      | Pintcomp cmp -> make_comparison cmp x y
      | _ -> (Uprim(p, args, dbg), Value_unknown)
      fin
  | [Value_const (Uconst_ptr x); Value_const (Uconst_int y)] ->
      début filtre p avec
      | Pintcomp cmp -> make_comparison cmp x y
      | _ -> (Uprim(p, args, dbg), Value_unknown)
      fin
  | [Value_const (Uconst_int x); Value_const (Uconst_ptr y)] ->
      début filtre p avec
      | Pintcomp cmp -> make_comparison cmp x y
      | _ -> (Uprim(p, args, dbg), Value_unknown)
      fin
  | _ ->
      (Uprim(p, args, dbg), Value_unknown)


soit field_approx n = fonction
  | Value_tuple a quand n < Array.length a -> a.(n)
  | Value_const (Uconst_ref(_, Uconst_block(_, l))) quand n < List.length l ->
      Value_const (List.nth l n)
  | _ -> Value_unknown

soit simplif_prim_pure p (args, approxs) dbg =
  filtre p, args, approxs avec
  | Pmakeblock(tag, Immutable), _, _ ->
      soit field = fonction
        | Value_const c -> c
        | _ -> raise Exit
      dans
      début essaie
        soit cst = Uconst_block (tag, List.map field approxs) dans
        soit name =
          Compilenv.new_structured_constant cst ~shared:vrai
        dans
        make_const (Uconst_ref (name, cst))
      avec Exit ->
        (Uprim(p, args, dbg), Value_tuple (Array.of_list approxs))
      fin
  | Pfield n, _, [ Value_const(Uconst_ref(_, Uconst_block(_, l))) ]
    quand n < List.length l ->
      make_const (List.nth l n)

  | Pfield n, [ Uprim(Pmakeblock _, ul, _) ], [approx] ->
      affirme(n < List.length ul);
      List.nth ul n, field_approx n approx

  | Pstringlength, _, [ Value_const(Uconst_ref(_, Uconst_string s)) ]
    ->
      make_const_int (String.length s)

  | _ ->
      simplif_int_prim_pure p (args, approxs) dbg

soit simplif_prim p (args, approxs tel args_approxs) dbg =
  si List.for_all is_pure_clambda args
  alors simplif_prim_pure p args_approxs dbg
  sinon
    (* XXX : always return the same approxs as simplif_prim_pure? *)
    soit approx =
      filtre p avec
      | Pmakeblock(_, Immutable) ->
          Value_tuple (Array.of_list approxs)
      | _ ->
          Value_unknown
    dans
    (Uprim(p, args, dbg), approx)

(* Substitute variables in a [ulambda] term (a body of an inlined function)
   and perform some more simplifications on integer primitives.
   Also perform alpha-conversion on let-bound identifiers to avoid
   clashes with locally-generated identifiers.
   The variables must not be assigned in the term.
   This is used to substitute "trivial" arguments for parameters
   during inline expansion, and also for the translation of let rec
   over functions. *)

soit approx_ulam = fonction
    Uconst c -> Value_const c
  | _ -> Value_unknown

soit rec substitute sb ulam =
  filtre ulam avec
    Uvar v ->
      début essaie Tbl.find v sb avec Not_found -> ulam fin
  | Uconst _ -> ulam
  | Udirect_apply(lbl, args, dbg) ->
      Udirect_apply(lbl, List.map (substitute sb) args, dbg)
  | Ugeneric_apply(fn, args, dbg) ->
      Ugeneric_apply(substitute sb fn, List.map (substitute sb) args, dbg)
  | Uclosure(defs, env) ->
      (* Question: should we rename function labels as well?  Otherwise,
         there is a risk that function labels are not globally unique.
         This should not happen in the current system because:
         - Inlined function bodies contain no Uclosure nodes
           (cf. function [lambda_smaller])
         - When we substitute offsets for idents bound by let rec
           in [close], case [Lletrec], we discard the original
           let rec body and use only the substituted term. *)
      Uclosure(defs, List.map (substitute sb) env)
  | Uoffset(u, ofs) -> Uoffset(substitute sb u, ofs)
  | Ulet(id, u1, u2) ->
      soit id' = Ident.rename id dans
      Ulet(id', substitute sb u1, substitute (Tbl.add id (Uvar id') sb) u2)
  | Uletrec(bindings, body) ->
      soit bindings1 =
        List.map (fonc (id, rhs) -> (id, Ident.rename id, rhs)) bindings dans
      soit sb' =
        List.fold_right
          (fonc (id, id', _) s -> Tbl.add id (Uvar id') s)
          bindings1 sb dans
      Uletrec(
        List.map (fonc (id, id', rhs) -> (id', substitute sb' rhs)) bindings1,
        substitute sb' body)
  | Uprim(p, args, dbg) ->
      soit sargs = List.map (substitute sb) args dans
      soit (res, _) = simplif_prim p (sargs, List.map approx_ulam sargs) dbg dans
      res
  | Uswitch(arg, sw) ->
      Uswitch(substitute sb arg,
              { sw avec
                us_actions_consts =
                  Array.map (substitute sb) sw.us_actions_consts;
                us_actions_blocks =
                  Array.map (substitute sb) sw.us_actions_blocks;
               })
  | Ustringswitch(arg,sw,d) ->
      Ustringswitch
        (substitute sb arg,
         List.map (fonc (s,act) -> s,substitute sb act) sw,
         substitute sb d)
  | Ustaticfail (nfail, args) ->
      Ustaticfail (nfail, List.map (substitute sb) args)
  | Ucatch(nfail, ids, u1, u2) ->
      Ucatch(nfail, ids, substitute sb u1, substitute sb u2)
  | Utrywith(u1, id, u2) ->
      soit id' = Ident.rename id dans
      Utrywith(substitute sb u1, id', substitute (Tbl.add id (Uvar id') sb) u2)
  | Uifthenelse(u1, u2, u3) ->
      début filtre substitute sb u1 avec
        Uconst (Uconst_ptr n) ->
          si n <> 0 alors substitute sb u2 sinon substitute sb u3
      | Uprim(Pmakeblock _, _, _) ->
          substitute sb u2
      | su1 ->
          Uifthenelse(su1, substitute sb u2, substitute sb u3)
      fin
  | Usequence(u1, u2) -> Usequence(substitute sb u1, substitute sb u2)
  | Uwhile(u1, u2) -> Uwhile(substitute sb u1, substitute sb u2)
  | Ufor(id, u1, u2, dir, u3) ->
      soit id' = Ident.rename id dans
      Ufor(id', substitute sb u1, substitute sb u2, dir,
           substitute (Tbl.add id (Uvar id') sb) u3)
  | Uassign(id, u) ->
      soit id' =
        essaie
          filtre Tbl.find id sb avec Uvar i -> i | _ -> affirme faux
        avec Not_found ->
          id dans
      Uassign(id', substitute sb u)
  | Usend(k, u1, u2, ul, dbg) ->
      Usend(k, substitute sb u1, substitute sb u2, List.map (substitute sb) ul,
            dbg)

(* Perform an inline expansion *)

soit is_simple_argument = fonction
  | Uvar _  | Uconst _ -> vrai
  | _ -> faux

soit no_effects = fonction
  | Uclosure _ -> vrai
  | u -> is_simple_argument u

soit rec bind_params_rec subst params args body =
  filtre (params, args) avec
    ([], []) -> substitute subst body
  | (p1 :: pl, a1 :: al) ->
      si is_simple_argument a1 alors
        bind_params_rec (Tbl.add p1 a1 subst) pl al body
      sinon début
        soit p1' = Ident.rename p1 dans
        soit u1, u2 =
          filtre Ident.name p1, a1 avec
          | "*opt*", Uprim(Pmakeblock(0, Immutable), [a], dbg) ->
              a, Uprim(Pmakeblock(0, Immutable), [Uvar p1'], dbg)
          | _ ->
              a1, Uvar p1'
        dans
        soit body' =
          bind_params_rec (Tbl.add p1 u2 subst) pl al body dans
        si occurs_var p1 body alors Ulet(p1', u1, body')
        sinon si no_effects a1 alors body'
        sinon Usequence(a1, body')
      fin
  | (_, _) -> affirme faux

soit bind_params params args body =
  (* Reverse parameters and arguments to preserve right-to-left
     evaluation order (PR#2910). *)
  bind_params_rec Tbl.empty (List.rev params) (List.rev args) body

(* Check if a lambda term is ``pure'',
   that is without side-effects *and* not containing function definitions *)

soit rec is_pure = fonction
    Lvar v -> vrai
  | Lconst cst -> vrai
  | Lprim((Psetglobal _ | Psetfield _ | Psetfloatfield _ | Pduprecord _ |
           Pccall _ | Praise _ | Poffsetref _ | Pstringsetu | Pstringsets |
           Parraysetu _ | Parraysets _ | Pbigarrayset _), _) -> faux
  | Lprim(p, args) -> List.for_all is_pure args
  | Levent(lam, ev) -> is_pure lam
  | _ -> faux

(* Generate a direct application *)

soit direct_apply fundesc funct ufunct uargs =
  soit app_args =
    si fundesc.fun_closed alors uargs sinon uargs @ [ufunct] dans
  soit app =
    filtre fundesc.fun_inline avec
      None -> Udirect_apply(fundesc.fun_label, app_args, Debuginfo.none)
    | Some(params, body) -> bind_params params app_args body dans
  (* If ufunct can contain side-effects or function definitions,
     we must make sure that it is evaluated exactly once.
     If the function is not closed, we evaluate ufunct as part of the
     arguments.
     If the function is closed, we force the evaluation of ufunct first. *)
  si not fundesc.fun_closed || is_pure funct
  alors app
  sinon Usequence(ufunct, app)

(* Add [Value_integer] or [Value_constptr] info to the approximation
   of an application *)

soit strengthen_approx appl approx =
  filtre approx_ulam appl avec
    (Value_const _) tel intapprox ->
      intapprox
  | _ -> approx

(* If a term has approximation Value_integer or Value_constptr and is pure,
   replace it by an integer constant *)

soit check_constant_result lam ulam approx =
  filtre approx avec
    Value_const c quand is_pure lam -> make_const c
  | Value_global_field (id, i) quand is_pure lam ->
      début filtre ulam avec
      | Uprim(Pfield _, [Uprim(Pgetglobal _, _, _)], _) -> (ulam, approx)
      | _ ->
          soit glb =
            Uprim(Pgetglobal (Ident.create_persistent id), [], Debuginfo.none)
          dans
          Uprim(Pfield i, [glb], Debuginfo.none), approx
      fin
  | _ -> (ulam, approx)

(* Evaluate an expression with known value for its side effects only,
   or discard it if it's pure *)

soit sequence_constant_expr lam ulam1 (ulam2, approx2 tel res2) =
  si is_pure lam alors res2 sinon (Usequence(ulam1, ulam2), approx2)

(* Maintain the approximation of the global structure being defined *)

soit global_approx = ref([||] : value_approximation array)

(* Maintain the nesting depth for functions *)

soit function_nesting_depth = ref 0
soit excessive_function_nesting_depth = 5

(* Decorate clambda term with debug information *)

soit rec add_debug_info ev u =
  filtre ev.lev_kind avec
  | Lev_after _ ->
      début filtre u avec
      | Udirect_apply(lbl, args, dinfo) ->
          Udirect_apply(lbl, args, Debuginfo.from_call ev)
      | Ugeneric_apply(Udirect_apply(lbl, args1, dinfo1),
                       args2, dinfo2) ->
          Ugeneric_apply(Udirect_apply(lbl, args1, Debuginfo.from_call ev),
                         args2, Debuginfo.from_call ev)
      | Ugeneric_apply(fn, args, dinfo) ->
          Ugeneric_apply(fn, args, Debuginfo.from_call ev)
      | Uprim(Praise k, args, dinfo) ->
          Uprim(Praise k, args, Debuginfo.from_call ev)
      | Uprim(p, args, dinfo) ->
          Uprim(p, args, Debuginfo.from_call ev)
      | Usend(kind, u1, u2, args, dinfo) ->
          Usend(kind, u1, u2, args, Debuginfo.from_call ev)
      | Usequence(u1, u2) ->
          Usequence(u1, add_debug_info ev u2)
      | _ -> u
      fin
  | _ -> u

(* Uncurry an expression and explicitate closures.
   Also return the approximation of the expression.
   The approximation environment [fenv] maps idents to approximations.
   Idents not bound in [fenv] approximate to [Value_unknown].
   The closure environment [cenv] maps idents to [ulambda] terms.
   It is used to substitute environment accesses for free identifiers. *)

exception NotClosed

soit close_approx_var fenv cenv id =
  soit approx = essaie Tbl.find id fenv avec Not_found -> Value_unknown dans
  filtre approx avec
    Value_const c -> make_const c
  | approx ->
      soit subst = essaie Tbl.find id cenv avec Not_found -> Uvar id dans
      (subst, approx)

soit close_var fenv cenv id =
  soit (ulam, app) = close_approx_var fenv cenv id dans ulam

soit rec close fenv cenv = fonction
    Lvar id ->
      close_approx_var fenv cenv id
  | Lconst cst ->
      soit str ?(shared = vrai) cst =
        soit name =
          Compilenv.new_structured_constant cst ~shared
        dans
        Uconst_ref (name, cst)
      dans
      soit rec transl = fonction
        | Const_base(Const_int n) -> Uconst_int n
        | Const_base(Const_char c) -> Uconst_int (Char.code c)
        | Const_pointer n -> Uconst_ptr n
        | Const_block (tag, fields) ->
            str (Uconst_block (tag, List.map transl fields))
        | Const_float_array sl ->
            (* constant float arrays are really immutable *)
            str (Uconst_float_array sl)
        | Const_immstring s ->
            str (Uconst_string s)
        | Const_base (Const_string (s, _)) ->
              (* strings (even literal ones) are mutable! *)
              (* of course, the empty string is really immutable *)
            str ~shared:faux(*(String.length s = 0)*) (Uconst_string s)
        | Const_base(Const_float x) -> str (Uconst_float x)
        | Const_base(Const_int32 x) -> str (Uconst_int32 x)
        | Const_base(Const_int64 x) -> str (Uconst_int64 x)
        | Const_base(Const_nativeint x) -> str (Uconst_nativeint x)
      dans
      make_const (transl cst)
  | Lfunction(kind, params, body) tel funct ->
      close_one_function fenv cenv (Ident.create "fun") funct

    (* We convert [f a] to [let a' = a in fun b c -> f a' b c]
       when fun_arity > nargs *)
  | Lapply(funct, args, loc) ->
      soit nargs = List.length args dans
      début filtre (close fenv cenv funct, close_list fenv cenv args) avec
        ((ufunct, Value_closure(fundesc, approx_res)),
         [Uprim(Pmakeblock(_, _), uargs, _)])
        quand List.length uargs = - fundesc.fun_arity ->
          soit app = direct_apply fundesc funct ufunct uargs dans
          (app, strengthen_approx app approx_res)
      | ((ufunct, Value_closure(fundesc, approx_res)), uargs)
        quand nargs = fundesc.fun_arity ->
          soit app = direct_apply fundesc funct ufunct uargs dans
          (app, strengthen_approx app approx_res)

      | ((ufunct, Value_closure(fundesc, approx_res)), uargs)
          quand nargs < fundesc.fun_arity ->
        soit first_args = List.map (fonc arg ->
          (Ident.create "arg", arg) ) uargs dans
        soit final_args =
          Array.to_list (Array.init (fundesc.fun_arity - nargs)
                                    (fonc _ -> Ident.create "arg")) dans
        soit rec iter args body =
          filtre args avec
              [] -> body
            | (arg1, arg2) :: args ->
              iter args
                (Ulet ( arg1, arg2, body))
        dans
        soit internal_args =
          (List.map (fonc (arg1, arg2) -> Lvar arg1) first_args)
          @ (List.map (fonc arg -> Lvar arg ) final_args)
        dans
        soit (new_fun, approx) = close fenv cenv
          (Lfunction(
            Curried, final_args, Lapply(funct, internal_args, loc)))
        dans
        soit new_fun = iter first_args new_fun dans
        (new_fun, approx)

      | ((ufunct, Value_closure(fundesc, approx_res)), uargs)
        quand fundesc.fun_arity > 0 && nargs > fundesc.fun_arity ->
          soit (first_args, rem_args) = split_list fundesc.fun_arity uargs dans
          (Ugeneric_apply(direct_apply fundesc funct ufunct first_args,
                          rem_args, Debuginfo.none),
           Value_unknown)
      | ((ufunct, _), uargs) ->
          (Ugeneric_apply(ufunct, uargs, Debuginfo.none), Value_unknown)
      fin
  | Lsend(kind, met, obj, args, _) ->
      soit (umet, _) = close fenv cenv met dans
      soit (uobj, _) = close fenv cenv obj dans
      (Usend(kind, umet, uobj, close_list fenv cenv args, Debuginfo.none),
       Value_unknown)
  | Llet(str, id, lam, body) ->
      soit (ulam, alam) = close_named fenv cenv id lam dans
      début filtre (str, alam) avec
        (Variable, _) ->
          soit (ubody, abody) = close fenv cenv body dans
          (Ulet(id, ulam, ubody), abody)
      | (_, Value_const _)
        quand str = Alias || is_pure lam ->
          close (Tbl.add id alam fenv) cenv body
      | (_, _) ->
          soit (ubody, abody) = close (Tbl.add id alam fenv) cenv body dans
          (Ulet(id, ulam, ubody), abody)
      fin
  | Lletrec(defs, body) ->
      si List.for_all
           (fonction (id, Lfunction(_, _, _)) -> vrai | _ -> faux)
           defs
      alors début
        (* Simple case: only function definitions *)
        soit (clos, infos) = close_functions fenv cenv defs dans
        soit clos_ident = Ident.create "clos" dans
        soit fenv_body =
          List.fold_right
            (fonc (id, pos, approx) fenv -> Tbl.add id approx fenv)
            infos fenv dans
        soit (ubody, approx) = close fenv_body cenv body dans
        soit sb =
          List.fold_right
            (fonc (id, pos, approx) sb ->
              Tbl.add id (Uoffset(Uvar clos_ident, pos)) sb)
            infos Tbl.empty dans
        (Ulet(clos_ident, clos, substitute sb ubody),
         approx)
      fin sinon début
        (* General case: recursive definition of values *)
        soit rec clos_defs = fonction
          [] -> ([], fenv)
        | (id, lam) :: rem ->
            soit (udefs, fenv_body) = clos_defs rem dans
            soit (ulam, approx) = close fenv cenv lam dans
            ((id, ulam) :: udefs, Tbl.add id approx fenv_body) dans
        soit (udefs, fenv_body) = clos_defs defs dans
        soit (ubody, approx) = close fenv_body cenv body dans
        (Uletrec(udefs, ubody), approx)
      fin
  | Lprim(Pdirapply loc,[funct;arg])
  | Lprim(Prevapply loc,[arg;funct]) ->
      close fenv cenv (Lapply(funct, [arg], loc))
  | Lprim(Pgetglobal id, []) tel lam ->
      check_constant_result lam
                            (getglobal id)
                            (Compilenv.global_approx id)
  | Lprim(Pfield n, [lam]) ->
      soit (ulam, approx) = close fenv cenv lam dans
      check_constant_result lam (Uprim(Pfield n, [ulam], Debuginfo.none))
                            (field_approx n approx)
  | Lprim(Psetfield(n, _), [Lprim(Pgetglobal id, []); lam]) ->
      soit (ulam, approx) = close fenv cenv lam dans
      si approx <> Value_unknown alors
        (!global_approx).(n) <- approx;
      (Uprim(Psetfield(n, faux), [getglobal id; ulam], Debuginfo.none),
       Value_unknown)
  | Lprim(Praise k, [Levent(arg, ev)]) ->
      soit (ulam, approx) = close fenv cenv arg dans
      (Uprim(Praise k, [ulam], Debuginfo.from_raise ev),
       Value_unknown)
  | Lprim(p, args) ->
      simplif_prim p (close_list_approx fenv cenv args) Debuginfo.none
  | Lswitch(arg, sw) ->
(* NB: failaction might get copied, thus it should be some Lstaticraise *)
      soit (uarg, _) = close fenv cenv arg dans
      soit const_index, const_actions =
        close_switch fenv cenv sw.sw_consts sw.sw_numconsts sw.sw_failaction
      et block_index, block_actions =
        close_switch fenv cenv sw.sw_blocks sw.sw_numblocks sw.sw_failaction dans
      (Uswitch(uarg,
               {us_index_consts = const_index;
                us_actions_consts = const_actions;
                us_index_blocks = block_index;
                us_actions_blocks = block_actions}),
       Value_unknown)
  | Lstringswitch(arg,sw,d) ->
      soit uarg,_ = close fenv cenv arg dans
      soit usw = 
        List.map
          (fonc (s,act) ->
            soit uact,_ = close fenv cenv act dans
            s,uact)
          sw dans
      soit ud,_ =  close fenv cenv d dans
      Ustringswitch (uarg,usw,ud),Value_unknown
  | Lstaticraise (i, args) ->
      (Ustaticfail (i, close_list fenv cenv args), Value_unknown)
  | Lstaticcatch(body, (i, vars), handler) ->
      soit (ubody, _) = close fenv cenv body dans
      soit (uhandler, _) = close fenv cenv handler dans
      (Ucatch(i, vars, ubody, uhandler), Value_unknown)
  | Ltrywith(body, id, handler) ->
      soit (ubody, _) = close fenv cenv body dans
      soit (uhandler, _) = close fenv cenv handler dans
      (Utrywith(ubody, id, uhandler), Value_unknown)
  | Lifthenelse(arg, ifso, ifnot) ->
      début filtre close fenv cenv arg avec
        (uarg, Value_const (Uconst_ptr n)) ->
          sequence_constant_expr arg uarg
            (close fenv cenv (si n = 0 alors ifnot sinon ifso))
      | (uarg, _ ) ->
          soit (uifso, _) = close fenv cenv ifso dans
          soit (uifnot, _) = close fenv cenv ifnot dans
          (Uifthenelse(uarg, uifso, uifnot), Value_unknown)
      fin
  | Lsequence(lam1, lam2) ->
      soit (ulam1, _) = close fenv cenv lam1 dans
      soit (ulam2, approx) = close fenv cenv lam2 dans
      (Usequence(ulam1, ulam2), approx)
  | Lwhile(cond, body) ->
      soit (ucond, _) = close fenv cenv cond dans
      soit (ubody, _) = close fenv cenv body dans
      (Uwhile(ucond, ubody), Value_unknown)
  | Lfor(id, lo, hi, dir, body) ->
      soit (ulo, _) = close fenv cenv lo dans
      soit (uhi, _) = close fenv cenv hi dans
      soit (ubody, _) = close fenv cenv body dans
      (Ufor(id, ulo, uhi, dir, ubody), Value_unknown)
  | Lassign(id, lam) ->
      soit (ulam, _) = close fenv cenv lam dans
      (Uassign(id, ulam), Value_unknown)
  | Levent(lam, ev) ->
      soit (ulam, approx) = close fenv cenv lam dans
      (add_debug_info ev ulam, approx)
  | Lifused _ ->
      affirme faux

et close_list fenv cenv = fonction
    [] -> []
  | lam :: rem ->
      soit (ulam, _) = close fenv cenv lam dans
      ulam :: close_list fenv cenv rem

et close_list_approx fenv cenv = fonction
    [] -> ([], [])
  | lam :: rem ->
      soit (ulam, approx) = close fenv cenv lam dans
      soit (ulams, approxs) = close_list_approx fenv cenv rem dans
      (ulam :: ulams, approx :: approxs)

et close_named fenv cenv id = fonction
    Lfunction(kind, params, body) tel funct ->
      close_one_function fenv cenv id funct
  | lam ->
      close fenv cenv lam

(* Build a shared closure for a set of mutually recursive functions *)

et close_functions fenv cenv fun_defs =
  soit fun_defs =
    List.flatten
      (List.map
         (fonction
           | (id, Lfunction(kind, params, body)) ->
               split_default_wrapper id kind params body
           | _ -> affirme faux
         )
         fun_defs)
  dans

  (* Update and check nesting depth *)
  incr function_nesting_depth;
  soit initially_closed =
    !function_nesting_depth < excessive_function_nesting_depth dans
  (* Determine the free variables of the functions *)
  soit fv =
    IdentSet.elements (free_variables (Lletrec(fun_defs, lambda_unit))) dans
  (* Build the function descriptors for the functions.
     Initially all functions are assumed not to need their environment
     parameter. *)
  soit uncurried_defs =
    List.map
      (fonction
          (id, Lfunction(kind, params, body)) ->
            soit label = Compilenv.make_symbol (Some (Ident.unique_name id)) dans
            soit arity = List.length params dans
            soit fundesc =
              {fun_label = label;
               fun_arity = (si kind = Tupled alors -arity sinon arity);
               fun_closed = initially_closed;
               fun_inline = None } dans
            (id, params, body, fundesc)
        | (_, _) -> fatal_error "Closure.close_functions")
      fun_defs dans
  (* Build an approximate fenv for compiling the functions *)
  soit fenv_rec =
    List.fold_right
      (fonc (id, params, body, fundesc) fenv ->
        Tbl.add id (Value_closure(fundesc, Value_unknown)) fenv)
      uncurried_defs fenv dans
  (* Determine the offsets of each function's closure in the shared block *)
  soit env_pos = ref (-1) dans
  soit clos_offsets =
    List.map
      (fonc (id, params, body, fundesc) ->
        soit pos = !env_pos + 1 dans
        env_pos := !env_pos + 1 + (si fundesc.fun_arity <> 1 alors 3 sinon 2);
        pos)
      uncurried_defs dans
  soit fv_pos = !env_pos dans
  (* This reference will be set to false if the hypothesis that a function
     does not use its environment parameter is invalidated. *)
  soit useless_env = ref initially_closed dans
  (* Translate each function definition *)
  soit clos_fundef (id, params, body, fundesc) env_pos =
    soit dbg = filtre body avec
      | Levent (_,({lev_kind=Lev_function} tel ev)) -> Debuginfo.from_call ev
      | _ -> Debuginfo.none dans
    soit env_param = Ident.create "env" dans
    soit cenv_fv =
      build_closure_env env_param (fv_pos - env_pos) fv dans
    soit cenv_body =
      List.fold_right2
        (fonc (id, params, body, fundesc) pos env ->
          Tbl.add id (Uoffset(Uvar env_param, pos - env_pos)) env)
        uncurried_defs clos_offsets cenv_fv dans
    soit (ubody, approx) = close fenv_rec cenv_body body dans
    si !useless_env && occurs_var env_param ubody alors raise NotClosed;
    soit fun_params = si !useless_env alors params sinon params @ [env_param] dans
    soit f =
      {
        label  = fundesc.fun_label;
        arity  = fundesc.fun_arity;
        params = fun_params;
        body   = ubody;
        dbg;
      }
    dans
    (* give more chance of function with default parameters (i.e.
       their wrapper functions) to be inlined *)
    soit n =
      List.fold_left
        (fonc n id -> n + si Ident.name id = "*opt*" alors 8 sinon 1)
        0
        fun_params
    dans
    si lambda_smaller ubody
        (!Clflags.inline_threshold + n)
    alors fundesc.fun_inline <- Some(fun_params, ubody);

    (f, (id, env_pos, Value_closure(fundesc, approx))) dans
  (* Translate all function definitions. *)
  soit clos_info_list =
    si initially_closed alors début
      soit snap = Compilenv.snapshot () dans
      essaie List.map2 clos_fundef uncurried_defs clos_offsets
      avec NotClosed ->
      (* If the hypothesis that the environment parameters are useless has been
         invalidated, then set [fun_closed] to false in all descriptions and
         recompile *)
        Compilenv.backtrack snap; (* PR#6337 *)
        List.iter
          (fonc (id, params, body, fundesc) ->
             fundesc.fun_closed <- faux;
             fundesc.fun_inline <- None;
          )
          uncurried_defs;
        useless_env := faux;
        List.map2 clos_fundef uncurried_defs clos_offsets
    fin sinon
      (* Excessive closure nesting: assume environment parameter is used *)
        List.map2 clos_fundef uncurried_defs clos_offsets
    dans
  (* Update nesting depth *)
  decr function_nesting_depth;
  (* Return the Uclosure node and the list of all identifiers defined,
     with offsets and approximations. *)
  soit (clos, infos) = List.split clos_info_list dans
  soit fv = si !useless_env alors [] sinon fv dans
  (Uclosure(clos, List.map (close_var fenv cenv) fv), infos)

(* Same, for one non-recursive function *)

et close_one_function fenv cenv id funct =
  filtre close_functions fenv cenv [id, funct] avec
  | (clos, (i, _, approx) :: _) quand id = i -> (clos, approx)
  | _ -> fatal_error "Closure.close_one_function"

(* Close a switch *)

et close_switch fenv cenv cases num_keys default =
  soit index = Array.create num_keys 0
  et store = mk_store Lambda.same dans

  (* First default case *)
  début filtre default avec
  | Some def quand List.length cases < num_keys ->
      ignore (store.act_store def)
  | _ -> ()
  fin ;
  (* Then all other cases *)
  List.iter
    (fonc (key,lam) ->
     index.(key) <- store.act_store lam)
    cases ;
  (* Compile action *)
  soit actions =
    Array.map
      (fonc lam ->
        soit ulam,_ = close fenv cenv lam dans
        ulam)
      (store.act_get ()) dans
  filtre actions avec
  | [| |] -> [| |], [| |] (* May happen when default is None *)
  | _     -> index, actions


(* Collect exported symbols for structured constants *)

soit collect_exported_structured_constants a =
  soit rec approx = fonction
    | Value_closure (fd, a) ->
        approx a;
        début filtre fd.fun_inline avec
        | Some (_, u) -> ulam u
        | None -> ()
        fin
    | Value_tuple a -> Array.iter approx a
    | Value_const c -> const c
    | Value_unknown | Value_global_field _ -> ()
  et const = fonction
    | Uconst_ref (s, c) ->
        Compilenv.add_exported_constant s;
        structured_constant c
    | Uconst_int _ | Uconst_ptr _ -> ()
  et structured_constant = fonction
    | Uconst_block (_, ul) -> List.iter const ul
    | Uconst_float _ | Uconst_int32 _
    | Uconst_int64 _ | Uconst_nativeint _
    | Uconst_float_array _ | Uconst_string _ -> ()
  et ulam = fonction
    | Uvar _ -> ()
    | Uconst c -> const c
    | Udirect_apply (_, ul, _) -> List.iter ulam ul
    | Ugeneric_apply (u, ul, _) -> ulam u; List.iter ulam ul
    | Uclosure (fl, ul) ->
        List.iter (fonc f -> ulam f.body) fl;
        List.iter ulam ul
    | Uoffset(u, _) -> ulam u
    | Ulet (_, u1, u2) -> ulam u1; ulam u2
    | Uletrec (l, u) -> List.iter (fonc (_, u) -> ulam u) l; ulam u
    | Uprim (_, ul, _) -> List.iter ulam ul
    | Uswitch (u, sl) ->
        ulam u;
        Array.iter ulam sl.us_actions_consts;
        Array.iter ulam sl.us_actions_blocks
    | Ustringswitch (u,sw,d) ->
        ulam u ;
        List.iter (fonc (_,act) -> ulam act) sw ;
        ulam d
    | Ustaticfail (_, ul) -> List.iter ulam ul
    | Ucatch (_, _, u1, u2)
    | Utrywith (u1, _, u2)
    | Usequence (u1, u2)
    | Uwhile (u1, u2)  -> ulam u1; ulam u2
    | Uifthenelse (u1, u2, u3)
    | Ufor (_, u1, u2, _, u3) -> ulam u1; ulam u2; ulam u3
    | Uassign (_, u) -> ulam u
    | Usend (_, u1, u2, ul, _) -> ulam u1; ulam u2; List.iter ulam ul
  dans
  approx a

(* The entry point *)

soit intro size lam =
  function_nesting_depth := 0;
  soit id = Compilenv.make_symbol None dans
  global_approx := Array.init size (fonc i -> Value_global_field (id, i));
  Compilenv.set_global_approx(Value_tuple !global_approx);
  soit (ulam, approx) = close Tbl.empty Tbl.empty lam dans
  collect_exported_structured_constants (Value_tuple !global_approx);
  global_approx := [||];
  ulam
