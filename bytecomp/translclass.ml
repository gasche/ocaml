(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Jerome Vouillon, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Asttypes
ouvre Types
ouvre Typedtree
ouvre Lambda
ouvre Translobj
ouvre Translcore

(* XXX Rajouter des evenements... *)

type error = Illegal_class_expr | Tags de label * label

exception Error de Location.t * error

soit lfunction params body =
  si params = [] alors body sinon
  filtre body avec
    Lfunction (Curried, params', body') ->
      Lfunction (Curried, params @ params', body')
  |  _ ->
      Lfunction (Curried, params, body)

soit lapply func args loc =
  filtre func avec
    Lapply(func', args', _) ->
      Lapply(func', args' @ args, loc)
  | _ ->
      Lapply(func, args, loc)

soit mkappl (func, args) = Lapply (func, args, Location.none);;

soit lsequence l1 l2 =
  si l2 = lambda_unit alors l1 sinon Lsequence(l1, l2)

soit lfield v i = Lprim(Pfield i, [Lvar v])

soit transl_label l = share (Const_immstring l)

soit transl_meth_list lst =
  si lst = [] alors Lconst (Const_pointer 0) sinon
  share (Const_block
            (0, List.map (fonc lab -> Const_immstring lab) lst))

soit set_inst_var obj id expr =
  soit kind = si Typeopt.maybe_pointer expr alors Paddrarray sinon Pintarray dans
  Lprim(Parraysetu kind, [Lvar obj; Lvar id; transl_exp expr])

soit copy_inst_var obj id expr templ offset =
  soit kind = si Typeopt.maybe_pointer expr alors Paddrarray sinon Pintarray dans
  soit id' = Ident.create (Ident.name id) dans
  Llet(Strict, id', Lprim (Pidentity, [Lvar id]),
  Lprim(Parraysetu kind,
        [Lvar obj; Lvar id';
         Lprim(Parrayrefu kind, [Lvar templ; Lprim(Paddint,
                                                   [Lvar id';
                                                    Lvar offset])])]))

soit transl_val tbl create name =
  mkappl (oo_prim (si create alors "new_variable" sinon "get_variable"),
          [Lvar tbl; transl_label name])

soit transl_vals tbl create strict vals rem =
  List.fold_right
    (fonc (name, id) rem ->
      Llet(strict, id, transl_val tbl create name, rem))
    vals rem

soit meths_super tbl meths inh_meths =
  List.fold_right
    (fonc (nm, id) rem ->
       essaie
         (nm, id,
          mkappl(oo_prim "get_method", [Lvar tbl; Lvar (Meths.find nm meths)]))
         :: rem
       avec Not_found -> rem)
    inh_meths []

soit bind_super tbl (vals, meths) cl_init =
  transl_vals tbl faux StrictOpt vals
    (List.fold_right (fonc (nm, id, def) rem -> Llet(StrictOpt, id, def, rem))
       meths cl_init)

soit create_object cl obj init =
  soit obj' = Ident.create "self" dans
  soit (inh_init, obj_init, has_init) = init obj' dans
  si obj_init = lambda_unit alors
    (inh_init,
     mkappl (oo_prim (si has_init alors "create_object_and_run_initializers"
                      sinon"create_object_opt"),
             [obj; Lvar cl]))
  sinon début
   (inh_init,
    Llet(Strict, obj',
            mkappl (oo_prim "create_object_opt", [obj; Lvar cl]),
         Lsequence(obj_init,
                   si not has_init alors Lvar obj' sinon
                   mkappl (oo_prim "run_initializers_opt",
                           [obj; Lvar obj'; Lvar cl]))))
  fin

soit name_pattern default p =
  filtre p.pat_desc avec
  | Tpat_var (id, _) -> id
  | Tpat_alias(p, id, _) -> id
  | _ -> Ident.create default

soit normalize_cl_path cl path =
  Env.normalize_path (Some cl.cl_loc) cl.cl_env path  

soit rec build_object_init cl_table obj params inh_init obj_init cl =
  filtre cl.cl_desc avec
    Tcl_ident ( path, _, _) ->
      soit obj_init = Ident.create "obj_init" dans
      soit envs, inh_init = inh_init dans
      soit env =
        filtre envs avec None -> []
        | Some envs -> [Lprim(Pfield (List.length inh_init + 1), [Lvar envs])]
      dans
      ((envs, (obj_init, normalize_cl_path cl path)
        ::inh_init),
       mkappl(Lvar obj_init, env @ [obj]))
  | Tcl_structure str ->
      create_object cl_table obj (fonc obj ->
        soit (inh_init, obj_init, has_init) =
          List.fold_right
            (fonc field (inh_init, obj_init, has_init) ->
               filtre field.cf_desc avec
                 Tcf_inherit (_, cl, _, _, _) ->
                   soit (inh_init, obj_init') =
                     build_object_init cl_table (Lvar obj) [] inh_init
                       (fonc _ -> lambda_unit) cl
                   dans
                   (inh_init, lsequence obj_init' obj_init, vrai)
               | Tcf_val (_, _, id, Tcfk_concrete (_, exp), _) ->
                   (inh_init, lsequence (set_inst_var obj id exp) obj_init,
                    has_init)
               | Tcf_method _ | Tcf_val _ | Tcf_constraint _ ->
                   (inh_init, obj_init, has_init)
               | Tcf_initializer _ ->
                   (inh_init, obj_init, vrai)
            )
            str.cstr_fields
            (inh_init, obj_init obj, faux)
        dans
        (inh_init,
         List.fold_right
           (fonc (id, expr) rem ->
              lsequence (Lifused (id, set_inst_var obj id expr)) rem)
           params obj_init,
         has_init))
  | Tcl_fun (_, pat, vals, cl, partial) ->
      soit vals = List.map (fonc (id, _, e) -> id,e) vals dans
      soit (inh_init, obj_init) =
        build_object_init cl_table obj (vals @ params) inh_init obj_init cl
      dans
      (inh_init,
       soit build params rem =
         soit param = name_pattern "param" pat dans
         Lfunction (Curried, param::params,
                    Matching.for_function
                      pat.pat_loc None (Lvar param) [pat, rem] partial)
       dans
       début filtre obj_init avec
         Lfunction (Curried, params, rem) -> build params rem
       | rem                              -> build [] rem
       fin)
  | Tcl_apply (cl, oexprs) ->
      soit (inh_init, obj_init) =
        build_object_init cl_table obj params inh_init obj_init cl
      dans
      (inh_init, transl_apply obj_init oexprs Location.none)
  | Tcl_let (rec_flag, defs, vals, cl) ->
      soit vals = List.map (fonc (id, _, e) -> id,e) vals dans
      soit (inh_init, obj_init) =
        build_object_init cl_table obj (vals @ params) inh_init obj_init cl
      dans
      (inh_init, Translcore.transl_let rec_flag defs obj_init)
  | Tcl_constraint (cl, _, vals, pub_meths, concr_meths) ->
      build_object_init cl_table obj params inh_init obj_init cl

soit rec build_object_init_0 cl_table params cl copy_env subst_env top ids =
  filtre cl.cl_desc avec
    Tcl_let (rec_flag, defs, vals, cl) ->
      soit vals = List.map (fonc (id, _, e) -> id,e) vals dans
      build_object_init_0 cl_table (vals@params) cl copy_env subst_env top ids
  | _ ->
      soit self = Ident.create "self" dans
      soit env = Ident.create "env" dans
      soit obj = si ids = [] alors lambda_unit sinon Lvar self dans
      soit envs = si top alors None sinon Some env dans
      soit ((_,inh_init), obj_init) =
        build_object_init cl_table obj params (envs,[]) (copy_env env) cl dans
      soit obj_init =
        si ids = [] alors obj_init sinon lfunction [self] obj_init dans
      (inh_init, lfunction [env] (subst_env env inh_init obj_init))


soit bind_method tbl lab id cl_init =
  Llet(Strict, id, mkappl (oo_prim "get_method_label",
                           [Lvar tbl; transl_label lab]),
       cl_init)

soit bind_methods tbl meths vals cl_init =
  soit methl = Meths.fold (fonc lab id tl -> (lab,id) :: tl) meths [] dans
  soit len = List.length methl et nvals = List.length vals dans
  si len < 2 && nvals = 0 alors Meths.fold (bind_method tbl) meths cl_init sinon
  si len = 0 && nvals < 2 alors transl_vals tbl vrai Strict vals cl_init sinon
  soit ids = Ident.create "ids" dans
  soit i = ref (len + nvals) dans
  soit getter, names =
    si nvals = 0 alors "get_method_labels", [] sinon
    "new_methods_variables", [transl_meth_list (List.map fst vals)]
  dans
  Llet(Strict, ids,
       mkappl (oo_prim getter,
               [Lvar tbl; transl_meth_list (List.map fst methl)] @ names),
       List.fold_right
         (fonc (lab,id) lam -> decr i; Llet(StrictOpt, id, lfield ids !i, lam))
         (methl @ vals) cl_init)

soit output_methods tbl methods lam =
  filtre methods avec
    [] -> lam
  | [lab; code] ->
      lsequence (mkappl(oo_prim "set_method", [Lvar tbl; lab; code])) lam
  | _ ->
      lsequence (mkappl(oo_prim "set_methods",
                        [Lvar tbl; Lprim(Pmakeblock(0,Immutable), methods)]))
        lam

soit rec ignore_cstrs cl =
  filtre cl.cl_desc avec
    Tcl_constraint (cl, _, _, _, _) -> ignore_cstrs cl
  | Tcl_apply (cl, _) -> ignore_cstrs cl
  | _ -> cl

soit rec index a = fonction
    [] -> raise Not_found
  | b :: l ->
      si b = a alors 0 sinon 1 + index a l

soit bind_id_as_val (id, _, _) = ("", id)

soit rec build_class_init cla cstr super inh_init cl_init msubst top cl =
  filtre cl.cl_desc avec
    Tcl_ident ( path, _, _) ->
      début filtre inh_init avec
        (obj_init, path')::inh_init ->
          soit lpath = transl_path ~loc:cl.cl_loc cl.cl_env path dans
          (inh_init,
           Llet (Strict, obj_init,
                 mkappl(Lprim(Pfield 1, [lpath]), Lvar cla ::
                        si top alors [Lprim(Pfield 3, [lpath])] sinon []),
                 bind_super cla super cl_init))
      | _ ->
          affirme faux
      fin
  | Tcl_structure str ->
      soit cl_init = bind_super cla super cl_init dans
      soit (inh_init, cl_init, methods, values) =
        List.fold_right
          (fonc field (inh_init, cl_init, methods, values) ->
            filtre field.cf_desc avec
              Tcf_inherit (_, cl, _, vals, meths) ->
                soit cl_init = output_methods cla methods cl_init dans
                soit inh_init, cl_init =
                  build_class_init cla faux
                    (vals, meths_super cla str.cstr_meths meths)
                    inh_init cl_init msubst top cl dans
                (inh_init, cl_init, [], values)
            | Tcf_val (name, _, id, _, over) ->
                soit values = si over alors values sinon (name.txt, id) :: values dans
                (inh_init, cl_init, methods, values)
            | Tcf_method (_, _, Tcfk_virtual _)
            | Tcf_constraint _
              ->
                (inh_init, cl_init, methods, values)
            | Tcf_method (name, _, Tcfk_concrete (_, exp)) ->
                soit met_code = msubst vrai (transl_exp exp) dans
                soit met_code =
                  si !Clflags.native_code && List.length met_code = 1 alors
                    (* Force correct naming of method for profiles *)
                    soit met = Ident.create ("method_" ^ name.txt) dans
                    [Llet(Strict, met, List.hd met_code, Lvar met)]
                  sinon met_code
                dans
                (inh_init, cl_init,
                 Lvar (Meths.find name.txt str.cstr_meths) :: met_code @ methods,
                 values)
            | Tcf_initializer exp ->
                (inh_init,
                 Lsequence(mkappl (oo_prim "add_initializer",
                                   Lvar cla :: msubst faux (transl_exp exp)),
                           cl_init),
                 methods, values))
          str.cstr_fields
          (inh_init, cl_init, [], [])
      dans
      soit cl_init = output_methods cla methods cl_init dans
      (inh_init, bind_methods cla str.cstr_meths values cl_init)
  | Tcl_fun (_, pat, vals, cl, _) ->
      soit (inh_init, cl_init) =
        build_class_init cla cstr super inh_init cl_init msubst top cl
      dans
      soit vals = List.map bind_id_as_val vals dans
      (inh_init, transl_vals cla vrai StrictOpt vals cl_init)
  | Tcl_apply (cl, exprs) ->
      build_class_init cla cstr super inh_init cl_init msubst top cl
  | Tcl_let (rec_flag, defs, vals, cl) ->
      soit (inh_init, cl_init) =
        build_class_init cla cstr super inh_init cl_init msubst top cl
      dans
      soit vals = List.map bind_id_as_val vals dans
      (inh_init, transl_vals cla vrai StrictOpt vals cl_init)
  | Tcl_constraint (cl, _, vals, meths, concr_meths) ->
      soit virt_meths =
        List.filter (fonc lab -> not (Concr.mem lab concr_meths)) meths dans
      soit concr_meths = Concr.elements concr_meths dans
      soit narrow_args =
        [Lvar cla;
         transl_meth_list vals;
         transl_meth_list virt_meths;
         transl_meth_list concr_meths] dans
      soit cl = ignore_cstrs cl dans
      début filtre cl.cl_desc, inh_init avec
        Tcl_ident (path, _, _), (obj_init, path')::inh_init ->
          affirme (Path.same (normalize_cl_path cl path) path');
          soit lpath = transl_normal_path path' dans
          soit inh = Ident.create "inh"
          et ofs = List.length vals + 1
          et valids, methids = super dans
          soit cl_init =
            List.fold_left
              (fonc init (nm, id, _) ->
                Llet(StrictOpt, id, lfield inh (index nm concr_meths + ofs),
                     init))
              cl_init methids dans
          soit cl_init =
            List.fold_left
              (fonc init (nm, id) ->
                Llet(StrictOpt, id, lfield inh (index nm vals + 1), init))
              cl_init valids dans
          (inh_init,
           Llet (Strict, inh,
                 mkappl(oo_prim "inherits", narrow_args @
                        [lpath; Lconst(Const_pointer(si top alors 1 sinon 0))]),
                 Llet(StrictOpt, obj_init, lfield inh 0, cl_init)))
      | _ ->
          soit core cl_init =
            build_class_init cla vrai super inh_init cl_init msubst top cl
          dans
          si cstr alors core cl_init sinon
          soit (inh_init, cl_init) =
            core (Lsequence (mkappl (oo_prim "widen", [Lvar cla]), cl_init))
          dans
          (inh_init,
           Lsequence(mkappl (oo_prim "narrow", narrow_args),
                     cl_init))
      fin

soit rec build_class_lets cl ids =
  filtre cl.cl_desc avec
    Tcl_let (rec_flag, defs, vals, cl') ->
      soit env, wrap = build_class_lets cl' [] dans
      (env, fonc x ->
        soit lam = Translcore.transl_let rec_flag defs (wrap x) dans
        (* Check recursion in toplevel let-definitions *)
        si ids = [] || Translcore.check_recursive_lambda ids lam alors lam
        sinon raise(Error(cl.cl_loc, Illegal_class_expr)))
  | _ ->
      (cl.cl_env, fonc x -> x)

soit rec get_class_meths cl =
  filtre cl.cl_desc avec
    Tcl_structure cl ->
      Meths.fold (fonc _ -> IdentSet.add) cl.cstr_meths IdentSet.empty
  | Tcl_ident _ -> IdentSet.empty
  | Tcl_fun (_, _, _, cl, _)
  | Tcl_let (_, _, _, cl)
  | Tcl_apply (cl, _)
  | Tcl_constraint (cl, _, _, _, _) -> get_class_meths cl

(*
   XXX Il devrait etre peu couteux d'ecrire des classes :
     class c x y = d e f
*)
soit rec transl_class_rebind obj_init cl vf =
  filtre cl.cl_desc avec
    Tcl_ident (path, _, _) ->
      si vf = Concrete alors début
        essaie si (Env.find_class path cl.cl_env).cty_new = None alors raise Exit
        avec Not_found -> raise Exit
      fin;
      (normalize_cl_path cl path, obj_init)
  | Tcl_fun (_, pat, _, cl, partial) ->
      soit path, obj_init = transl_class_rebind obj_init cl vf dans
      soit build params rem =
        soit param = name_pattern "param" pat dans
        Lfunction (Curried, param::params,
                   Matching.for_function
                     pat.pat_loc None (Lvar param) [pat, rem] partial)
      dans
      (path,
       filtre obj_init avec
         Lfunction (Curried, params, rem) -> build params rem
       | rem                              -> build [] rem)
  | Tcl_apply (cl, oexprs) ->
      soit path, obj_init = transl_class_rebind obj_init cl vf dans
      (path, transl_apply obj_init oexprs Location.none)
  | Tcl_let (rec_flag, defs, vals, cl) ->
      soit path, obj_init = transl_class_rebind obj_init cl vf dans
      (path, Translcore.transl_let rec_flag defs obj_init)
  | Tcl_structure _ -> raise Exit
  | Tcl_constraint (cl', _, _, _, _) ->
      soit path, obj_init = transl_class_rebind obj_init cl' vf dans
      soit rec check_constraint = fonction
          Cty_constr(path', _, _) quand Path.same path path' -> ()
        | Cty_arrow (_, _, cty) -> check_constraint cty
        | _ -> raise Exit
      dans
      check_constraint cl.cl_type;
      (path, obj_init)

soit rec transl_class_rebind_0 self obj_init cl vf =
  filtre cl.cl_desc avec
    Tcl_let (rec_flag, defs, vals, cl) ->
      soit path, obj_init = transl_class_rebind_0 self obj_init cl vf dans
      (path, Translcore.transl_let rec_flag defs obj_init)
  | _ ->
      soit path, obj_init = transl_class_rebind obj_init cl vf dans
      (path, lfunction [self] obj_init)

soit transl_class_rebind ids cl vf =
  essaie
    soit obj_init = Ident.create "obj_init"
    et self = Ident.create "self" dans
    soit obj_init0 = lapply (Lvar obj_init) [Lvar self] Location.none dans
    soit path, obj_init' = transl_class_rebind_0 self obj_init0 cl vf dans
    si not (Translcore.check_recursive_lambda ids obj_init') alors
      raise(Error(cl.cl_loc, Illegal_class_expr));
    soit id = (obj_init' = lfunction [self] obj_init0) dans
    si id alors transl_normal_path path sinon

    soit cla = Ident.create "class"
    et new_init = Ident.create "new_init"
    et env_init = Ident.create "env_init"
    et table = Ident.create "table"
    et envs = Ident.create "envs" dans
    Llet(
    Strict, new_init, lfunction [obj_init] obj_init',
    Llet(
    Alias, cla, transl_normal_path path,
    Lprim(Pmakeblock(0, Immutable),
          [mkappl(Lvar new_init, [lfield cla 0]);
           lfunction [table]
             (Llet(Strict, env_init,
                   mkappl(lfield cla 1, [Lvar table]),
                   lfunction [envs]
                     (mkappl(Lvar new_init,
                             [mkappl(Lvar env_init, [Lvar envs])]))));
           lfield cla 2;
           lfield cla 3])))
  avec Exit ->
    lambda_unit

(* Rewrite a closure using builtins. Improves native code size. *)

soit rec module_path = fonction
    Lvar id ->
      soit s = Ident.name id dans s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'
  | Lprim(Pfield _, [p])    -> module_path p
  | Lprim(Pgetglobal _, []) -> vrai
  | _                       -> faux

soit const_path local = fonction
    Lvar id -> not (List.mem id local)
  | Lconst _ -> vrai
  | Lfunction (Curried, _, body) ->
      soit fv = free_variables body dans
      List.for_all (fonc x -> not (IdentSet.mem x fv)) local
  | p -> module_path p

soit rec builtin_meths self env env2 body =
  soit const_path = const_path (env::self) dans
  soit conv = fonction
    (* Lvar s when List.mem s self ->  "_self", [] *)
    | p quand const_path p -> "const", [p]
    | Lprim(Parrayrefu _, [Lvar s; Lvar n]) quand List.mem s self ->
        "var", [Lvar n]
    | Lprim(Pfield n, [Lvar e]) quand Ident.same e env ->
        "env", [Lvar env2; Lconst(Const_pointer n)]
    | Lsend(Self, met, Lvar s, [], _) quand List.mem s self ->
        "meth", [met]
    | _ -> raise Not_found
  dans
  filtre body avec
  | Llet(_, s', Lvar s, body) quand List.mem s self ->
      builtin_meths (s'::self) env env2 body
  | Lapply(f, [arg], _) quand const_path f ->
      soit s, args = conv arg dans ("app_"^s, f :: args)
  | Lapply(f, [arg; p], _) quand const_path f && const_path p ->
      soit s, args = conv arg dans
      ("app_"^s^"_const", f :: args @ [p])
  | Lapply(f, [p; arg], _) quand const_path f && const_path p ->
      soit s, args = conv arg dans
      ("app_const_"^s, f :: p :: args)
  | Lsend(Self, Lvar n, Lvar s, [arg], _) quand List.mem s self ->
      soit s, args = conv arg dans
      ("meth_app_"^s, Lvar n :: args)
  | Lsend(Self, met, Lvar s, [], _) quand List.mem s self ->
      ("get_meth", [met])
  | Lsend(Public, met, arg, [], _) ->
      soit s, args = conv arg dans
      ("send_"^s, met :: args)
  | Lsend(Cached, met, arg, [_;_], _) ->
      soit s, args = conv arg dans
      ("send_"^s, met :: args)
  | Lfunction (Curried, [x], body) ->
      soit rec enter self = fonction
        | Lprim(Parraysetu _, [Lvar s; Lvar n; Lvar x'])
          quand Ident.same x x' && List.mem s self ->
            ("set_var", [Lvar n])
        | Llet(_, s', Lvar s, body) quand List.mem s self ->
            enter (s'::self) body
        | _ -> raise Not_found
      dans enter self body
  | Lfunction _ -> raise Not_found
  | _ ->
      soit s, args = conv body dans ("get_"^s, args)

module M = struct
  ouvre CamlinternalOO
  soit builtin_meths self env env2 body =
    soit builtin, args = builtin_meths self env env2 body dans
    (* if not arr then [mkappl(oo_prim builtin, args)] else *)
    soit tag = filtre builtin avec
      "get_const" -> GetConst
    | "get_var"   -> GetVar
    | "get_env"   -> GetEnv
    | "get_meth"  -> GetMeth
    | "set_var"   -> SetVar
    | "app_const" -> AppConst
    | "app_var"   -> AppVar
    | "app_env"   -> AppEnv
    | "app_meth"  -> AppMeth
    | "app_const_const" -> AppConstConst
    | "app_const_var"   -> AppConstVar
    | "app_const_env"   -> AppConstEnv
    | "app_const_meth"  -> AppConstMeth
    | "app_var_const"   -> AppVarConst
    | "app_env_const"   -> AppEnvConst
    | "app_meth_const"  -> AppMethConst
    | "meth_app_const"  -> MethAppConst
    | "meth_app_var"    -> MethAppVar
    | "meth_app_env"    -> MethAppEnv
    | "meth_app_meth"   -> MethAppMeth
    | "send_const" -> SendConst
    | "send_var"   -> SendVar
    | "send_env"   -> SendEnv
    | "send_meth"  -> SendMeth
    | _ -> affirme faux
    dans Lconst(Const_pointer(Obj.magic tag)) :: args
fin
ouvre M


(*
   Traduction d'une classe.
   Plusieurs cas:
    * reapplication d'une classe connue -> transl_class_rebind
    * classe sans dependances locales -> traduction directe
    * avec dependances locale -> creation d'un arbre de stubs,
      avec un noeud pour chaque classe locale heritee
   Une classe est un 4-uplet:
    (obj_init, class_init, env_init, env)
    obj_init: fonction de creation d'objet (unit -> obj)
    class_init: fonction d'heritage (table -> env_init)
      (une seule par code source)
    env_init: parametrage par l'environnement local (env -> params -> obj_init)
      (une par combinaison de class_init herites)
    env: environnement local
   Si ids=0 (objet immediat), alors on ne conserve que env_init.
*)

soit prerr_ids msg ids =
  soit names = List.map Ident.unique_toplevel_name ids dans
  prerr_endline (String.concat " " (msg :: names))

soit transl_class ids cl_id pub_meths cl vflag =
  (* First check if it is not only a rebind *)
  soit rebind = transl_class_rebind ids cl vflag dans
  si rebind <> lambda_unit alors rebind sinon

  (* Prepare for heavy environment handling *)
  soit tables = Ident.create (Ident.name cl_id ^ "_tables") dans
  soit (top_env, req) = oo_add_class tables dans
  soit top = not req dans
  soit cl_env, llets = build_class_lets cl ids dans
  soit new_ids = si top alors [] sinon Env.diff top_env cl_env dans
  soit env2 = Ident.create "env" dans
  soit meth_ids = get_class_meths cl dans
  soit subst env lam i0 new_ids' =
    soit fv = free_variables lam dans
    (* prerr_ids "cl_id =" [cl_id]; prerr_ids "fv =" (IdentSet.elements fv); *)
    soit fv = List.fold_right IdentSet.remove !new_ids' fv dans
    (* We need to handle method ids specially, as they do not appear
       in the typing environment (PR#3576, PR#4560) *)
    (* very hacky: we add and remove free method ids on the fly,
       depending on the visit order... *)
    method_ids :=
      IdentSet.diff (IdentSet.union (free_methods lam) !method_ids) meth_ids;
    (* prerr_ids "meth_ids =" (IdentSet.elements meth_ids);
       prerr_ids "method_ids =" (IdentSet.elements !method_ids); *)
    soit new_ids = List.fold_right IdentSet.add new_ids !method_ids dans
    soit fv = IdentSet.inter fv new_ids dans
    new_ids' := !new_ids' @ IdentSet.elements fv;
    (* prerr_ids "new_ids' =" !new_ids'; *)
    soit i = ref (i0-1) dans
    List.fold_left
      (fonc subst id ->
        incr i; Ident.add id (lfield env !i)  subst)
      Ident.empty !new_ids'
  dans
  soit new_ids_meths = ref [] dans
  soit msubst arr = fonction
      Lfunction (Curried, self :: args, body) ->
        soit env = Ident.create "env" dans
        soit body' =
          si new_ids = [] alors body sinon
          subst_lambda (subst env body 0 new_ids_meths) body dans
        début essaie
          (* Doesn't seem to improve size for bytecode *)
          (* if not !Clflags.native_code then raise Not_found; *)
          si not arr || !Clflags.debug alors raise Not_found;
          builtin_meths [self] env env2 (lfunction args body')
        avec Not_found ->
          [lfunction (self :: args)
             (si not (IdentSet.mem env (free_variables body')) alors body' sinon
              Llet(Alias, env,
                   Lprim(Parrayrefu Paddrarray,
                         [Lvar self; Lvar env2]), body'))]
        fin
      | _ -> affirme faux
  dans
  soit new_ids_init = ref [] dans
  soit env1 = Ident.create "env" et env1' = Ident.create "env'" dans
  soit copy_env envs self =
    si top alors lambda_unit sinon
    Lifused(env2, Lprim(Parraysetu Paddrarray,
                        [Lvar self; Lvar env2; Lvar env1']))
  et subst_env envs l lam =
    si top alors lam sinon
    (* must be called only once! *)
    soit lam = subst_lambda (subst env1 lam 1 new_ids_init) lam dans
    Llet(Alias, env1, (si l = [] alors Lvar envs sinon lfield envs 0),
    Llet(Alias, env1',
         (si !new_ids_init = [] alors Lvar env1 sinon lfield env1 0),
         lam))
  dans

  (* Now we start compiling the class *)
  soit cla = Ident.create "class" dans
  soit (inh_init, obj_init) =
    build_object_init_0 cla [] cl copy_env subst_env top ids dans
  soit inh_init' = List.rev inh_init dans
  soit (inh_init', cl_init) =
    build_class_init cla vrai ([],[]) inh_init' obj_init msubst top cl
  dans
  affirme (inh_init' = []);
  soit table = Ident.create "table"
  et class_init = Ident.create (Ident.name cl_id ^ "_init")
  et env_init = Ident.create "env_init"
  et obj_init = Ident.create "obj_init" dans
  soit pub_meths =
    List.sort
      (fonc s s' -> compare (Btype.hash_variant s) (Btype.hash_variant s'))
      pub_meths dans
  soit tags = List.map Btype.hash_variant pub_meths dans
  soit rev_map = List.combine tags pub_meths dans
  List.iter2
    (fonc tag name ->
      soit name' = List.assoc tag rev_map dans
      si name' <> name alors raise(Error(cl.cl_loc, Tags(name, name'))))
    tags pub_meths;
  soit ltable table lam =
    Llet(Strict, table,
         mkappl (oo_prim "create_table", [transl_meth_list pub_meths]), lam)
  et ldirect obj_init =
    Llet(Strict, obj_init, cl_init,
         Lsequence(mkappl (oo_prim "init_class", [Lvar cla]),
                   mkappl (Lvar obj_init, [lambda_unit])))
  dans
  (* Simplest case: an object defined at toplevel (ids=[]) *)
  si top && ids = [] alors llets (ltable cla (ldirect obj_init)) sinon

  soit concrete = (vflag = Concrete)
  et lclass lam =
    soit cl_init = llets (Lfunction(Curried, [cla], cl_init)) dans
    Llet(Strict, class_init, cl_init, lam (free_variables cl_init))
  et lbody fv =
    si List.for_all (fonc id -> not (IdentSet.mem id fv)) ids alors
      mkappl (oo_prim "make_class",[transl_meth_list pub_meths;
                                    Lvar class_init])
    sinon
      ltable table (
      Llet(
      Strict, env_init, mkappl (Lvar class_init, [Lvar table]),
      Lsequence(
      mkappl (oo_prim "init_class", [Lvar table]),
      Lprim(Pmakeblock(0, Immutable),
            [mkappl (Lvar env_init, [lambda_unit]);
             Lvar class_init; Lvar env_init; lambda_unit]))))
  et lbody_virt lenvs =
    Lprim(Pmakeblock(0, Immutable),
          [lambda_unit; Lfunction(Curried,[cla], cl_init); lambda_unit; lenvs])
  dans
  (* Still easy: a class defined at toplevel *)
  si top && concrete alors lclass lbody sinon
  si top alors llets (lbody_virt lambda_unit) sinon

  (* Now for the hard stuff: prepare for table cacheing *)
  soit envs = Ident.create "envs"
  et cached = Ident.create "cached" dans
  soit lenvs =
    si !new_ids_meths = [] && !new_ids_init = [] && inh_init = []
    alors lambda_unit
    sinon Lvar envs dans
  soit lenv =
    soit menv =
      si !new_ids_meths = [] alors lambda_unit sinon
      Lprim(Pmakeblock(0, Immutable),
            List.map (fonc id -> Lvar id) !new_ids_meths) dans
    si !new_ids_init = [] alors menv sinon
    Lprim(Pmakeblock(0, Immutable),
          menv :: List.map (fonc id -> Lvar id) !new_ids_init)
  et linh_envs =
    List.map (fonc (_, p) -> Lprim(Pfield 3, [transl_normal_path p]))
      (List.rev inh_init)
  dans
  soit make_envs lam =
    Llet(StrictOpt, envs,
         (si linh_envs = [] alors lenv sinon
         Lprim(Pmakeblock(0, Immutable), lenv :: linh_envs)),
         lam)
  et def_ids cla lam =
    Llet(StrictOpt, env2,
         mkappl (oo_prim "new_variable", [Lvar cla; transl_label ""]),
         lam)
  dans
  soit inh_paths =
    List.filter
      (fonc (_,path) -> List.mem (Path.head path) new_ids) inh_init dans
  soit inh_keys =
    List.map (fonc (_,p) -> Lprim(Pfield 1, [transl_normal_path p])) inh_paths dans
  soit lclass lam =
    Llet(Strict, class_init,
         Lfunction(Curried, [cla], def_ids cla cl_init), lam)
  et lcache lam =
    si inh_keys = [] alors Llet(Alias, cached, Lvar tables, lam) sinon
    Llet(Strict, cached,
         mkappl (oo_prim "lookup_tables",
                [Lvar tables; Lprim(Pmakeblock(0, Immutable), inh_keys)]),
         lam)
  et lset cached i lam =
    Lprim(Psetfield(i, vrai), [Lvar cached; lam])
  dans
  soit ldirect () =
    ltable cla
      (Llet(Strict, env_init, def_ids cla cl_init,
            Lsequence(mkappl (oo_prim "init_class", [Lvar cla]),
                      lset cached 0 (Lvar env_init))))
  et lclass_virt () =
    lset cached 0 (Lfunction(Curried, [cla], def_ids cla cl_init))
  dans
  llets (
  lcache (
  Lsequence(
  Lifthenelse(lfield cached 0, lambda_unit,
              si ids = [] alors ldirect () sinon
              si not concrete alors lclass_virt () sinon
              lclass (
              mkappl (oo_prim "make_class_store",
                      [transl_meth_list pub_meths;
                       Lvar class_init; Lvar cached]))),
  make_envs (
  si ids = [] alors mkappl (lfield cached 0, [lenvs]) sinon
  Lprim(Pmakeblock(0, Immutable),
        si concrete alors
          [mkappl (lfield cached 0, [lenvs]);
           lfield cached 1;
           lfield cached 0;
           lenvs]
        sinon [lambda_unit; lfield cached 0; lambda_unit; lenvs]
       )))))

(* Wrapper for class compilation *)
(*
    let cl_id = ci.ci_id_class in
(* TODO: cl_id is used somewhere else as typesharp ? *)
  let _arity = List.length (fst ci.ci_params) in
  let pub_meths = m in
  let cl = ci.ci_expr in
  let vflag = vf in
*)

soit transl_class ids id pub_meths cl vf =
  oo_wrap cl.cl_env faux (transl_class ids id pub_meths cl) vf

soit () =
  transl_object := (fonc id meths cl -> transl_class [] id meths cl Concrete)

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Illegal_class_expr ->
      fprintf ppf "This kind of recursive class expression is not allowed"
  | Tags (lab1, lab2) ->
      fprintf ppf "Method labels `%s' and `%s' are incompatible.@ %s"
        lab1 lab2 "Change one of them."

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, err) ->
        Some (Location.error_of_printer loc report_error err)
      | _ ->
        None
    )
