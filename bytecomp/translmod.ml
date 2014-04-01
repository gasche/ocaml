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

(* Translation from typed abstract syntax to lambda terms,
   for the module language *)

ouvre Misc
ouvre Asttypes
ouvre Longident
ouvre Path
ouvre Types
ouvre Typedtree
ouvre Lambda
ouvre Translobj
ouvre Translcore
ouvre Translclass

type error =
  Circular_dependency de Ident.t


exception Error de Location.t * error

(* Compile an exception definition *)

soit prim_set_oo_id =
  Pccall {Primitive.prim_name = "caml_set_oo_id"; prim_arity = 1;
          prim_alloc = faux; prim_native_name = "";
          prim_native_float = faux}

soit transl_exception path decl =
  soit name =
    filtre path avec
      None -> Ident.name decl.cd_id
    | Some p -> Path.name p
  dans
  Lprim(prim_set_oo_id,
        [Lprim(Pmakeblock(Obj.object_tag, Mutable),
              [Lconst(Const_base(Const_string (name,None)));
               Lconst(Const_base(Const_int 0))])])

(* Compile a coercion *)

soit rec apply_coercion strict restr arg =
  filtre restr avec
    Tcoerce_none ->
      arg
  | Tcoerce_structure(pos_cc_list, id_pos_list) ->
      name_lambda strict arg (fonc id ->
        soit lam =
          Lprim(Pmakeblock(0, Immutable),
                List.map (apply_coercion_field id) pos_cc_list) dans
        soit fv = free_variables lam dans
        soit (lam,s) =
          List.fold_left (fonc (lam,s) (id',pos,c) ->
            si IdentSet.mem id' fv alors
              soit id'' = Ident.create (Ident.name id') dans
              (Llet(Alias,id'',
                    apply_coercion Alias c (Lprim(Pfield pos,[Lvar id])),lam),
               Ident.add id' (Lvar id'') s)
            sinon (lam,s))
            (lam, Ident.empty) id_pos_list
        dans
        si s == Ident.empty alors lam sinon subst_lambda s lam)
  | Tcoerce_functor(cc_arg, cc_res) ->
      soit param = Ident.create "funarg" dans
      name_lambda strict arg (fonc id ->
        Lfunction(Curried, [param],
          apply_coercion Strict cc_res
            (Lapply(Lvar id, [apply_coercion Alias cc_arg (Lvar param)],
                    Location.none))))
  | Tcoerce_primitive p ->
      transl_primitive Location.none p
  | Tcoerce_alias (path, cc) ->
      name_lambda strict arg
        (fonc id -> apply_coercion Alias cc (transl_normal_path path))

et apply_coercion_field id (pos, cc) =
  apply_coercion Alias cc (Lprim(Pfield pos, [Lvar id]))

(* Compose two coercions
   apply_coercion c1 (apply_coercion c2 e) behaves like
   apply_coercion (compose_coercions c1 c2) e. *)

soit rec compose_coercions c1 c2 =
  filtre (c1, c2) avec
    (Tcoerce_none, c2) -> c2
  | (c1, Tcoerce_none) -> c1
  | (Tcoerce_structure (pc1, ids1), Tcoerce_structure (pc2, ids2)) ->
      soit v2 = Array.of_list pc2 dans
      soit ids1 =
        List.map (fonc (id,pos1,c1) ->
          soit (pos2,c2) = v2.(pos1) dans (id, pos2, compose_coercions c1 c2))
          ids1
      dans
      Tcoerce_structure
        (List.map
          (fonction (p1, Tcoerce_primitive p) ->
                      (p1, Tcoerce_primitive p)
                  | (p1, c1) ->
                      soit (p2, c2) = v2.(p1) dans (p2, compose_coercions c1 c2))
             pc1,
         ids1 @ ids2)
  | (Tcoerce_functor(arg1, res1), Tcoerce_functor(arg2, res2)) ->
      Tcoerce_functor(compose_coercions arg2 arg1,
                      compose_coercions res1 res2)
  | (c1, Tcoerce_alias (path, c2)) ->
      Tcoerce_alias (path, compose_coercions c1 c2)
  | (_, _) ->
      fatal_error "Translmod.compose_coercions"

(* Record the primitive declarations occuring in the module compiled *)

soit primitive_declarations = ref ([] : Primitive.description list)
soit record_primitive = fonction
  | {val_kind=Val_prim p} ->
      primitive_declarations := p :: !primitive_declarations
  | _ -> ()

(* Keep track of the root path (from the root of the namespace to the
   currently compiled module expression).  Useful for naming exceptions. *)

soit global_path glob = Some(Pident glob)
soit functor_path path param =
  filtre path avec
    None -> None
  | Some p -> Some(Papply(p, Pident param))
soit field_path path field =
  filtre path avec
    None -> None
  | Some p -> Some(Pdot(p, Ident.name field, Path.nopos))

(* Utilities for compiling "module rec" definitions *)

soit mod_prim name =
  essaie
    transl_normal_path
      (fst (Env.lookup_value (Ldot (Lident "CamlinternalMod", name))
                             Env.empty))
  avec Not_found ->
    fatal_error ("Primitive " ^ name ^ " introuvable.")

soit undefined_location loc =
  soit (fname, line, char) = Location.get_pos_info loc.Location.loc_start dans
  Lconst(Const_block(0,
                     [Const_base(Const_string (fname, None));
                      Const_base(Const_int line);
                      Const_base(Const_int char)]))

soit init_shape modl =
  soit rec init_shape_mod env mty =
    filtre Mtype.scrape env mty avec
      Mty_ident _ ->
        raise Not_found
    | Mty_alias _ ->
        Const_block (1, [Const_pointer 0])
    | Mty_signature sg ->
        Const_block(0, [Const_block(0, init_shape_struct env sg)])
    | Mty_functor(id, arg, res) ->
        raise Not_found (* can we do better? *)
  et init_shape_struct env sg =
    filtre sg avec
      [] -> []
    | Sig_value(id, vdesc) :: rem ->
        soit init_v =
          filtre Ctype.expand_head env vdesc.val_type avec
            {desc = Tarrow(_,_,_,_)} ->
              Const_pointer 0 (* camlinternalMod.Function *)
          | {desc = Tconstr(p, _, _)} quand Path.same p Predef.path_lazy_t ->
              Const_pointer 1 (* camlinternalMod.Lazy *)
          | _ -> raise Not_found dans
        init_v :: init_shape_struct env rem
    | Sig_type(id, tdecl, _) :: rem ->
        init_shape_struct (Env.add_type ~check:faux id tdecl env) rem
    | Sig_exception(id, edecl) :: rem ->
        raise Not_found
    | Sig_module(id, md, _) :: rem ->
        init_shape_mod env md.md_type ::
        init_shape_struct (Env.add_module_declaration id md env) rem
    | Sig_modtype(id, minfo) :: rem ->
        init_shape_struct (Env.add_modtype id minfo env) rem
    | Sig_class(id, cdecl, _) :: rem ->
        Const_pointer 2 (* camlinternalMod.Class *)
        :: init_shape_struct env rem
    | Sig_class_type(id, ctyp, _) :: rem ->
        init_shape_struct env rem
  dans
  essaie
    Some(undefined_location modl.mod_loc,
         Lconst(init_shape_mod modl.mod_env modl.mod_type))
  avec Not_found ->
    None

(* Reorder bindings to honor dependencies.  *)

type binding_status = Undefined | Inprogress | Defined

soit reorder_rec_bindings bindings =
  soit id = Array.of_list (List.map (fonc (id,_,_,_) -> id) bindings)
  et loc = Array.of_list (List.map (fonc (_,loc,_,_) -> loc) bindings)
  et init = Array.of_list (List.map (fonc (_,_,init,_) -> init) bindings)
  et rhs = Array.of_list (List.map (fonc (_,_,_,rhs) -> rhs) bindings) dans
  soit fv = Array.map Lambda.free_variables rhs dans
  soit num_bindings = Array.length id dans
  soit status = Array.create num_bindings Undefined dans
  soit res = ref [] dans
  soit rec emit_binding i =
    filtre status.(i) avec
      Defined -> ()
    | Inprogress -> raise(Error(loc.(i), Circular_dependency id.(i)))
    | Undefined ->
        si init.(i) = None alors début
          status.(i) <- Inprogress;
          pour j = 0 à num_bindings - 1 faire
            si IdentSet.mem id.(j) fv.(i) alors emit_binding j
          fait
        fin;
        res := (id.(i), init.(i), rhs.(i)) :: !res;
        status.(i) <- Defined dans
  pour i = 0 à num_bindings - 1 faire
    filtre status.(i) avec
      Undefined -> emit_binding i
    | Inprogress -> affirme faux
    | Defined -> ()
  fait;
  List.rev !res

(* Generate lambda-code for a reordered list of bindings *)

soit eval_rec_bindings bindings cont =
  soit rec bind_inits = fonction
    [] ->
      bind_strict bindings
  | (id, None, rhs) :: rem ->
      bind_inits rem
  | (id, Some(loc, shape), rhs) :: rem ->
      Llet(Strict, id, Lapply(mod_prim "init_mod", [loc; shape], Location.none),
           bind_inits rem)
  et bind_strict = fonction
    [] ->
      patch_forwards bindings
  | (id, None, rhs) :: rem ->
      Llet(Strict, id, rhs, bind_strict rem)
  | (id, Some(loc, shape), rhs) :: rem ->
      bind_strict rem
  et patch_forwards = fonction
    [] ->
      cont
  | (id, None, rhs) :: rem ->
      patch_forwards rem
  | (id, Some(loc, shape), rhs) :: rem ->
      Lsequence(Lapply(mod_prim "update_mod", [shape; Lvar id; rhs],
                       Location.none),
                patch_forwards rem)
  dans
    bind_inits bindings

soit compile_recmodule compile_rhs bindings cont =
  eval_rec_bindings
    (reorder_rec_bindings
       (List.map
          (fonc {mb_id=id; mb_expr=modl; _} ->
            (id, modl.mod_loc, init_shape modl, compile_rhs id modl))
          bindings))
    cont

(* Extract the list of "value" identifiers bound by a signature.
   "Value" identifiers are identifiers for signature components that
   correspond to a run-time value: values, exceptions, modules, classes.
   Note: manifest primitives do not correspond to a run-time value! *)

soit rec bound_value_identifiers = fonction
    [] -> []
  | Sig_value(id, {val_kind = Val_reg}) :: rem ->
      id :: bound_value_identifiers rem
  | Sig_exception(id, decl) :: rem -> id :: bound_value_identifiers rem
  | Sig_module(id, mty, _) :: rem -> id :: bound_value_identifiers rem
  | Sig_class(id, decl, _) :: rem -> id :: bound_value_identifiers rem
  | _ :: rem -> bound_value_identifiers rem

(* Compile a module expression *)

soit rec transl_module cc rootpath mexp =
  filtre mexp.mod_type avec
    Mty_alias _ -> apply_coercion Alias cc lambda_unit
  | _ ->
  filtre mexp.mod_desc avec
    Tmod_ident (path,_) ->
      apply_coercion StrictOpt cc
        (transl_path ~loc:mexp.mod_loc mexp.mod_env path)
  | Tmod_structure str ->
      transl_struct [] cc rootpath str
  | Tmod_functor( param, _, mty, body) ->
      soit bodypath = functor_path rootpath param dans
      oo_wrap mexp.mod_env vrai
        (fonction
        | Tcoerce_none ->
            Lfunction(Curried, [param],
                      transl_module Tcoerce_none bodypath body)
        | Tcoerce_functor(ccarg, ccres) ->
            soit param' = Ident.create "funarg" dans
            Lfunction(Curried, [param'],
                      Llet(Alias, param,
                           apply_coercion Alias ccarg (Lvar param'),
                           transl_module ccres bodypath body))
        | _ ->
            fatal_error "Translmod.transl_module")
        cc
  | Tmod_apply(funct, arg, ccarg) ->
      oo_wrap mexp.mod_env vrai
        (apply_coercion Strict cc)
        (Lapply(transl_module Tcoerce_none None funct,
                [transl_module ccarg None arg], mexp.mod_loc))
  | Tmod_constraint(arg, mty, _, ccarg) ->
      transl_module (compose_coercions cc ccarg) rootpath arg
  | Tmod_unpack(arg, _) ->
      apply_coercion Strict cc (Translcore.transl_exp arg)

et transl_struct fields cc rootpath str =
  transl_structure fields cc rootpath str.str_items

et transl_structure fields cc rootpath = fonction
    [] ->
      début filtre cc avec
        Tcoerce_none ->
          Lprim(Pmakeblock(0, Immutable),
                List.map (fonc id -> Lvar id) (List.rev fields))
      | Tcoerce_structure(pos_cc_list, id_pos_list) ->
              (* ignore id_pos_list as the ids are already bound *)
          soit v = Array.of_list (List.rev fields) dans
          (*List.fold_left
            (fun lam (id, pos) -> Llet(Alias, id, Lvar v.(pos), lam))*)
            (Lprim(Pmakeblock(0, Immutable),
                List.map
                  (fonc (pos, cc) ->
                    filtre cc avec
                      Tcoerce_primitive p -> transl_primitive Location.none p
                    | _ -> apply_coercion Strict cc (Lvar v.(pos)))
                  pos_cc_list))
            (*id_pos_list*)
      | _ ->
          fatal_error "Translmod.transl_structure"
      fin
  | item :: rem ->
      filtre item.str_desc avec
      | Tstr_eval (expr, _) ->
      Lsequence(transl_exp expr, transl_structure fields cc rootpath rem)
  | Tstr_value(rec_flag, pat_expr_list) ->
      soit ext_fields = rev_let_bound_idents pat_expr_list @ fields dans
      transl_let rec_flag pat_expr_list
                 (transl_structure ext_fields cc rootpath rem)
  | Tstr_primitive descr ->
      record_primitive descr.val_val;
      transl_structure fields cc rootpath rem
  | Tstr_type(decls) ->
      transl_structure fields cc rootpath rem
  | Tstr_exception decl ->
      soit id = decl.cd_id dans
      Llet(Strict, id, transl_exception (field_path rootpath id) decl,
           transl_structure (id :: fields) cc rootpath rem)
  | Tstr_exn_rebind( id, _, path, {Location.loc=loc}, _) ->
      Llet(Strict, id, transl_path ~loc item.str_env path,
           transl_structure (id :: fields) cc rootpath rem)
  | Tstr_module mb ->
      soit id = mb.mb_id dans
      Llet(pure_module mb.mb_expr, id,
           transl_module Tcoerce_none (field_path rootpath id) mb.mb_expr,
           transl_structure (id :: fields) cc rootpath rem)
  | Tstr_recmodule bindings ->
      soit ext_fields =
        List.rev_append (List.map (fonc mb -> mb.mb_id) bindings) fields
      dans
      compile_recmodule
        (fonc id modl ->
          transl_module Tcoerce_none (field_path rootpath id) modl)
        bindings
        (transl_structure ext_fields cc rootpath rem)
  | Tstr_class cl_list ->
      soit ids = List.map (fonc (ci,_,_) -> ci.ci_id_class) cl_list dans
      Lletrec(List.map
              (fonc (ci, meths, vf) ->
                soit id = ci.ci_id_class dans
                soit cl = ci.ci_expr dans
                  (id, transl_class ids id meths cl vf ))
                cl_list,
              transl_structure (List.rev ids @ fields) cc rootpath rem)
  | Tstr_include(modl, sg, _) ->
      soit ids = bound_value_identifiers sg dans
      soit mid = Ident.create "include" dans
      soit rec rebind_idents pos newfields = fonction
        [] ->
          transl_structure newfields cc rootpath rem
      | id :: ids ->
          Llet(Alias, id, Lprim(Pfield pos, [Lvar mid]),
               rebind_idents (pos + 1) (id :: newfields) ids) dans
      Llet(pure_module modl, mid, transl_module Tcoerce_none None modl,
           rebind_idents 0 fields ids)

  | Tstr_modtype _
  | Tstr_open _
  | Tstr_class_type _
  | Tstr_attribute _ ->
      transl_structure fields cc rootpath rem

et pure_module m =
  filtre m.mod_desc avec
    Tmod_ident _ -> Alias
  | Tmod_constraint (m,_,_,_) -> pure_module m
  | _ -> Strict

(* Update forward declaration in Translcore *)
soit _ =
  Translcore.transl_module := transl_module

(* Compile an implementation *)

soit transl_implementation module_name (str, cc) =
  reset_labels ();
  primitive_declarations := [];
  soit module_id = Ident.create_persistent module_name dans
  Lprim(Psetglobal module_id,
        [transl_label_init
            (transl_struct [] cc (global_path module_id) str)])


(* Build the list of value identifiers defined by a toplevel structure
   (excluding primitive declarations). *)

soit rec defined_idents = fonction
    [] -> []
  | item :: rem ->
    filtre item.str_desc avec
    | Tstr_eval (expr, _) -> defined_idents rem
    | Tstr_value(rec_flag, pat_expr_list) ->
      let_bound_idents pat_expr_list @ defined_idents rem
    | Tstr_primitive desc -> defined_idents rem
    | Tstr_type decls -> defined_idents rem
    | Tstr_exception decl -> decl.cd_id :: defined_idents rem
    | Tstr_exn_rebind(id, _, path, _, _) -> id :: defined_idents rem
    | Tstr_module mb -> mb.mb_id :: defined_idents rem
    | Tstr_recmodule decls ->
      List.map (fonc mb -> mb.mb_id) decls @ defined_idents rem
    | Tstr_modtype _ -> defined_idents rem
    | Tstr_open _ -> defined_idents rem
    | Tstr_class cl_list ->
      List.map (fonc (ci, _, _) -> ci.ci_id_class) cl_list @ defined_idents rem
    | Tstr_class_type cl_list -> defined_idents rem
    | Tstr_include(modl, sg, _) -> bound_value_identifiers sg @ defined_idents rem
    | Tstr_attribute _ -> defined_idents rem

(* second level idents (module M = struct ... let id = ... end),
   and all sub-levels idents *)
soit rec more_idents = fonction
    [] -> []
  | item :: rem ->
    filtre item.str_desc avec
    | Tstr_eval (expr, _attrs) -> more_idents rem
    | Tstr_value(rec_flag, pat_expr_list) -> more_idents rem
    | Tstr_primitive _ -> more_idents rem
    | Tstr_type decls -> more_idents rem
    | Tstr_exception _ -> more_idents rem
    | Tstr_exn_rebind(id, _, path, _, _) -> more_idents rem
    | Tstr_recmodule decls -> more_idents rem
    | Tstr_modtype _ -> more_idents rem
    | Tstr_open _ -> more_idents rem
    | Tstr_class cl_list -> more_idents rem
    | Tstr_class_type cl_list -> more_idents rem
    | Tstr_include(modl, _, _) -> more_idents rem
    | Tstr_module {mb_expr={mod_desc = Tmod_structure str}} ->
        all_idents str.str_items @ more_idents rem
    | Tstr_module _ -> more_idents rem
    | Tstr_attribute _ -> more_idents rem

et all_idents = fonction
    [] -> []
  | item :: rem ->
    filtre item.str_desc avec
    | Tstr_eval (expr, _attrs) -> all_idents rem
    | Tstr_value(rec_flag, pat_expr_list) ->
      let_bound_idents pat_expr_list @ all_idents rem
    | Tstr_primitive _ -> all_idents rem
    | Tstr_type decls -> all_idents rem
    | Tstr_exception decl -> decl.cd_id :: all_idents rem
    | Tstr_exn_rebind(id, _, path, _, _) -> id :: all_idents rem
    | Tstr_recmodule decls ->
      List.map (fonc mb -> mb.mb_id) decls @ all_idents rem
    | Tstr_modtype _ -> all_idents rem
    | Tstr_open _ -> all_idents rem
    | Tstr_class cl_list ->
      List.map (fonc (ci, _, _) -> ci.ci_id_class) cl_list @ all_idents rem
    | Tstr_class_type cl_list -> all_idents rem
    | Tstr_include(modl, sg, _) -> bound_value_identifiers sg @ all_idents rem
    | Tstr_module {mb_id;mb_expr={mod_desc = Tmod_structure str}} ->
        mb_id :: all_idents str.str_items @ all_idents rem
    | Tstr_module mb -> mb.mb_id :: all_idents rem
    | Tstr_attribute _ -> all_idents rem


(* A variant of transl_structure used to compile toplevel structure definitions
   for the native-code compiler. Store the defined values in the fields
   of the global as soon as they are defined, in order to reduce register
   pressure.  Also rewrites the defining expressions so that they
   refer to earlier fields of the structure through the fields of
   the global, not by their names.
   "map" is a table from defined idents to (pos in global block, coercion).
   "prim" is a list of (pos in global block, primitive declaration). *)

soit transl_store_subst = ref Ident.empty
  (** In the native toplevel, this reference is threaded through successive
      calls of transl_store_structure *)

soit nat_toplevel_name id =
  essaie filtre Ident.find_same id !transl_store_subst avec
    | Lprim(Pfield pos, [Lprim(Pgetglobal glob, [])]) -> (glob,pos)
    | _ -> raise Not_found
  avec Not_found ->
    fatal_error("Translmod.nat_toplevel_name: " ^ Ident.unique_name id)

soit transl_store_structure glob map prims str =
  soit rec transl_store rootpath subst = fonction
    [] ->
      transl_store_subst := subst;
        lambda_unit
    | item :: rem ->
        filtre item.str_desc avec
  | Tstr_eval (expr, _attrs) ->
      Lsequence(subst_lambda subst (transl_exp expr),
                transl_store rootpath subst rem)
  | Tstr_value(rec_flag, pat_expr_list) ->
      soit ids = let_bound_idents pat_expr_list dans
      soit lam = transl_let rec_flag pat_expr_list (store_idents ids) dans
      Lsequence(subst_lambda subst lam,
                transl_store rootpath (add_idents faux ids subst) rem)
  | Tstr_primitive descr ->
      record_primitive descr.val_val;
      transl_store rootpath subst rem
  | Tstr_type(decls) ->
      transl_store rootpath subst rem
  | Tstr_exception decl ->
      soit id = decl.cd_id dans
      soit lam = transl_exception (field_path rootpath id) decl dans
      Lsequence(Llet(Strict, id, lam, store_ident id),
                transl_store rootpath (add_ident faux id subst) rem)
  | Tstr_exn_rebind( id, _, path, {Location.loc=loc}, _) ->
      soit lam = subst_lambda subst (transl_path ~loc item.str_env path) dans
      Lsequence(Llet(Strict, id, lam, store_ident id),
                transl_store rootpath (add_ident faux id subst) rem)
  | Tstr_module{mb_id=id; mb_expr={mod_desc = Tmod_structure str}} ->
    soit lam = transl_store (field_path rootpath id) subst str.str_items dans
      (* Careful: see next case *)
    soit subst = !transl_store_subst dans
    Lsequence(lam,
              Llet(Strict, id,
                   subst_lambda subst
                   (Lprim(Pmakeblock(0, Immutable),
                          List.map (fonc id -> Lvar id)
                                   (defined_idents str.str_items))),
                   Lsequence(store_ident id,
                             transl_store rootpath (add_ident vrai id subst)
                                          rem)))
  | Tstr_module{mb_id=id; mb_expr=modl} ->
      soit lam = transl_module Tcoerce_none (field_path rootpath id) modl dans
      (* Careful: the module value stored in the global may be different
         from the local module value, in case a coercion is applied.
         If so, keep using the local module value (id) in the remainder of
         the compilation unit (add_ident true returns subst unchanged).
         If not, we can use the value from the global
         (add_ident true adds id -> Pgetglobal... to subst). *)
      Llet(Strict, id, subst_lambda subst lam,
        Lsequence(store_ident id,
                  transl_store rootpath (add_ident vrai id subst) rem))
  | Tstr_recmodule bindings ->
      soit ids = List.map (fonc mb -> mb.mb_id) bindings dans
      compile_recmodule
        (fonc id modl ->
          subst_lambda subst
            (transl_module Tcoerce_none
                           (field_path rootpath id) modl))
        bindings
        (Lsequence(store_idents ids,
                   transl_store rootpath (add_idents vrai ids subst) rem))
  | Tstr_class cl_list ->
      soit ids = List.map (fonc (ci, _, _) -> ci.ci_id_class) cl_list dans
      soit lam =
        Lletrec(List.map
              (fonc (ci, meths, vf) ->
                soit id = ci.ci_id_class dans
                soit cl = ci.ci_expr dans
                     (id, transl_class ids id meths cl vf))
                  cl_list,
                store_idents ids) dans
      Lsequence(subst_lambda subst lam,
                transl_store rootpath (add_idents faux ids subst) rem)
  | Tstr_include(modl, sg, _attrs) ->
      soit ids = bound_value_identifiers sg dans
      soit mid = Ident.create "include" dans
      soit rec store_idents pos = fonction
        [] -> transl_store rootpath (add_idents vrai ids subst) rem
      | id :: idl ->
          Llet(Alias, id, Lprim(Pfield pos, [Lvar mid]),
               Lsequence(store_ident id, store_idents (pos + 1) idl)) dans
      Llet(Strict, mid,
           subst_lambda subst (transl_module Tcoerce_none None modl),
           store_idents 0 ids)
  | Tstr_modtype _
  | Tstr_open _
  | Tstr_class_type _
  | Tstr_attribute _ ->
      transl_store rootpath subst rem

  et store_ident id =
    essaie
      soit (pos, cc) = Ident.find_same id map dans
      soit init_val = apply_coercion Alias cc (Lvar id) dans
      Lprim(Psetfield(pos, faux), [Lprim(Pgetglobal glob, []); init_val])
    avec Not_found ->
      fatal_error("Translmod.store_ident: " ^ Ident.unique_name id)

  et store_idents idlist =
    make_sequence store_ident idlist

  et add_ident may_coerce id subst =
    essaie
      soit (pos, cc) = Ident.find_same id map dans
      filtre cc avec
        Tcoerce_none ->
          Ident.add id (Lprim(Pfield pos, [Lprim(Pgetglobal glob, [])])) subst
      | _ ->
          si may_coerce alors subst sinon affirme faux
    avec Not_found ->
      affirme faux

  et add_idents may_coerce idlist subst =
    List.fold_right (add_ident may_coerce) idlist subst

  et store_primitive (pos, prim) cont =
    Lsequence(Lprim(Psetfield(pos, faux),
                    [Lprim(Pgetglobal glob, []);
                     transl_primitive Location.none prim]),
              cont)

  dans List.fold_right store_primitive prims
                     (transl_store (global_path glob) !transl_store_subst str)

(* Transform a coercion and the list of value identifiers defined by
   a toplevel structure into a table [id -> (pos, coercion)],
   with [pos] being the position in the global block where the value of
   [id] must be stored, and [coercion] the coercion to be applied to it.
   A given identifier may appear several times
   in the coercion (if it occurs several times in the signature); remember
   to assign it the position of its last occurrence.
   Identifiers that are not exported are assigned positions at the
   end of the block (beyond the positions of all exported idents).
   Also compute the total size of the global block,
   and the list of all primitives exported as values. *)

soit build_ident_map restr idlist more_ids =
  soit rec natural_map pos map prims = fonction
    [] ->
      (map, prims, pos)
  | id :: rem ->
      natural_map (pos+1) (Ident.add id (pos, Tcoerce_none) map) prims rem dans
  soit (map, prims, pos) =
    filtre restr avec
        Tcoerce_none ->
          natural_map 0 Ident.empty [] idlist
      | Tcoerce_structure (pos_cc_list, _id_pos_list) ->
              (* ignore _id_pos_list as the ids are already bound *)
        soit idarray = Array.of_list idlist dans
        soit rec export_map pos map prims undef = fonction
        [] ->
          natural_map pos map prims undef
          | (source_pos, Tcoerce_primitive p) :: rem ->
            export_map (pos + 1) map ((pos, p) :: prims) undef rem
          | (source_pos, cc) :: rem ->
            soit id = idarray.(source_pos) dans
            export_map (pos + 1) (Ident.add id (pos, cc) map)
              prims (list_remove id undef) rem
        dans export_map 0 Ident.empty [] idlist pos_cc_list
      | _ ->
        fatal_error "Translmod.build_ident_map"
  dans
  natural_map pos map prims more_ids

(* Compile an implementation using transl_store_structure
   (for the native-code compiler). *)

soit transl_store_gen module_name ({ str_items = str }, restr) topl =
  reset_labels ();
  primitive_declarations := [];
  soit module_id = Ident.create_persistent module_name dans
  soit (map, prims, size) =
    build_ident_map restr (defined_idents str) (more_idents str) dans
  soit f = fonction
    | [ { str_desc = Tstr_eval (expr, _attrs) } ] quand topl ->
        affirme (size = 0);
        subst_lambda !transl_store_subst (transl_exp expr)
    | str -> transl_store_structure module_id map prims str dans
  transl_store_label_init module_id size f str
  (*size, transl_label_init (transl_store_structure module_id map prims str)*)

soit transl_store_phrases module_name str =
  transl_store_gen module_name (str,Tcoerce_none) vrai

soit transl_store_implementation module_name (str, restr) =
  soit s = !transl_store_subst dans
  transl_store_subst := Ident.empty;
  soit r = transl_store_gen module_name (str, restr) faux dans
  transl_store_subst := s;
  r

(* Compile a toplevel phrase *)

soit toploop_ident = Ident.create_persistent "Toploop"
soit toploop_getvalue_pos = 0 (* position of getvalue in module Toploop *)
soit toploop_setvalue_pos = 1 (* position of setvalue in module Toploop *)

soit aliased_idents = ref Ident.empty

soit set_toplevel_unique_name id =
  aliased_idents :=
    Ident.add id (Ident.unique_toplevel_name id) !aliased_idents

soit toplevel_name id =
  essaie Ident.find_same id !aliased_idents
  avec Not_found -> Ident.name id

soit toploop_getvalue id =
  Lapply(Lprim(Pfield toploop_getvalue_pos,
                 [Lprim(Pgetglobal toploop_ident, [])]),
         [Lconst(Const_base(Const_string (toplevel_name id, None)))],
         Location.none)

soit toploop_setvalue id lam =
  Lapply(Lprim(Pfield toploop_setvalue_pos,
                 [Lprim(Pgetglobal toploop_ident, [])]),
         [Lconst(Const_base(Const_string (toplevel_name id, None))); lam],
         Location.none)

soit toploop_setvalue_id id = toploop_setvalue id (Lvar id)

soit close_toplevel_term lam =
  IdentSet.fold (fonc id l -> Llet(Strict, id, toploop_getvalue id, l))
                (free_variables lam) lam

soit transl_toplevel_item item =
  filtre item.str_desc avec
    Tstr_eval (expr, _attrs) ->
      transl_exp expr
  | Tstr_value(rec_flag, pat_expr_list) ->
      soit idents = let_bound_idents pat_expr_list dans
      transl_let rec_flag pat_expr_list
                 (make_sequence toploop_setvalue_id idents)
  | Tstr_exception decl ->
      toploop_setvalue decl.cd_id (transl_exception None decl)
  | Tstr_exn_rebind(id, _, path, {Location.loc=loc}, _) ->
      toploop_setvalue id (transl_path ~loc item.str_env path)
  | Tstr_module {mb_id=id; mb_expr=modl} ->
      (* we need to use the unique name for the module because of issues
         with "open" (PR#1672) *)
      set_toplevel_unique_name id;
      soit lam = transl_module Tcoerce_none (Some(Pident id)) modl dans
      toploop_setvalue id lam
  | Tstr_recmodule bindings ->
      soit idents = List.map (fonc mb -> mb.mb_id) bindings dans
      compile_recmodule
        (fonc id modl -> transl_module Tcoerce_none (Some(Pident id)) modl)
        bindings
        (make_sequence toploop_setvalue_id idents)
  | Tstr_class cl_list ->
      (* we need to use unique names for the classes because there might
         be a value named identically *)
      soit ids = List.map (fonc (ci, _, _) -> ci.ci_id_class) cl_list dans
      List.iter set_toplevel_unique_name ids;
      Lletrec(List.map
          (fonc (ci, meths, vf) ->
            soit id = ci.ci_id_class dans
            soit cl = ci.ci_expr dans
                   (id, transl_class ids id meths cl vf))
                cl_list,
              make_sequence
                (fonc (ci, _, _) -> toploop_setvalue_id ci.ci_id_class)
                cl_list)
  | Tstr_include(modl, sg, _attrs) ->
      soit ids = bound_value_identifiers sg dans
      soit mid = Ident.create "include" dans
      soit rec set_idents pos = fonction
        [] ->
          lambda_unit
      | id :: ids ->
          Lsequence(toploop_setvalue id (Lprim(Pfield pos, [Lvar mid])),
                    set_idents (pos + 1) ids) dans
      Llet(Strict, mid, transl_module Tcoerce_none None modl, set_idents 0 ids)
  | Tstr_modtype _
  | Tstr_open _
  | Tstr_primitive _
  | Tstr_type _
  | Tstr_class_type _
  | Tstr_attribute _ ->
      lambda_unit

soit transl_toplevel_item_and_close itm =
  close_toplevel_term (transl_label_init (transl_toplevel_item itm))

soit transl_toplevel_definition str =
  reset_labels ();
  make_sequence transl_toplevel_item_and_close str.str_items

(* Compile the initialization code for a packed library *)

soit get_component = fonction
    None -> Lconst const_unit
  | Some id -> Lprim(Pgetglobal id, [])

soit transl_package component_names target_name coercion =
  soit components =
    Lprim(Pmakeblock(0, Immutable), List.map get_component component_names) dans
  Lprim(Psetglobal target_name, [apply_coercion Strict coercion components])
  (*
  let components =
    match coercion with
      Tcoerce_none ->
        List.map get_component component_names
    | Tcoerce_structure (pos_cc_list, id_pos_list) ->
              (* ignore id_pos_list as the ids are already bound *)
        let g = Array.of_list component_names in
        List.map
          (fun (pos, cc) -> apply_coercion Strict cc (get_component g.(pos)))
          pos_cc_list
    | _ ->
        assert false in
  Lprim(Psetglobal target_name, [Lprim(Pmakeblock(0, Immutable), components)])
   *)

soit transl_store_package component_names target_name coercion =
  soit rec make_sequence fn pos arg =
    filtre arg avec
      [] -> lambda_unit
    | hd :: tl -> Lsequence(fn pos hd, make_sequence fn (pos + 1) tl) dans
  filtre coercion avec
    Tcoerce_none ->
      (List.length component_names,
       make_sequence
         (fonc pos id ->
           Lprim(Psetfield(pos, faux),
                 [Lprim(Pgetglobal target_name, []);
                  get_component id]))
         0 component_names)
  | Tcoerce_structure (pos_cc_list, id_pos_list) ->
      soit components =
        Lprim(Pmakeblock(0, Immutable), List.map get_component component_names)
      dans
      soit blk = Ident.create "block" dans
      (List.length pos_cc_list,
       Llet (Strict, blk, apply_coercion Strict coercion components,
             make_sequence
               (fonc pos id ->
                 Lprim(Psetfield(pos, faux),
                       [Lprim(Pgetglobal target_name, []);
                        Lprim(Pfield pos, [Lvar blk])]))
               0 pos_cc_list))
  (*    
              (* ignore id_pos_list as the ids are already bound *)
      let id = Array.of_list component_names in
      (List.length pos_cc_list,
       make_sequence
         (fun dst (src, cc) ->
           Lprim(Psetfield(dst, false),
                 [Lprim(Pgetglobal target_name, []);
                  apply_coercion Strict cc (get_component id.(src))]))
         0 pos_cc_list)
  *)
  | _ -> affirme faux

(* Error report *)

ouvre Format

soit report_error ppf = fonction
    Circular_dependency id ->
      fprintf ppf
        "@[Cannot safely evaluate the definition@ \
         of the recursively-defined module %a@]"
        Printtyp.ident id

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, err) ->
        Some (Location.error_of_printer loc report_error err)
      | _ ->
        None
    )
