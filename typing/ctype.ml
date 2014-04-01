(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(* Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt*)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Operations on core types *)

ouvre Misc
ouvre Asttypes
ouvre Types
ouvre Btype

(*
   Type manipulation after type inference
   ======================================
   If one wants to manipulate a type after type inference (for
   instance, during code generation or in the debugger), one must
   first make sure that the type levels are correct, using the
   function [correct_levels]. Then, this type can be correctely
   manipulated by [apply], [expand_head] and [moregeneral].
*)

(*
   General notes
   =============
   - As much sharing as possible should be kept : it makes types
     smaller and better abbreviated.
     When necessary, some sharing can be lost. Types will still be
     printed correctly (+++ TO DO...), and abbreviations defined by a
     class do not depend on sharing thanks to constrained
     abbreviations. (Of course, even if some sharing is lost, typing
     will still be correct.)
   - All nodes of a type have a level : that way, one know whether a
     node need to be duplicated or not when instantiating a type.
   - Levels of a type are decreasing (generic level being considered
     as greatest).
   - The level of a type constructor is superior to the binding
     time of its path.
   - Recursive types without limitation should be handled (even if
     there is still an occur check). This avoid treating specially the
     case for objects, for instance. Furthermore, the occur check
     policy can then be easily changed.
*)

(*
   A faire
   =======
   - Revoir affichage des types.
   - Etendre la portee d'un alias [... as 'a] a tout le type englobant.
   - #-type implementes comme de vraies abreviations.
   - Niveaux plus fins pour les identificateurs :
       Champ [global] renomme en [level];
       Niveau -1 : global
               0 : module toplevel
               1 : module contenu dans module toplevel
              ...
     En fait, incrementer le niveau a chaque fois que l'on rentre dans
     un module.

       3   4 6
        \ / /
       1 2 5
        \|/
         0

     [Subst] doit ecreter les niveaux (pour qu'un variable non
     generalisable dans un module de niveau 2 ne se retrouve pas
     generalisable lorsque l'on l'utilise au niveau 0).

   - Traitement de la trace de l'unification separe de la fonction
     [unify].
*)

(**** Errors ****)

exception Unify de (type_expr * type_expr) list

exception Tags de label * label

soit () =
  Location.register_error_of_exn
    (fonction
      | Tags (l, l') ->
          Some
            Location.
              (errorf ~loc:(in_file !input_name)
                 "In this program,@ variant constructors@ `%s and `%s@ \
                  have the same hash value.@ Change one of them." l l'
              )
      | _ -> None
    )

exception Subtype de
        (type_expr * type_expr) list * (type_expr * type_expr) list

exception Cannot_expand

exception Cannot_apply

exception Recursive_abbrev

(* GADT: recursive abbrevs can appear as a result of local constraints *)
exception Unification_recursive_abbrev de (type_expr * type_expr) list

(**** Type level management ****)

soit current_level = ref 0
soit nongen_level = ref 0
soit global_level = ref 1
soit saved_level = ref []

soit get_current_level () = !current_level
soit init_def level = current_level := level; nongen_level := level
soit begin_def () =
  saved_level := (!current_level, !nongen_level) :: !saved_level;
  incr current_level; nongen_level := !current_level
soit begin_class_def () =
  saved_level := (!current_level, !nongen_level) :: !saved_level;
  incr current_level
soit raise_nongen_level () =
  saved_level := (!current_level, !nongen_level) :: !saved_level;
  nongen_level := !current_level
soit end_def () =
  soit (cl, nl) = List.hd !saved_level dans
  saved_level := List.tl !saved_level;
  current_level := cl; nongen_level := nl

soit reset_global_level () =
  global_level := !current_level + 1
soit increase_global_level () =
  soit gl = !global_level dans
  global_level := !current_level;
  gl
soit restore_global_level gl =
  global_level := gl

(**** Whether a path points to an object type (with hidden row variable) ****)
soit is_object_type path =
  soit name =
    filtre path avec Path.Pident id -> Ident.name id
    | Path.Pdot(_, s,_) -> s
    | Path.Papply _ -> affirme faux
  dans name.[0] = '#'

(**** Control tracing of GADT instances *)

soit trace_gadt_instances = ref faux
soit check_trace_gadt_instances env =
  not !trace_gadt_instances && Env.has_local_constraints env &&
  (trace_gadt_instances := vrai; cleanup_abbrev (); vrai)

soit reset_trace_gadt_instances b =
  si b alors trace_gadt_instances := faux

soit wrap_trace_gadt_instances env f x =
  soit b = check_trace_gadt_instances env dans
  soit y = f x dans
  reset_trace_gadt_instances b;
  y

(**** Abbreviations without parameters ****)
(* Shall reset after generalizing *)

soit simple_abbrevs = ref Mnil

soit proper_abbrevs path tl abbrev =
  si tl <> [] || !trace_gadt_instances || !Clflags.principal ||
     is_object_type path
  alors abbrev
  sinon simple_abbrevs

(**** Some type creators ****)

(* Re-export generic type creators *)

soit newty2             = Btype.newty2
soit newty desc         = newty2 !current_level desc
soit new_global_ty desc = newty2 !global_level desc

soit newvar ?name ()         = newty2 !current_level (Tvar name)
soit newvar2 ?name level     = newty2 level (Tvar name)
soit new_global_var ?name () = newty2 !global_level (Tvar name)

soit newobj fields      = newty (Tobject (fields, ref None))

soit newconstr path tyl = newty (Tconstr (path, tyl, ref Mnil))

soit none = newty (Ttuple [])                (* Clearly ill-formed type *)

(**** Representative of a type ****)

(* Re-export repr *)
soit repr = repr

(**** Type maps ****)

module TypePairs =
  Hashtbl.Make (struct
    type t = type_expr * type_expr
    soit equal (t1, t1') (t2, t2') = (t1 == t2) && (t1' == t2')
    soit hash (t, t') = t.id + 93 * t'.id
 fin)


(**** unification mode ****)

type unification_mode =
  | Expression (* unification in expression *)
  | Pattern (* unification in pattern which may add local constraints *)

soit umode = ref Expression
soit generate_equations = ref faux

soit set_mode mode ?(generate = (mode = Pattern)) f =
  soit old_unification_mode = !umode
  et old_gen = !generate_equations dans
  essaie
    umode := mode;
    generate_equations := generate;
    soit ret = f () dans
    umode := old_unification_mode;
    generate_equations := old_gen;
    ret
  avec e ->
    umode := old_unification_mode;
    generate_equations := old_gen;
    raise e


(*** Checks for type definitions ***)

soit in_current_module = fonction
  | Path.Pident _ -> vrai
  | Path.Pdot _ | Path.Papply _ -> faux

soit in_pervasives p =
  in_current_module p &&
  essaie ignore (Env.find_type p Env.initial); vrai
  avec Not_found -> faux

soit is_datatype decl=
  filtre decl.type_kind avec
    Type_record _ | Type_variant _ -> vrai
  | Type_abstract -> faux


                  (**********************************************)
                  (*  Miscellaneous operations on object types  *)
                  (**********************************************)

(* Note:
   We need to maintain some invariants:
   * cty_self must be a Tobject
   * ...
*)

(**** Object field manipulation. ****)

soit object_fields ty =
  filtre (repr ty).desc avec
    Tobject (fields, _) -> fields
  | _                   -> affirme faux

soit flatten_fields ty =
  soit rec flatten l ty =
    soit ty = repr ty dans
    filtre ty.desc avec
      Tfield(s, k, ty1, ty2) ->
        flatten ((s, k, ty1)::l) ty2
    | _ ->
        (l, ty)
  dans
    soit (l, r) = flatten [] ty dans
    (Sort.list (fonc (n, _, _) (n', _, _) -> n < n') l, r)

soit build_fields level =
  List.fold_right
    (fonc (s, k, ty1) ty2 -> newty2 level (Tfield(s, k, ty1, ty2)))

soit associate_fields fields1 fields2 =
  soit rec associate p s s' =
    fonction
      (l, []) ->
        (List.rev p, (List.rev s) @ l, List.rev s')
    | ([], l') ->
        (List.rev p, List.rev s, (List.rev s') @ l')
    | ((n, k, t)::r, (n', k', t')::r') quand n = n' ->
        associate ((n, k, t, k', t')::p) s s' (r, r')
    | ((n, k, t)::r, ((n', k', t')::_ tel l')) quand n < n' ->
        associate p ((n, k, t)::s) s' (r, l')
    | (((n, k, t)::r tel l), (n', k', t')::r') (* when n > n' *) ->
        associate p s ((n', k', t')::s') (l, r')
  dans
  associate [] [] [] (fields1, fields2)

(**** Check whether an object is open ****)

(* +++ Il faudra penser a eventuellement expanser l'abreviation *)
soit rec object_row ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tobject (t, _)     -> object_row t
  | Tfield(_, _, _, t) -> object_row t
  | _ -> ty

soit opened_object ty =
  filtre (object_row ty).desc avec
  | Tvar _  | Tunivar _ | Tconstr _ -> vrai
  | _                               -> faux

soit concrete_object ty =
  filtre (object_row ty).desc avec
  | Tvar _             -> faux
  | _                  -> vrai

(**** Close an object ****)

soit close_object ty =
  soit rec close ty =
    soit ty = repr ty dans
    filtre ty.desc avec
      Tvar _ ->
        link_type ty (newty2 ty.level Tnil)
    | Tfield(_, _, _, ty') -> close ty'
    | _                    -> affirme faux
  dans
  filtre (repr ty).desc avec
    Tobject (ty, _)   -> close ty
  | _                 -> affirme faux

(**** Row variable of an object type ****)

soit row_variable ty =
  soit rec find ty =
    soit ty = repr ty dans
    filtre ty.desc avec
      Tfield (_, _, _, ty) -> find ty
    | Tvar _               -> ty
    | _                    -> affirme faux
  dans
  filtre (repr ty).desc avec
    Tobject (fi, _) -> find fi
  | _               -> affirme faux

(**** Object name manipulation ****)
(* +++ Bientot obsolete *)

soit set_object_name id rv params ty =
  filtre (repr ty).desc avec
    Tobject (fi, nm) ->
      set_name nm (Some (Path.Pident id, rv::params))
  | _ ->
      affirme faux

soit remove_object_name ty =
  filtre (repr ty).desc avec
    Tobject (_, nm)   -> set_name nm None
  | Tconstr (_, _, _) -> ()
  | _                 -> fatal_error "Ctype.remove_object_name"

(**** Hiding of private methods ****)

soit hide_private_methods ty =
  filtre (repr ty).desc avec
    Tobject (fi, nm) ->
      nm := None;
      soit (fl, _) = flatten_fields fi dans
      List.iter
        (fonction (_, k, _) ->
          filtre field_kind_repr k avec
            Fvar r -> set_kind r Fabsent
          | _      -> ())
        fl
  | _ ->
      affirme faux


                              (*******************************)
                              (*  Operations on class types  *)
                              (*******************************)


soit rec signature_of_class_type =
  fonction
    Cty_constr (_, _, cty) -> signature_of_class_type cty
  | Cty_signature sign     -> sign
  | Cty_arrow (_, ty, cty)   -> signature_of_class_type cty

soit self_type cty =
  repr (signature_of_class_type cty).csig_self

soit rec class_type_arity =
  fonction
    Cty_constr (_, _, cty) ->  class_type_arity cty
  | Cty_signature _        ->  0
  | Cty_arrow (_, _, cty)    ->  1 + class_type_arity cty


                  (*******************************************)
                  (*  Miscellaneous operations on row types  *)
                  (*******************************************)

soit sort_row_fields = Sort.list (fonc (p,_) (q,_) -> p < q)

soit rec merge_rf r1 r2 pairs fi1 fi2 =
  filtre fi1, fi2 avec
    (l1,f1 tel p1)::fi1', (l2,f2 tel p2)::fi2' ->
      si l1 = l2 alors merge_rf r1 r2 ((l1,f1,f2)::pairs) fi1' fi2' sinon
      si l1 < l2 alors merge_rf (p1::r1) r2 pairs fi1' fi2 sinon
      merge_rf r1 (p2::r2) pairs fi1 fi2'
  | [], _ -> (List.rev r1, List.rev_append r2 fi2, pairs)
  | _, [] -> (List.rev_append r1 fi1, List.rev r2, pairs)

soit merge_row_fields fi1 fi2 =
  filtre fi1, fi2 avec
    [], _ | _, [] -> (fi1, fi2, [])
  | [p1], _ quand not (List.mem_assoc (fst p1) fi2) -> (fi1, fi2, [])
  | _, [p2] quand not (List.mem_assoc (fst p2) fi1) -> (fi1, fi2, [])
  | _ -> merge_rf [] [] [] (sort_row_fields fi1) (sort_row_fields fi2)

soit rec filter_row_fields erase = fonction
    [] -> []
  | (l,f tel p)::fi ->
      soit fi = filter_row_fields erase fi dans
      filtre row_field_repr f avec
        Rabsent -> fi
      | Reither(_,_,faux,e) quand erase -> set_row_field e Rabsent; fi
      | _ -> p :: fi

                    (**************************************)
                    (*  Check genericity of type schemes  *)
                    (**************************************)


exception Non_closed

soit rec closed_schema_rec ty =
  soit ty = repr ty dans
  si ty.level >= lowest_level alors début
    soit level = ty.level dans
    ty.level <- pivot_level - level;
    filtre ty.desc avec
      Tvar _ quand level <> generic_level ->
        raise Non_closed
    | Tfield(_, kind, t1, t2) ->
        si field_kind_repr kind = Fpresent alors
          closed_schema_rec t1;
        closed_schema_rec t2
    | Tvariant row ->
        soit row = row_repr row dans
        iter_row closed_schema_rec row;
        si not (static_row row) alors closed_schema_rec row.row_more
    | _ ->
        iter_type_expr closed_schema_rec ty
  fin

(* Return whether all variables of type [ty] are generic. *)
soit closed_schema ty =
  essaie
    closed_schema_rec ty;
    unmark_type ty;
    vrai
  avec Non_closed ->
    unmark_type ty;
    faux

exception Non_closed de type_expr * bool

soit free_variables = ref []
soit really_closed = ref None

soit rec free_vars_rec real ty =
  soit ty = repr ty dans
  si ty.level >= lowest_level alors début
    ty.level <- pivot_level - ty.level;
    début filtre ty.desc, !really_closed avec
      Tvar _, _ ->
        free_variables := (ty, real) :: !free_variables
    | Tconstr (path, tl, _), Some env ->
        début essaie
          soit (_, body, _) = Env.find_type_expansion path env dans
          si (repr body).level <> generic_level alors
            free_variables := (ty, real) :: !free_variables
        avec Not_found -> ()
        fin;
        List.iter (free_vars_rec vrai) tl
(* Do not count "virtual" free variables
    | Tobject(ty, {contents = Some (_, p)}) ->
        free_vars_rec false ty; List.iter (free_vars_rec true) p
*)
    | Tobject (ty, _), _ ->
        free_vars_rec faux ty
    | Tfield (_, _, ty1, ty2), _ ->
        free_vars_rec vrai ty1; free_vars_rec faux ty2
    | Tvariant row, _ ->
        soit row = row_repr row dans
        iter_row (free_vars_rec vrai) row;
        si not (static_row row) alors free_vars_rec faux row.row_more
    | _    ->
        iter_type_expr (free_vars_rec vrai) ty
    fin;
  fin

soit free_vars ?env ty =
  free_variables := [];
  really_closed := env;
  free_vars_rec vrai ty;
  soit res = !free_variables dans
  free_variables := [];
  really_closed := None;
  res

soit free_variables ?env ty =
  soit tl = List.map fst (free_vars ?env ty) dans
  unmark_type ty;
  tl

soit closed_type ty =
  filtre free_vars ty avec
      []           -> ()
  | (v, real) :: _ -> raise (Non_closed (v, real))

soit closed_parameterized_type params ty =
  List.iter mark_type params;
  soit ok =
    essaie closed_type ty; vrai avec Non_closed _ -> faux dans
  List.iter unmark_type params;
  unmark_type ty;
  ok

soit closed_type_decl decl =
  essaie
    List.iter mark_type decl.type_params;
    début filtre decl.type_kind avec
      Type_abstract ->
        ()
    | Type_variant v ->
        List.iter
          (fonc {cd_args; cd_res; _} ->
            filtre cd_res avec
            | Some _ -> ()
            | None -> List.iter closed_type cd_args)
          v
    | Type_record(r, rep) ->
        List.iter (fonc l -> closed_type l.ld_type) r
    fin;
    début filtre decl.type_manifest avec
      None    -> ()
    | Some ty -> closed_type ty
    fin;
    unmark_type_decl decl;
    None
  avec Non_closed (ty, _) ->
    unmark_type_decl decl;
    Some ty

type closed_class_failure =
    CC_Method de type_expr * bool * string * type_expr
  | CC_Value de type_expr * bool * string * type_expr

exception Failure de closed_class_failure

soit closed_class params sign =
  soit ty = object_fields (repr sign.csig_self) dans
  soit (fields, rest) = flatten_fields ty dans
  List.iter mark_type params;
  mark_type rest;
  List.iter
    (fonc (lab, _, ty) -> si lab = dummy_method alors mark_type ty)
    fields;
  essaie
    mark_type_node (repr sign.csig_self);
    List.iter
      (fonc (lab, kind, ty) ->
        si field_kind_repr kind = Fpresent alors
        essaie closed_type ty avec Non_closed (ty0, real) ->
          raise (Failure (CC_Method (ty0, real, lab, ty))))
      fields;
    mark_type_params (repr sign.csig_self);
    List.iter unmark_type params;
    unmark_class_signature sign;
    None
  avec Failure reason ->
    mark_type_params (repr sign.csig_self);
    List.iter unmark_type params;
    unmark_class_signature sign;
    Some reason


                            (**********************)
                            (*  Type duplication  *)
                            (**********************)


(* Duplicate a type, preserving only type variables *)
soit duplicate_type ty =
  Subst.type_expr Subst.identity ty

(* Same, for class types *)
soit duplicate_class_type ty =
  Subst.class_type Subst.identity ty


                         (*****************************)
                         (*  Type level manipulation  *)
                         (*****************************)

(*
   It would be a bit more efficient to remove abbreviation expansions
   rather than generalizing them: these expansions will usually not be
   used anymore. However, this is not possible in the general case, as
   [expand_abbrev] (via [subst]) requires these expansions to be
   preserved. Does it worth duplicating this code ?
*)
soit rec iter_generalize tyl ty =
  soit ty = repr ty dans
  si (ty.level > !current_level) && (ty.level <> generic_level) alors début
    set_level ty generic_level;
    début filtre ty.desc avec
      Tconstr (_, _, abbrev) ->
        iter_abbrev (iter_generalize tyl) !abbrev
    | _ -> ()
    fin;
    iter_type_expr (iter_generalize tyl) ty
  fin sinon
    tyl := ty :: !tyl

soit iter_generalize tyl ty =
  simple_abbrevs := Mnil;
  iter_generalize tyl ty

soit generalize ty =
  iter_generalize (ref []) ty

(* Efficient repeated generalisation of the same type *)
soit iterative_generalization min_level tyl =
  soit tyl' = ref [] dans
  List.iter (iter_generalize tyl') tyl;
  List.fold_right (fonc ty l -> si ty.level <= min_level alors l sinon ty::l)
    !tyl' []

(* Generalize the structure and lower the variables *)

soit rec generalize_structure var_level ty =
  soit ty = repr ty dans
  si ty.level <> generic_level alors début
    si is_Tvar ty && ty.level > var_level alors
      set_level ty var_level
    sinon si
      ty.level > !current_level &&
      filtre ty.desc avec
        Tconstr (p, _, abbrev) ->
          not (is_object_type p) && (abbrev := Mnil; vrai)
      | _ -> vrai
    alors début
      set_level ty generic_level;
      iter_type_expr (generalize_structure var_level) ty
    fin
  fin

soit generalize_structure var_level ty =
  simple_abbrevs := Mnil;
  generalize_structure var_level ty

(* Generalize the spine of a function, if the level >= !current_level *)

soit rec generalize_spine ty =
  soit ty = repr ty dans
  si ty.level < !current_level || ty.level = generic_level alors () sinon
  filtre ty.desc avec
    Tarrow (_, ty1, ty2, _) ->
      set_level ty generic_level;
      generalize_spine ty1;
      generalize_spine ty2;
  | Tpoly (ty', _) ->
      set_level ty generic_level;
      generalize_spine ty'
  | Ttuple tyl
  | Tpackage (_, _, tyl) ->
      set_level ty generic_level;
      List.iter generalize_spine tyl
  | Tconstr (p, tyl, memo) quand not (is_object_type p) ->
      set_level ty generic_level;
      memo := Mnil;
      List.iter generalize_spine tyl
  | _ -> ()

soit forward_try_expand_once = (* Forward declaration *)
  ref (fonc env ty -> raise Cannot_expand)

(*
   Lower the levels of a type (assume [level] is not
   [generic_level]).
*)
(*
    The level of a type constructor must be greater than its binding
    time. That way, a type constructor cannot escape the scope of its
    definition, as would be the case in
      let x = ref []
      module M = struct type t let _ = (x : t list ref) end
    (without this constraint, the type system would actually be unsound.)
*)
soit get_level env p =
  essaie
    filtre (Env.find_type p env).type_newtype_level avec
      | None -> Path.binding_time p
      | Some (x, _) -> x
  avec
    | Not_found ->
      (* no newtypes in predef *)
      Path.binding_time p

soit rec normalize_package_path env p =
  soit t =
    essaie (Env.find_modtype p env).mtd_type
    avec Not_found -> None
  dans
  filtre t avec
  | Some (Mty_ident p) -> normalize_package_path env p
  | Some (Mty_signature _ | Mty_functor _ | Mty_alias _) | None -> p

soit rec update_level env level ty =
  soit ty = repr ty dans
  si ty.level > level alors début
    début filtre Env.gadt_instance_level env ty avec
      Some lv -> si level < lv alors raise (Unify [(ty, newvar2 level)])
    | None -> ()
    fin;
    filtre ty.desc avec
      Tconstr(p, tl, abbrev) quand level < get_level env p ->
        (* Try first to replace an abbreviation by its expansion. *)
        début essaie
          (* if is_newtype env p then raise Cannot_expand; *)
          link_type ty (!forward_try_expand_once env ty);
          update_level env level ty
        avec Cannot_expand ->
          (* +++ Levels should be restored... *)
          (* Format.printf "update_level: %i < %i@." level (get_level env p); *)
          si level < get_level env p alors raise (Unify [(ty, newvar2 level)]);
          iter_type_expr (update_level env level) ty
        fin
    | Tpackage (p, nl, tl) quand level < get_level env p ->
        soit p' = normalize_package_path env p dans
        si Path.same p p' alors raise (Unify [(ty, newvar2 level)]);
        log_type ty; ty.desc <- Tpackage (p', nl, tl);
        update_level env level ty
    | Tobject(_, ({contents=Some(p, tl)} tel nm))
      quand level < get_level env p ->
        set_name nm None;
        update_level env level ty
    | Tvariant row ->
        soit row = row_repr row dans
        début filtre row.row_name avec
        | Some (p, tl) quand level < get_level env p ->
            log_type ty;
            ty.desc <- Tvariant {row avec row_name = None}
        | _ -> ()
        fin;
        set_level ty level;
        iter_type_expr (update_level env level) ty
    | Tfield(lab, _, ty1, _)
      quand lab = dummy_method && (repr ty1).level > level ->
        raise (Unify [(ty1, newvar2 level)])
    | _ ->
        set_level ty level;
        (* XXX what about abbreviations in Tconstr ? *)
        iter_type_expr (update_level env level) ty
  fin

(* Generalize and lower levels of contravariant branches simultaneously *)

soit generalize_contravariant env =
  si !Clflags.principal alors generalize_structure sinon update_level env

soit rec generalize_expansive env var_level ty =
  soit ty = repr ty dans
  si ty.level <> generic_level alors début
    si ty.level > var_level alors début
      set_level ty generic_level;
      filtre ty.desc avec
        Tconstr (path, tyl, abbrev) ->
          soit variance =
            essaie (Env.find_type path env).type_variance
            avec Not_found -> List.map (fonc _ -> Variance.may_inv) tyl dans
          abbrev := Mnil;
          List.iter2
            (fonc v t ->
              si Variance.(mem May_weak v)
              alors generalize_contravariant env var_level t
              sinon generalize_expansive env var_level t)
            variance tyl
      | Tpackage (_, _, tyl) ->
          List.iter (generalize_contravariant env var_level) tyl
      | Tarrow (_, t1, t2, _) ->
          generalize_contravariant env var_level t1;
          generalize_expansive env var_level t2
      | _ ->
          iter_type_expr (generalize_expansive env var_level) ty
    fin
  fin

soit generalize_expansive env ty =
  simple_abbrevs := Mnil;
  essaie
    generalize_expansive env !nongen_level ty
  avec Unify ([_, ty'] tel tr) ->
    raise (Unify ((ty, ty') :: tr))

soit generalize_global ty = generalize_structure !global_level ty
soit generalize_structure ty = generalize_structure !current_level ty

(* Correct the levels of type [ty]. *)
soit correct_levels ty =
  duplicate_type ty

(* Only generalize the type ty0 in ty *)
soit limited_generalize ty0 ty =
  soit ty0 = repr ty0 dans

  soit graph = Hashtbl.create 17 dans
  soit idx = ref lowest_level dans
  soit roots = ref [] dans

  soit rec inverse pty ty =
    soit ty = repr ty dans
    si (ty.level > !current_level) || (ty.level = generic_level) alors début
      decr idx;
      Hashtbl.add graph !idx (ty, ref pty);
      si (ty.level = generic_level) || (ty == ty0) alors
        roots := ty :: !roots;
      set_level ty !idx;
      iter_type_expr (inverse [ty]) ty
    fin sinon si ty.level < lowest_level alors début
      soit (_, parents) = Hashtbl.find graph ty.level dans
      parents := pty @ !parents
    fin

  et generalize_parents ty =
    soit idx = ty.level dans
    si idx <> generic_level alors début
      set_level ty generic_level;
      List.iter generalize_parents !(snd (Hashtbl.find graph idx));
      (* Special case for rows: must generalize the row variable *)
      filtre ty.desc avec
        Tvariant row ->
          soit more = row_more row dans
          soit lv = more.level dans
          si (lv < lowest_level || lv > !current_level)
          && lv <> generic_level alors set_level more generic_level
      | _ -> ()
    fin
  dans

  inverse [] ty;
  si ty0.level < lowest_level alors
    iter_type_expr (inverse []) ty0;
  List.iter generalize_parents !roots;
  Hashtbl.iter
    (fonc _ (ty, _) ->
       si ty.level <> generic_level alors set_level ty !current_level)
    graph


(* Compute statically the free univars of all nodes in a type *)
(* This avoids doing it repeatedly during instantiation *)

type inv_type_expr =
    { inv_type : type_expr;
      modifiable inv_parents : inv_type_expr list }

soit rec inv_type hash pty ty =
  soit ty = repr ty dans
  essaie
    soit inv = TypeHash.find hash ty dans
    inv.inv_parents <- pty @ inv.inv_parents
  avec Not_found ->
    soit inv = { inv_type = ty; inv_parents = pty } dans
    TypeHash.add hash ty inv;
    iter_type_expr (inv_type hash [inv]) ty

soit compute_univars ty =
  soit inverted = TypeHash.create 17 dans
  inv_type inverted [] ty;
  soit node_univars = TypeHash.create 17 dans
  soit rec add_univar univ inv =
    filtre inv.inv_type.desc avec
      Tpoly (ty, tl) quand List.memq univ (List.map repr tl) -> ()
    | _ ->
        essaie
          soit univs = TypeHash.find node_univars inv.inv_type dans
          si not (TypeSet.mem univ !univs) alors début
            univs := TypeSet.add univ !univs;
            List.iter (add_univar univ) inv.inv_parents
          fin
        avec Not_found ->
          TypeHash.add node_univars inv.inv_type (ref(TypeSet.singleton univ));
          List.iter (add_univar univ) inv.inv_parents
  dans
  TypeHash.iter (fonc ty inv -> si is_Tunivar ty alors add_univar ty inv)
    inverted;
  fonc ty ->
    essaie !(TypeHash.find node_univars ty) avec Not_found -> TypeSet.empty


                              (*******************)
                              (*  Instantiation  *)
                              (*******************)


soit rec find_repr p1 =
  fonction
    Mnil ->
      None
  | Mcons (Public, p2, ty, _, _) quand Path.same p1 p2 ->
      Some ty
  | Mcons (_, _, _, _, rem) ->
      find_repr p1 rem
  | Mlink {contents = rem} ->
      find_repr p1 rem

(*
   Generic nodes are duplicated, while non-generic nodes are left
   as-is.
   During instantiation, the description of a generic node is first
   replaced by a link to a stub ([Tsubst (newvar ())]). Once the
   copy is made, it replaces the stub.
   After instantiation, the description of generic node, which was
   stored by [save_desc], must be put back, using [cleanup_types].
*)

soit abbreviations = ref (ref Mnil)
  (* Abbreviation memorized. *)

(* partial: we may not wish to copy the non generic types
   before we call type_pat *)
soit rec copy ?env ?partial ?keep_names ty =
  soit copy = copy ?env ?partial ?keep_names dans
  soit ty = repr ty dans
  filtre ty.desc avec
    Tsubst ty -> ty
  | _ ->
    si ty.level <> generic_level && partial = None alors ty sinon
    (* We only forget types that are non generic and do not contain
       free univars *)
    soit forget =
      si ty.level = generic_level alors generic_level sinon
      filtre partial avec
        None -> affirme faux
      | Some (free_univars, keep) ->
          si TypeSet.is_empty (free_univars ty) alors
            si keep alors ty.level sinon !current_level
          sinon generic_level
    dans
    si forget <> generic_level alors newty2 forget (Tvar None) sinon
    soit desc = ty.desc dans
    save_desc ty desc;
    soit t = newvar() dans          (* Stub *)
    début filtre env avec
      Some env quand Env.has_local_constraints env ->
        début filtre Env.gadt_instance_level env ty avec
          Some lv -> Env.add_gadt_instances env lv [t]
        | None -> ()
        fin
    | _ -> ()
    fin;
    ty.desc <- Tsubst t;
    t.desc <-
      début filtre desc avec
      | Tconstr (p, tl, _) ->
          soit abbrevs = proper_abbrevs p tl !abbreviations dans
          début filtre find_repr p !abbrevs avec
            Some ty quand repr ty != t -> (* XXX Commentaire... *)
              Tlink ty
          | _ ->
          (*
             One must allocate a new reference, so that abbrevia-
             tions belonging to different branches of a type are
             independent.
             Moreover, a reference containing a [Mcons] must be
             shared, so that the memorized expansion of an abbrevi-
             ation can be released by changing the content of just
             one reference.
          *)
              Tconstr (p, List.map copy tl,
                       ref (filtre !(!abbreviations) avec
                              Mcons _ -> Mlink !abbreviations
                            | abbrev  -> abbrev))
          fin
      | Tvariant row0 ->
          soit row = row_repr row0 dans
          soit more = repr row.row_more dans
          (* We must substitute in a subtle way *)
          (* Tsubst takes a tuple containing the row var and the variant *)
          début filtre more.desc avec
            Tsubst {desc = Ttuple [_;ty2]} ->
              (* This variant type has been already copied *)
              ty.desc <- Tsubst ty2; (* avoid Tlink in the new type *)
              Tlink ty2
          | _ ->
              (* If the row variable is not generic, we must keep it *)
              soit keep = more.level <> generic_level dans
              soit more' =
                filtre more.desc avec
                  Tsubst ty -> ty
                | Tconstr _ | Tnil ->
                    si keep alors save_desc more more.desc;
                    copy more
                | Tvar _ | Tunivar _ ->
                    save_desc more more.desc;
                    si keep alors more sinon newty more.desc
                |  _ -> affirme faux
              dans
              soit row =
                filtre repr more' avec (* PR#6163 *)
                  {desc=Tconstr _} quand not row.row_fixed ->
                    {row avec row_fixed = vrai}
                | _ -> row
              dans
              (* Open row if partial for pattern and contains Reither *)
              soit more', row =
                filtre partial avec
                  Some (free_univars, faux) quand row.row_closed
                  && not row.row_fixed && TypeSet.is_empty (free_univars ty) ->
                    soit not_reither (_, f) =
                      filtre row_field_repr f avec
                        Reither _ -> faux
                      | _ -> vrai
                    dans
                    si List.for_all not_reither row.row_fields
                    alors (more', row) sinon
                    (newty2 (si keep alors more.level sinon !current_level)
                       (Tvar None),
                     {row_fields = List.filter not_reither row.row_fields;
                      row_more = more; row_bound = ();
                      row_closed = faux; row_fixed = faux; row_name = None})
                | _ -> (more', row)
              dans
              (* Register new type first for recursion *)
              more.desc <- Tsubst(newgenty(Ttuple[more';t]));
              (* Return a new copy *)
              Tvariant (copy_row copy vrai row keep more')
          fin
      | Tfield (p, k, ty1, ty2) ->
          début filtre field_kind_repr k avec
            Fabsent  -> Tlink (copy ty2)
          | Fpresent -> copy_type_desc copy desc
          | Fvar r ->
              dup_kind r;
              copy_type_desc copy desc
          fin
      | Tobject (ty1, _) quand partial <> None ->
          Tobject (copy ty1, ref None)
      | _ -> copy_type_desc ?keep_names copy desc
      fin;
    t

soit simple_copy t = copy t

(**** Variants of instantiations ****)

soit gadt_env env =
  si Env.has_local_constraints env
  alors Some env
  sinon None

soit instance ?partial env sch =
  soit env = gadt_env env dans
  soit partial =
    filtre partial avec
      None -> None
    | Some keep -> Some (compute_univars sch, keep)
  dans
  soit ty = copy ?env ?partial sch dans
  cleanup_types ();
  ty

soit instance_def sch =
  soit ty = copy sch dans
  cleanup_types ();
  ty

soit instance_list env schl =
  soit env = gadt_env env dans
  soit tyl = List.map (fonc t -> copy ?env t) schl dans
  cleanup_types ();
  tyl

soit reified_var_counter = ref Vars.empty

(* names given to new type constructors.
   Used for existential types and
   local constraints *)
soit get_new_abstract_name s =
  soit index =
    essaie Vars.find s !reified_var_counter + 1
    avec Not_found -> 0 dans
  reified_var_counter := Vars.add s index !reified_var_counter;
  Printf.sprintf "%s#%d" s index

soit new_declaration newtype manifest =
  {
    type_params = [];
    type_arity = 0;
    type_kind = Type_abstract;
    type_private = Public;
    type_manifest = manifest;
    type_variance = [];
    type_newtype_level = newtype;
    type_loc = Location.none;
    type_attributes = [];
  }

soit instance_constructor ?in_pattern cstr =
  début filtre in_pattern avec
  | None -> ()
  | Some (env, newtype_lev) ->
      soit process existential =
        soit decl = new_declaration (Some (newtype_lev, newtype_lev)) None dans
        soit name =
          filtre repr existential avec
            {desc = Tvar (Some name)} -> name
          | _ -> "ex"
        dans
        soit (id, new_env) =
          Env.enter_type (get_new_abstract_name name) decl !env dans
        env := new_env;
        soit to_unify = newty (Tconstr (Path.Pident id,[],ref Mnil)) dans
        soit tv = copy existential dans
        affirme (is_Tvar tv);
        link_type tv to_unify
      dans
      List.iter process cstr.cstr_existentials
  fin;
  soit ty_res = copy cstr.cstr_res dans
  soit ty_args = List.map simple_copy  cstr.cstr_args dans
  cleanup_types ();
  (ty_args, ty_res)

soit instance_parameterized_type ?keep_names sch_args sch =
  soit ty_args = List.map (fonc t -> copy ?keep_names t) sch_args dans
  soit ty = copy sch dans
  cleanup_types ();
  (ty_args, ty)

soit instance_parameterized_type_2 sch_args sch_lst sch =
  soit ty_args = List.map simple_copy sch_args dans
  soit ty_lst = List.map simple_copy sch_lst dans
  soit ty = copy sch dans
  cleanup_types ();
  (ty_args, ty_lst, ty)

soit instance_declaration decl =
  soit decl =
    {decl avec type_params = List.map simple_copy decl.type_params;
     type_manifest = may_map simple_copy decl.type_manifest;
     type_kind = filtre decl.type_kind avec
     | Type_abstract -> Type_abstract
     | Type_variant cl ->
         Type_variant (
           List.map
             (fonc c ->
                {c avec cd_args=List.map simple_copy c.cd_args;
                        cd_res=may_map simple_copy c.cd_res})
             cl)
     | Type_record (fl, rr) ->
         Type_record (
           List.map
             (fonc l ->
                {l avec ld_type = copy l.ld_type}
             ) fl, rr)
    }
  dans
  cleanup_types ();
  decl

soit instance_class params cty =
  soit rec copy_class_type =
    fonction
      Cty_constr (path, tyl, cty) ->
        Cty_constr (path, List.map simple_copy tyl, copy_class_type cty)
    | Cty_signature sign ->
        Cty_signature
          {csig_self = copy sign.csig_self;
           csig_vars =
             Vars.map (fonction (m, v, ty) -> (m, v, copy ty)) sign.csig_vars;
           csig_concr = sign.csig_concr;
           csig_inher =
             List.map (fonc (p,tl) -> (p, List.map simple_copy tl))
               sign.csig_inher}
    | Cty_arrow (l, ty, cty) ->
        Cty_arrow (l, copy ty, copy_class_type cty)
  dans
  soit params' = List.map simple_copy params dans
  soit cty' = copy_class_type cty dans
  cleanup_types ();
  (params', cty')

(**** Instanciation for types with free universal variables ****)

soit rec diff_list l1 l2 =
  si l1 == l2 alors [] sinon
  filtre l1 avec [] -> invalid_arg "Ctype.diff_list"
  | a :: l1 -> a :: diff_list l1 l2

soit conflicts free bound =
  soit bound = List.map repr bound dans
  TypeSet.exists (fonc t -> List.memq (repr t) bound) free

soit delayed_copy = ref []
    (* copying to do later *)

(* Copy without sharing until there are no free univars left *)
(* all free univars must be included in [visited]            *)
soit rec copy_sep fixed free bound visited ty =
  soit ty = repr ty dans
  soit univars = free ty dans
  si TypeSet.is_empty univars alors
    si ty.level <> generic_level alors ty sinon
    soit t = newvar () dans
    delayed_copy :=
      paresseux (t.desc <- Tlink (copy ty))
      :: !delayed_copy;
    t
  sinon essaie
    soit t, bound_t = List.assq ty visited dans
    soit dl = si is_Tunivar ty alors [] sinon diff_list bound bound_t dans
    si dl <> [] && conflicts univars dl alors raise Not_found;
    t
  avec Not_found -> début
    soit t = newvar() dans          (* Stub *)
    soit visited =
      filtre ty.desc avec
        Tarrow _ | Ttuple _ | Tvariant _ | Tconstr _ | Tobject _ | Tpackage _ ->
          (ty,(t,bound)) :: visited
      | _ -> visited dans
    soit copy_rec = copy_sep fixed free bound visited dans
    t.desc <-
      début filtre ty.desc avec
      | Tvariant row0 ->
          soit row = row_repr row0 dans
          soit more = repr row.row_more dans
          (* We shall really check the level on the row variable *)
          soit keep = is_Tvar more && more.level <> generic_level dans
          soit more' = copy_rec more dans
          soit fixed' = fixed && is_Tvar (repr more') dans
          soit row = copy_row copy_rec fixed' row keep more' dans
          Tvariant row
      | Tpoly (t1, tl) ->
          soit tl = List.map repr tl dans
          soit tl' = List.map (fonc t -> newty t.desc) tl dans
          soit bound = tl @ bound dans
          soit visited =
            List.map2 (fonc ty t -> ty,(t,bound)) tl tl' @ visited dans
          Tpoly (copy_sep fixed free bound visited t1, tl')
      | _ -> copy_type_desc copy_rec ty.desc
      fin;
    t
  fin

soit instance_poly ?(keep_names=faux) fixed univars sch =
  soit univars = List.map repr univars dans
  soit copy_var ty =
    filtre ty.desc avec
      Tunivar name -> si keep_names alors newty (Tvar name) sinon newvar ()
    | _ -> affirme faux
  dans
  soit vars = List.map copy_var univars dans
  soit pairs = List.map2 (fonc u v -> u, (v, [])) univars vars dans
  delayed_copy := [];
  soit ty = copy_sep fixed (compute_univars sch) [] pairs sch dans
  List.iter Lazy.force !delayed_copy;
  delayed_copy := [];
  cleanup_types ();
  vars, ty

soit instance_label fixed lbl =
  soit ty_res = copy lbl.lbl_res dans
  soit vars, ty_arg =
    filtre repr lbl.lbl_arg avec
      {desc = Tpoly (ty, tl)} ->
        instance_poly fixed tl ty
    | ty ->
        [], copy lbl.lbl_arg
  dans
  cleanup_types ();
  (vars, ty_arg, ty_res)

(**** Instantiation with parameter substitution ****)

soit unify' = (* Forward declaration *)
  ref (fonc env ty1 ty2 -> raise (Unify []))

soit subst env level priv abbrev ty params args body =
  si List.length params <> List.length args alors raise (Unify []);
  soit old_level = !current_level dans
  current_level := level;
  essaie
    soit body0 = newvar () dans          (* Stub *)
    début filtre ty avec
      None      -> ()
    | Some ({desc = Tconstr (path, tl, _)} tel ty) ->
        soit abbrev = proper_abbrevs path tl abbrev dans
        memorize_abbrev abbrev priv path ty body0
    | _ ->
        affirme faux
    fin;
    abbreviations := abbrev;
    soit (params', body') = instance_parameterized_type params body dans
    abbreviations := ref Mnil;
    !unify' env body0 body';
    List.iter2 (!unify' env) params' args;
    current_level := old_level;
    body'
  avec Unify _ tel exn ->
    current_level := old_level;
    raise exn

(*
   Only the shape of the type matters, not whether is is generic or
   not. [generic_level] might be somewhat slower, but it ensures
   invariants on types are enforced (decreasing levels.), and we don't
   care about efficiency here.
*)
soit apply env params body args =
  essaie
    subst env generic_level Public (ref Mnil) None params args body
  avec
    Unify _ -> raise Cannot_apply


                              (****************************)
                              (*  Abbreviation expansion  *)
                              (****************************)

(*
   If the environnement has changed, memorized expansions might not
   be correct anymore, and so we flush the cache. This is safe but
   quite pessimistic: it would be enough to flush the cache when a
   type or module definition is overridden in the environnement.
*)
soit previous_env = ref Env.empty
soit string_of_kind = fonction Public -> "public" | Private -> "private"
soit check_abbrev_env env =
  si env != !previous_env alors début
    (* prerr_endline "cleanup expansion cache"; *)
    cleanup_abbrev ();
    previous_env := env
  fin


(* Expand an abbreviation. The expansion is memorized. *)
(*
   Assume the level is greater than the path binding time of the
   expanded abbreviation.
*)
(*
   An abbreviation expansion will fail in either of these cases:
   1. The type constructor does not correspond to a manifest type.
   2. The type constructor is defined in an external file, and this
      file is not in the path (missing -I options).
   3. The type constructor is not in the "local" environment. This can
      happens when a non-generic type variable has been instantiated
      afterwards to the not yet defined type constructor. (Actually,
      this cannot happen at the moment due to the strong constraints
      between type levels and constructor binding time.)
   4. The expansion requires the expansion of another abbreviation,
      and this other expansion fails.
*)
soit expand_abbrev_gen kind find_type_expansion env ty =
  check_abbrev_env env;
  filtre ty avec
    {desc = Tconstr (path, args, abbrev); level = level} ->
      soit lookup_abbrev = proper_abbrevs path args abbrev dans
      début filtre find_expans kind path !lookup_abbrev avec
        Some ty ->
          (* prerr_endline
            ("found a "^string_of_kind kind^" expansion for "^Path.name path);*)
          si level <> generic_level alors
            début essaie
              update_level env level ty
            avec Unify _ ->
              (* XXX This should not happen.
                 However, levels are not correctly restored after a
                 typing error *)
              ()
            fin;
          ty
      | None ->
          soit (params, body, lv) =
            essaie find_type_expansion path env avec Not_found ->
              raise Cannot_expand
          dans
          (* prerr_endline
            ("add a "^string_of_kind kind^" expansion for "^Path.name path);*)
          soit ty' = subst env level kind abbrev (Some ty) params args body dans
          (* Hack to name the variant type *)
          début filtre repr ty' avec
            {desc=Tvariant row} tel ty quand static_row row ->
              ty.desc <- Tvariant { row avec row_name = Some (path, args) }
          | _ -> ()
          fin;
          (* For gadts, remember type as non exportable *)
          (* The ambiguous level registered for ty' should be the highest *)
          si !trace_gadt_instances alors début
            filtre max lv (Env.gadt_instance_level env ty) avec
              None -> ()
            | Some lv ->
                si level < lv alors raise (Unify [(ty, newvar2 level)]);
                Env.add_gadt_instances env lv [ty; ty']
          fin;
          ty'
      fin
  | _ ->
      affirme faux

(* Expand respecting privacy *)
soit expand_abbrev ty =
  expand_abbrev_gen Public Env.find_type_expansion ty

(* Expand once the head of a type *)
soit expand_head_once env ty =
  essaie expand_abbrev env (repr ty) avec Cannot_expand -> affirme faux

(* Check whether a type can be expanded *)
soit safe_abbrev env ty =
  soit snap = Btype.snapshot () dans
  essaie ignore (expand_abbrev env ty); vrai
  avec Cannot_expand | Unify _ ->
    Btype.backtrack snap;
    faux

(* Expand the head of a type once.
   Raise Cannot_expand if the type cannot be expanded.
   May raise Unify, if a recursion was hidden in the type. *)
soit try_expand_once env ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tconstr (p, _, _) -> repr (expand_abbrev env ty)
  | _ -> raise Cannot_expand

(* This one only raises Cannot_expand *)
soit try_expand_safe env ty =
  soit snap = Btype.snapshot () dans
  essaie try_expand_once env ty
  avec Unify _ ->
    Btype.backtrack snap; raise Cannot_expand

(* Fully expand the head of a type. *)
soit rec try_expand_head try_once env ty =
  soit ty' = try_once env ty dans
  essaie try_expand_head try_once env ty'
  avec Cannot_expand -> ty'

soit try_expand_head try_once env ty =
  soit ty' = try_expand_head try_once env ty dans
  début filtre Env.gadt_instance_level env ty' avec
    None -> ()
  | Some lv -> Env.add_gadt_instance_chain env lv ty
  fin;
  ty'

(* Unsafe full expansion, may raise Unify. *)
soit expand_head_unif env ty =
  essaie try_expand_head try_expand_once env ty avec Cannot_expand -> repr ty

(* Safe version of expand_head, never fails *)
soit expand_head env ty =
  essaie try_expand_head try_expand_safe env ty avec Cannot_expand -> repr ty

soit _ = forward_try_expand_once := try_expand_safe


(* Expand until we find a non-abstract type declaration *)

soit rec extract_concrete_typedecl env ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tconstr (p, _, _) ->
      soit decl = Env.find_type p env dans
      si decl.type_kind <> Type_abstract alors (p, p, decl) sinon
      soit ty =
        essaie try_expand_once env ty avec Cannot_expand -> raise Not_found
      dans
      soit (_, p', decl) = extract_concrete_typedecl env ty dans
        (p, p', decl)
  | _ -> raise Not_found

(* Implementing function [expand_head_opt], the compiler's own version of
   [expand_head] used for type-based optimisations.
   [expand_head_opt] uses [Env.find_type_expansion_opt] to access the
   manifest type information of private abstract data types which is
   normally hidden to the type-checker out of the implementation module of
   the private abbreviation. *)

soit expand_abbrev_opt =
  expand_abbrev_gen Private Env.find_type_expansion_opt

soit try_expand_once_opt env ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tconstr _ -> repr (expand_abbrev_opt env ty)
  | _ -> raise Cannot_expand

soit rec try_expand_head_opt env ty =
  soit ty' = try_expand_once_opt env ty dans
  début essaie
    try_expand_head_opt env ty'
  avec Cannot_expand ->
    ty'
  fin

soit expand_head_opt env ty =
  soit snap = Btype.snapshot () dans
  essaie try_expand_head_opt env ty
  avec Cannot_expand | Unify _ -> (* expand_head shall never fail *)
    Btype.backtrack snap;
    repr ty

(* Make sure that the type parameters of the type constructor [ty]
   respect the type constraints *)
soit enforce_constraints env ty =
  filtre ty avec
    {desc = Tconstr (path, args, abbrev); level = level} ->
      début essaie
        soit decl = Env.find_type path env dans
        ignore
          (subst env level Public (ref Mnil) None decl.type_params args
             (newvar2 level))
      avec Not_found -> ()
      fin
  | _ ->
      affirme faux

(* Recursively expand the head of a type.
   Also expand #-types. *)
soit full_expand env ty =
  soit ty = repr (expand_head env ty) dans
  filtre ty.desc avec
    Tobject (fi, {contents = Some (_, v::_)}) quand is_Tvar (repr v) ->
      newty2 ty.level (Tobject (fi, ref None))
  | _ ->
      ty

(*
   Check whether the abbreviation expands to a well-defined type.
   During the typing of a class, abbreviations for correspondings
   types expand to non-generic types.
*)
soit generic_abbrev env path =
  essaie
    soit (_, body, _) = Env.find_type_expansion path env dans
    (repr body).level = generic_level
  avec
    Not_found ->
      faux

soit generic_private_abbrev env path =
  essaie
    filtre Env.find_type path env avec
      {type_kind = Type_abstract;
       type_private = Private;
       type_manifest = Some body} ->
         (repr body).level = generic_level
    | _ -> faux
  avec Not_found -> faux

                              (*****************)
                              (*  Occur check  *)
                              (*****************)


exception Occur

(* The marks are already used by [expand_abbrev]... *)
soit visited = ref []

soit rec non_recursive_abbrev env ty0 ty =
  soit ty = repr ty dans
  si ty == repr ty0 alors raise Recursive_abbrev;
  si not (List.memq ty !visited) alors début
    visited := ty :: !visited;
    filtre ty.desc avec
      Tconstr(p, args, abbrev) ->
        début essaie
          non_recursive_abbrev env ty0 (try_expand_once_opt env ty)
        avec Cannot_expand ->
          si !Clflags.recursive_types &&
            (in_pervasives p ||
             essaie is_datatype (Env.find_type p env) avec Not_found -> faux)
          alors ()
          sinon iter_type_expr (non_recursive_abbrev env ty0) ty
        fin
    | Tobject _ | Tvariant _ ->
        ()
    | _ ->
        si !Clflags.recursive_types alors () sinon
        iter_type_expr (non_recursive_abbrev env ty0) ty
  fin

soit correct_abbrev env path params ty =
  check_abbrev_env env;
  soit ty0 = newgenvar () dans
  visited := [];
  soit abbrev = Mcons (Public, path, ty0, ty0, Mnil) dans
  simple_abbrevs := abbrev;
  essaie
    non_recursive_abbrev env ty0
      (subst env generic_level Public (ref abbrev) None [] [] ty);
    simple_abbrevs := Mnil;
    visited := []
  avec exn ->
    simple_abbrevs := Mnil;
    visited := [];
    raise exn

soit rec occur_rec env visited ty0 ty =
  si ty == ty0  alors raise Occur;
  filtre ty.desc avec
    Tconstr(p, tl, abbrev) ->
      début essaie
        si List.memq ty visited || !Clflags.recursive_types alors raise Occur;
        iter_type_expr (occur_rec env (ty::visited) ty0) ty
      avec Occur -> essaie
        soit ty' = try_expand_head try_expand_once env ty dans
        (* Maybe we could simply make a recursive call here,
           but it seems it could make the occur check loop
           (see change in rev. 1.58) *)
        si ty' == ty0 || List.memq ty' visited alors raise Occur;
        filtre ty'.desc avec
          Tobject _ | Tvariant _ -> ()
        | _ ->
            si not !Clflags.recursive_types alors
              iter_type_expr (occur_rec env (ty'::visited) ty0) ty'
      avec Cannot_expand ->
        si not !Clflags.recursive_types alors raise Occur
      fin
  | Tobject _ | Tvariant _ ->
      ()
  | _ ->
      si not !Clflags.recursive_types alors
        iter_type_expr (occur_rec env visited ty0) ty

soit type_changed = ref faux (* trace possible changes to the studied type *)

soit merge r b = si b alors r := vrai

soit occur env ty0 ty =
  soit old = !type_changed dans
  essaie
    pendant_que type_changed := faux; occur_rec env [] ty0 ty; !type_changed
    faire () (* prerr_endline "changed" *) fait;
    merge type_changed old
  avec exn ->
    merge type_changed old;
    raise (filtre exn avec Occur -> Unify [] | _ -> exn)

soit occur_in env ty0 t =
  essaie occur env ty0 t; faux avec Unify _ -> vrai

(* checks that a local constraint is non recursive *)
soit rec local_non_recursive_abbrev visited env p ty =
  soit ty = repr ty dans
  si not (List.memq ty !visited) alors début
    visited := ty :: !visited;
    filtre ty.desc avec
      Tconstr(p', args, abbrev) ->
        si Path.same p p' alors raise Recursive_abbrev;
        début essaie
          local_non_recursive_abbrev visited env p (try_expand_once_opt env ty)
        avec Cannot_expand ->
          si !Clflags.recursive_types alors () sinon
          iter_type_expr (local_non_recursive_abbrev visited env p) ty
        fin
    | Tobject _ | Tvariant _ ->
        ()
    | _ ->
        si !Clflags.recursive_types alors () sinon
        iter_type_expr (local_non_recursive_abbrev visited env p) ty
  fin

soit local_non_recursive_abbrev env p =
  local_non_recursive_abbrev (ref []) env p

                   (*****************************)
                   (*  Polymorphic Unification  *)
                   (*****************************)

(* Since we cannot duplicate universal variables, unification must
   be done at meta-level, using bindings in univar_pairs *)
soit rec unify_univar t1 t2 = fonction
    (cl1, cl2) :: rem ->
      soit find_univ t cl =
        essaie
          soit (_, r) = List.find (fonc (t',_) -> t == repr t') cl dans
          Some r
        avec Not_found -> None
      dans
      début filtre find_univ t1 cl1, find_univ t2 cl2 avec
        Some {contents=Some t'2}, Some _ quand t2 == repr t'2 ->
          ()
      | Some({contents=None} tel r1), Some({contents=None} tel r2) ->
          set_univar r1 t2; set_univar r2 t1
      | None, None ->
          unify_univar t1 t2 rem
      | _ ->
          raise (Unify [])
      fin
  | [] -> raise (Unify [])

(* Test the occurence of free univars in a type *)
(* that's way too expansive. Must do some kind of cacheing *)
soit occur_univar env ty =
  soit visited = ref TypeMap.empty dans
  soit rec occur_rec bound ty =
    soit ty = repr ty dans
    si ty.level >= lowest_level &&
      si TypeSet.is_empty bound alors
        (ty.level <- pivot_level - ty.level; vrai)
      sinon essaie
        soit bound' = TypeMap.find ty !visited dans
        si TypeSet.exists (fonc x -> not (TypeSet.mem x bound)) bound' alors
          (visited := TypeMap.add ty (TypeSet.inter bound bound') !visited;
           vrai)
        sinon faux
      avec Not_found ->
        visited := TypeMap.add ty bound !visited;
        vrai
    alors
      filtre ty.desc avec
        Tunivar _ ->
          si not (TypeSet.mem ty bound) alors raise (Unify [ty, newgenvar ()])
      | Tpoly (ty, tyl) ->
          soit bound = List.fold_right TypeSet.add (List.map repr tyl) bound dans
          occur_rec bound  ty
      | Tconstr (_, [], _) -> ()
      | Tconstr (p, tl, _) ->
          début essaie
            soit td = Env.find_type p env dans
            List.iter2
              (fonc t v ->
                si Variance.(mem May_pos v || mem May_neg v)
                alors occur_rec bound t)
              tl td.type_variance
          avec Not_found ->
            List.iter (occur_rec bound) tl
          fin
      | _ -> iter_type_expr (occur_rec bound) ty
  dans
  essaie
    occur_rec TypeSet.empty ty; unmark_type ty
  avec exn ->
    unmark_type ty; raise exn

(* Grouping univars by families according to their binders *)
soit add_univars =
  List.fold_left (fonc s (t,_) -> TypeSet.add (repr t) s)

soit get_univar_family univar_pairs univars =
  si univars = [] alors TypeSet.empty sinon
  soit insert s = fonction
      cl1, (_::_ tel cl2) ->
        si List.exists (fonc (t1,_) -> TypeSet.mem (repr t1) s) cl1 alors
          add_univars s cl2
        sinon s
    | _ -> s
  dans
  soit s = List.fold_right TypeSet.add univars TypeSet.empty dans
  List.fold_left insert s univar_pairs

(* Whether a family of univars escapes from a type *)
soit univars_escape env univar_pairs vl ty =
  soit family = get_univar_family univar_pairs vl dans
  soit visited = ref TypeSet.empty dans
  soit rec occur t =
    soit t = repr t dans
    si TypeSet.mem t !visited alors () sinon début
      visited := TypeSet.add t !visited;
      filtre t.desc avec
        Tpoly (t, tl) ->
          si List.exists (fonc t -> TypeSet.mem (repr t) family) tl alors ()
          sinon occur t
      | Tunivar _ ->
          si TypeSet.mem t family alors raise Occur
      | Tconstr (_, [], _) -> ()
      | Tconstr (p, tl, _) ->
          début essaie
            soit td = Env.find_type p env dans
            List.iter2
              (fonc t v ->
                si Variance.(mem May_pos v || mem May_neg v) alors occur t)
              tl td.type_variance
          avec Not_found ->
            List.iter occur tl
          fin
      | _ ->
          iter_type_expr occur t
    fin
  dans
  essaie occur ty; faux avec Occur -> vrai

(* Wrapper checking that no variable escapes and updating univar_pairs *)
soit enter_poly env univar_pairs t1 tl1 t2 tl2 f =
  soit old_univars = !univar_pairs dans
  soit known_univars =
    List.fold_left (fonc s (cl,_) -> add_univars s cl)
      TypeSet.empty old_univars
  dans
  soit tl1 = List.map repr tl1 et tl2 = List.map repr tl2 dans
  si List.exists (fonc t -> TypeSet.mem t known_univars) tl1 &&
    univars_escape env old_univars tl1 (newty(Tpoly(t2,tl2)))
  || List.exists (fonc t -> TypeSet.mem t known_univars) tl2 &&
    univars_escape env old_univars tl2 (newty(Tpoly(t1,tl1)))
  alors raise (Unify []);
  soit cl1 = List.map (fonc t -> t, ref None) tl1
  et cl2 = List.map (fonc t -> t, ref None) tl2 dans
  univar_pairs := (cl1,cl2) :: (cl2,cl1) :: old_univars;
  essaie soit res = f t1 t2 dans univar_pairs := old_univars; res
  avec exn -> univar_pairs := old_univars; raise exn

soit univar_pairs = ref []


                              (*****************)
                              (*  Unification  *)
                              (*****************)



soit rec has_cached_expansion p abbrev =
  filtre abbrev avec
    Mnil                   -> faux
  | Mcons(_, p', _, _, rem)   -> Path.same p p' || has_cached_expansion p rem
  | Mlink rem              -> has_cached_expansion p !rem

(**** Transform error trace ****)
(* +++ Move it to some other place ? *)

soit expand_trace env trace =
  List.fold_right
    (fonc (t1, t2) rem ->
       (repr t1, full_expand env t1)::(repr t2, full_expand env t2)::rem)
    trace []

(* build a dummy variant type *)
soit mkvariant fields closed =
  newgenty
    (Tvariant
       {row_fields = fields; row_closed = closed; row_more = newvar();
        row_bound = (); row_fixed = faux; row_name = None })

(* force unification in Reither when one side has as non-conjunctive type *)
soit rigid_variants = ref faux

(**** Unification ****)

(* Return whether [t0] occurs in [ty]. Objects are also traversed. *)
soit deep_occur t0 ty =
  soit rec occur_rec ty =
    soit ty = repr ty dans
    si ty.level >= lowest_level alors début
      si ty == t0 alors raise Occur;
      ty.level <- pivot_level - ty.level;
      iter_type_expr occur_rec ty
    fin
  dans
  essaie
    occur_rec ty; unmark_type ty; faux
  avec Occur ->
    unmark_type ty; vrai

(*
   1. When unifying two non-abbreviated types, one type is made a link
      to the other. When unifying an abbreviated type with a
      non-abbreviated type, the non-abbreviated type is made a link to
      the other one. When unifying to abbreviated types, these two
      types are kept distincts, but they are made to (temporally)
      expand to the same type.
   2. Abbreviations with at least one parameter are systematically
      expanded. The overhead does not seem to high, and that way
      abbreviations where some parameters does not appear in the
      expansion, such as ['a t = int], are correctly handled. In
      particular, for this example, unifying ['a t] with ['b t] keeps
      ['a] and ['b] distincts. (Is it really important ?)
   3. Unifying an abbreviation ['a t = 'a] with ['a] should not yield
      ['a t as 'a]. Indeed, the type variable would otherwise be lost.
      This problem occurs for abbreviations expanding to a type
      variable, but also to many other constrained abbreviations (for
      instance, [(< x : 'a > -> unit) t = <x : 'a>]). The solution is
      that, if an abbreviation is unified with some subpart of its
      parameters, then the parameter actually does not get
      abbreviated.  It would be possible to check whether some
      information is indeed lost, but it probably does not worth it.
*)

soit newtype_level = ref None

soit get_newtype_level () =
  filtre !newtype_level avec
  | None -> affirme faux
  | Some x -> x

(* a local constraint can be added only if the rhs
   of the constraint does not contain any Tvars.
   They need to be removed using this function *)
soit reify env t =
  soit newtype_level = get_newtype_level () dans
  soit create_fresh_constr lev name =
    soit decl = new_declaration (Some (newtype_level, newtype_level)) None dans
    soit name = get_new_abstract_name name dans
    soit (id, new_env) = Env.enter_type name decl !env dans
    soit t = newty2 lev (Tconstr (Path.Pident id,[],ref Mnil))  dans
    env := new_env;
    t
  dans
  soit visited = ref TypeSet.empty dans
  soit rec iterator ty =
    soit ty = repr ty dans
    si TypeSet.mem ty !visited alors () sinon début
      visited := TypeSet.add ty !visited;
      filtre ty.desc avec
        Tvar o ->
          soit name = filtre o avec Some s -> s | _ -> "ex" dans
          soit t = create_fresh_constr ty.level name dans
          link_type ty t
      | Tvariant r ->
          soit r = row_repr r dans
          si not (static_row r) alors début
            si r.row_fixed alors iterator (row_more r) sinon
            soit m = r.row_more dans
            filtre m.desc avec
              Tvar o ->
                soit name = filtre o avec Some s -> s | _ -> "ex" dans
                soit t = create_fresh_constr m.level name dans
                soit row =
                  {r avec row_fields=[]; row_fixed=vrai; row_more = t} dans
                link_type m (newty2 m.level (Tvariant row))
            | _ -> affirme faux
          fin;
          iter_row iterator r
      | Tconstr (p, _, _) quand is_object_type p ->
          iter_type_expr iterator (full_expand !env ty)
      | _ ->
          iter_type_expr iterator ty
    fin
  dans
  iterator t

soit is_newtype env p =
  essaie
    soit decl = Env.find_type p env dans
    decl.type_newtype_level <> None &&
    decl.type_kind = Type_abstract &&
    decl.type_private = Public
  avec Not_found -> faux

soit non_aliasable p decl =
  (* in_pervasives p ||  (subsumed by in_current_module) *)
  in_current_module p && decl.type_newtype_level = None

(* mcomp type_pairs subst env t1 t2 does not raise an
   exception if it is possible that t1 and t2 are actually
   equal, assuming the types in type_pairs are equal and
   that the mapping subst holds.
   Assumes that both t1 and t2 do not contain any tvars
   and that both their objects and variants are closed
 *)

soit rec mcomp type_pairs env t1 t2 =
  si t1 == t2 alors () sinon
  soit t1 = repr t1 dans
  soit t2 = repr t2 dans
  si t1 == t2 alors () sinon
  filtre (t1.desc, t2.desc) avec
  | (Tvar _, _)
  | (_, Tvar _)  ->
      ()
  | (Tconstr (p1, [], _), Tconstr (p2, [], _)) quand Path.same p1 p2 ->
      ()
  | _ ->
      soit t1' = expand_head_opt env t1 dans
      soit t2' = expand_head_opt env t2 dans
      (* Expansion may have changed the representative of the types... *)
      soit t1' = repr t1' et t2' = repr t2' dans
      si t1' == t2' alors () sinon
      début essaie TypePairs.find type_pairs (t1', t2')
      avec Not_found ->
        TypePairs.add type_pairs (t1', t2') ();
        filtre (t1'.desc, t2'.desc) avec
          (Tvar _, Tvar _) -> affirme faux
        | (Tarrow (l1, t1, u1, _), Tarrow (l2, t2, u2, _))
          quand l1 = l2 || not (is_optional l1 || is_optional l2) ->
            mcomp type_pairs env t1 t2;
            mcomp type_pairs env u1 u2;
        | (Ttuple tl1, Ttuple tl2) ->
            mcomp_list type_pairs env tl1 tl2
        | (Tconstr (p1, tl1, _), Tconstr (p2, tl2, _)) ->
            mcomp_type_decl type_pairs env p1 p2 tl1 tl2
        | (Tconstr (p, _, _), _) | (_, Tconstr (p, _, _)) ->
            soit decl = Env.find_type p env dans
            si non_aliasable p decl alors raise (Unify [])
        (*
        | (Tpackage (p1, n1, tl1), Tpackage (p2, n2, tl2)) when n1 = n2 ->
            mcomp_list type_pairs env tl1 tl2
        *)
        | (Tpackage _, Tpackage _) -> ()
        | (Tvariant row1, Tvariant row2) ->
            mcomp_row type_pairs env row1 row2
        | (Tobject (fi1, _), Tobject (fi2, _)) ->
            mcomp_fields type_pairs env fi1 fi2
        | (Tfield _, Tfield _) ->       (* Actually unused *)
            mcomp_fields type_pairs env t1' t2'
        | (Tnil, Tnil) ->
            ()
        | (Tpoly (t1, []), Tpoly (t2, [])) ->
            mcomp type_pairs env t1 t2
        | (Tpoly (t1, tl1), Tpoly (t2, tl2)) ->
            enter_poly env univar_pairs t1 tl1 t2 tl2
              (mcomp type_pairs env)
        | (Tunivar _, Tunivar _) ->
            unify_univar t1' t2' !univar_pairs
        | (_, _) ->
            raise (Unify [])
      fin

et mcomp_list type_pairs env tl1 tl2 =
  si List.length tl1 <> List.length tl2 alors
    raise (Unify []);
  List.iter2 (mcomp type_pairs env) tl1 tl2

et mcomp_fields type_pairs env ty1 ty2 =
  si not (concrete_object ty1 && concrete_object ty2) alors affirme faux;
  soit (fields2, rest2) = flatten_fields ty2 dans
  soit (fields1, rest1) = flatten_fields ty1 dans
  soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
  mcomp type_pairs env rest1 rest2;
  si miss1 <> []  && (object_row ty1).desc = Tnil
  || miss2 <> []  && (object_row ty2).desc = Tnil alors raise (Unify []);
  List.iter
    (fonction (n, k1, t1, k2, t2) ->
       mcomp_kind k1 k2;
       mcomp type_pairs env t1 t2)
    pairs

et mcomp_kind k1 k2 =
  soit k1 = field_kind_repr k1 dans
  soit k2 = field_kind_repr k2 dans
  filtre k1, k2 avec
    (Fvar _, Fvar _)
  | (Fpresent, Fpresent) -> ()
  | _                    -> raise (Unify [])

et mcomp_row type_pairs env row1 row2 =
  soit row1 = row_repr row1 et row2 = row_repr row2 dans
  soit r1, r2, pairs = merge_row_fields row1.row_fields row2.row_fields dans
  soit cannot_erase (_,f) =
    filtre row_field_repr f avec
      Rpresent _ -> vrai
    | Rabsent | Reither _ -> faux
  dans
  si row1.row_closed && List.exists cannot_erase r2
  || row2.row_closed && List.exists cannot_erase r1 alors raise (Unify []);
  List.iter
    (fonc (_,f1,f2) ->
      filtre row_field_repr f1, row_field_repr f2 avec
      | Rpresent None, (Rpresent (Some _) | Reither (_, _::_, _, _) | Rabsent)
      | Rpresent (Some _), (Rpresent None | Reither (vrai, _, _, _) | Rabsent)
      | (Reither (_, _::_, _, _) | Rabsent), Rpresent None
      | (Reither (vrai, _, _, _) | Rabsent), Rpresent (Some _) ->
          raise (Unify [])
      | Rpresent(Some t1), Rpresent(Some t2) ->
          mcomp type_pairs env t1 t2
      | Rpresent(Some t1), Reither(faux, tl2, _, _) ->
          List.iter (mcomp type_pairs env t1) tl2
      | Reither(faux, tl1, _, _), Rpresent(Some t2) ->
          List.iter (mcomp type_pairs env t2) tl1
      | _ -> ())
    pairs

et mcomp_type_decl type_pairs env p1 p2 tl1 tl2 =
  essaie
    soit decl = Env.find_type p1 env dans
    soit decl' = Env.find_type p2 env dans
    si Path.same p1 p2 alors début
      (* Format.eprintf "@[%a@ %a@]@."
        !print_raw (newconstr p1 tl2) !print_raw (newconstr p2 tl2);
      if non_aliasable p1 decl then Format.eprintf "non_aliasable@."
      else Format.eprintf "aliasable@."; *)
      soit inj =
        essaie List.map Variance.(mem Inj) (Env.find_type p1 env).type_variance
        avec Not_found -> List.map (fonc _ -> faux) tl1
      dans
      List.iter2
        (fonc i (t1,t2) -> si i alors mcomp type_pairs env t1 t2)
        inj (List.combine tl1 tl2)
    fin
    sinon filtre decl.type_kind, decl'.type_kind avec
    | Type_record (lst,r), Type_record (lst',r') quand r = r' ->
        mcomp_list type_pairs env tl1 tl2;
        mcomp_record_description type_pairs env lst lst'
    | Type_variant v1, Type_variant v2 ->
        mcomp_list type_pairs env tl1 tl2;
        mcomp_variant_description type_pairs env v1 v2
    | Type_variant _, Type_record _
    | Type_record _, Type_variant _ -> raise (Unify [])
    | _ ->
        si non_aliasable p1 decl && (non_aliasable p2 decl'||is_datatype decl')
        || is_datatype decl && non_aliasable p2 decl' alors raise (Unify [])
  avec Not_found -> ()

et mcomp_type_option type_pairs env t t' =
  filtre t, t' avec
    None, None -> ()
  | Some t, Some t' -> mcomp type_pairs env t t'
  | _ -> raise (Unify [])

et mcomp_variant_description type_pairs env xs ys =
  soit rec iter = fonc x y ->
    filtre x, y avec
    | c1 :: xs, c2 :: ys   ->
      mcomp_type_option type_pairs env c1.cd_res c2.cd_res;
      mcomp_list type_pairs env c1.cd_args c2.cd_args;
     si Ident.name c1.cd_id = Ident.name c2.cd_id
      alors iter xs ys
      sinon raise (Unify [])
    | [],[] -> ()
    | _ -> raise (Unify [])
  dans
  iter xs ys

et mcomp_record_description type_pairs env =
  soit rec iter x y =
    filtre x, y avec
    | l1 :: xs, l2 :: ys ->
        mcomp type_pairs env l1.ld_type l2.ld_type;
        si Ident.name l1.ld_id = Ident.name l2.ld_id &&
           l1.ld_mutable = l2.ld_mutable
        alors iter xs ys
        sinon raise (Unify [])
    | [], [] -> ()
    | _ -> raise (Unify [])
  dans
  iter

soit mcomp env t1 t2 =
  mcomp (TypePairs.create 4) env t1 t2

(* Real unification *)

soit find_lowest_level ty =
  soit lowest = ref generic_level dans
  soit rec find ty =
    soit ty = repr ty dans
    si ty.level >= lowest_level alors début
      si ty.level < !lowest alors lowest := ty.level;
      ty.level <- pivot_level - ty.level;
      iter_type_expr find ty
    fin
  dans find ty; unmark_type ty; !lowest

soit find_newtype_level env path =
  essaie filtre (Env.find_type path env).type_newtype_level avec
    Some x -> x
  | None -> affirme faux
  avec Not_found -> affirme faux

soit add_gadt_equation env source destination =
  soit destination = duplicate_type destination dans
  soit source_lev = find_newtype_level !env (Path.Pident source) dans
  soit decl = new_declaration (Some source_lev) (Some destination) dans
  soit newtype_level = get_newtype_level () dans
  env := Env.add_local_constraint source decl newtype_level !env;
  cleanup_abbrev ()

soit unify_eq_set = TypePairs.create 11

soit order_type_pair t1 t2 =
  si t1.id <= t2.id alors (t1, t2) sinon (t2, t1)

soit add_type_equality t1 t2 =
  TypePairs.add unify_eq_set (order_type_pair t1 t2) ()

soit eq_package_path env p1 p2 =
  Path.same p1 p2 ||
  Path.same (normalize_package_path env p1) (normalize_package_path env p2)

soit nondep_type' = ref (fonc _ _ _ -> affirme faux)
soit package_subtype = ref (fonc _ _ _ _ _ _ _ -> affirme faux)

soit rec concat_longident lid1 =
  soit ouvre Longident dans
  fonction
    Lident s -> Ldot (lid1, s)
  | Ldot (lid2, s) -> Ldot (concat_longident lid1 lid2, s)
  | Lapply (lid2, lid) -> Lapply (concat_longident lid1 lid2, lid)

soit nondep_instance env level id ty =
  soit ty = !nondep_type' env id ty dans
  si level = generic_level alors duplicate_type ty sinon
  soit old = !current_level dans
  current_level := level;
  soit ty = instance env ty dans
  current_level := old;
  ty

(* Find the type paths nl1 in the module type mty2, and add them to the
   list (nl2, tl2). raise Not_found if impossible *)
soit complete_type_list ?(allow_absent=faux) env nl1 lv2 mty2 nl2 tl2 =
  soit id2 = Ident.create "Pkg" dans
  soit env' = Env.add_module id2 mty2 env dans
  soit rec complete nl1 ntl2 =
    filtre nl1, ntl2 avec
      [], _ -> ntl2
    | n :: nl, (n2, _ tel nt2) :: ntl' quand n >= n2 ->
        nt2 :: complete (si n = n2 alors nl sinon nl1) ntl'
    | n :: nl, _ ->
        essaie
          soit (_, decl) =
            Env.lookup_type (concat_longident (Longident.Lident "Pkg") n) env'
          dans
          filtre decl avec
            {type_arity = 0; type_kind = Type_abstract;
             type_private = Public; type_manifest = Some t2} ->
               (n, nondep_instance env' lv2 id2 t2) :: complete nl ntl2
          | {type_arity = 0; type_kind = Type_abstract;
             type_private = Public; type_manifest = None} quand allow_absent ->
               complete nl ntl2
          | _ -> raise Exit
        avec
        | Not_found quand allow_absent -> complete nl ntl2
        | Exit -> raise Not_found
  dans
  complete nl1 (List.combine nl2 tl2)

(* raise Not_found rather than Unify if the module types are incompatible *)
soit unify_package env unify_list lv1 p1 n1 tl1 lv2 p2 n2 tl2 =
  soit ntl2 = complete_type_list env n1 lv2 (Mty_ident p2) n2 tl2
  et ntl1 = complete_type_list env n2 lv2 (Mty_ident p1) n1 tl1 dans
  unify_list (List.map snd ntl1) (List.map snd ntl2);
  si eq_package_path env p1 p2 
  || !package_subtype env p1 n1 tl1 p2 n2 tl2
  && !package_subtype env p2 n2 tl2 p1 n1 tl1 alors () sinon raise Not_found


soit unify_eq env t1 t2 =
  t1 == t2 ||
  filtre !umode avec
  | Expression -> faux
  | Pattern ->
      essaie TypePairs.find unify_eq_set (order_type_pair t1 t2); vrai
      avec Not_found -> faux

soit rec unify (env:Env.t ref) t1 t2 =
  (* First step: special cases (optimizations) *)
  si t1 == t2 alors () sinon
  soit t1 = repr t1 dans
  soit t2 = repr t2 dans
  si unify_eq !env t1 t2 alors () sinon
  soit reset_tracing = check_trace_gadt_instances !env dans

  essaie
    type_changed := vrai;
    début filtre (t1.desc, t2.desc) avec
      (Tvar _, Tconstr _) quand deep_occur t1 t2 ->
        unify2 env t1 t2
    | (Tconstr _, Tvar _) quand deep_occur t2 t1 ->
        unify2 env t1 t2
    | (Tvar _, _) ->
        occur !env t1 t2;
        occur_univar !env t2;
        link_type t1 t2;
        update_level !env t1.level t2
    | (_, Tvar _) ->
        occur !env t2 t1;
        occur_univar !env t1;
        link_type t2 t1;
        update_level !env t2.level t1
    | (Tunivar _, Tunivar _) ->
        unify_univar t1 t2 !univar_pairs;
        update_level !env t1.level t2;
        link_type t1 t2
    | (Tconstr (p1, [], a1), Tconstr (p2, [], a2))
          quand Path.same p1 p2 (* && actual_mode !env = Old *)
            (* This optimization assumes that t1 does not expand to t2
               (and conversely), so we fall back to the general case
               when any of the types has a cached expansion. *)
            && not (has_cached_expansion p1 !a1
                 || has_cached_expansion p2 !a2) ->
        update_level !env t1.level t2;
        link_type t1 t2
    | (Tconstr (p1, [], _), Tconstr (p2, [], _))
      quand Env.has_local_constraints !env
      && is_newtype !env p1 && is_newtype !env p2 ->
        (* Do not use local constraints more than necessary *)
        début essaie
          si find_newtype_level !env p1 < find_newtype_level !env p2 alors
            unify env t1 (try_expand_once !env t2)
          sinon
            unify env (try_expand_once !env t1) t2
        avec Cannot_expand ->
          unify2 env t1 t2
        fin
    | _ ->
        unify2 env t1 t2
    fin;
    reset_trace_gadt_instances reset_tracing;
  avec Unify trace ->
    reset_trace_gadt_instances reset_tracing;
    raise (Unify ((t1, t2)::trace))

et unify2 env t1 t2 =
  (* Second step: expansion of abbreviations *)
  soit rec expand_both t1'' t2'' =
    soit t1' = expand_head_unif !env t1 dans
    soit t2' = expand_head_unif !env t2 dans
    (* Expansion may have changed the representative of the types... *)
    si unify_eq !env t1' t1'' && unify_eq !env t2' t2'' alors (t1',t2') sinon
    expand_both t1' t2'
  dans
  soit t1', t2' = expand_both t1 t2 dans
  soit lv = min t1'.level t2'.level dans
  update_level !env lv t2;
  update_level !env lv t1;
  si unify_eq !env t1' t2' alors () sinon

  soit t1 = repr t1 et t2 = repr t2 dans
  si !trace_gadt_instances alors début
    (* All types in chains already have the same ambiguity levels *)
    soit ilevel t =
      filtre Env.gadt_instance_level !env t avec None -> 0 | Some lv -> lv dans
    soit lv1 = ilevel t1 et lv2 = ilevel t2 dans
    si lv1 > lv2 alors Env.add_gadt_instance_chain !env lv1 t2 sinon
    si lv2 > lv1 alors Env.add_gadt_instance_chain !env lv2 t1
  fin;
  soit t1, t2 =
    si !Clflags.principal
    && (find_lowest_level t1' < lv || find_lowest_level t2' < lv) alors
      (* Expand abbreviations hiding a lower level *)
      (* Should also do it for parameterized types, after unification... *)
      (filtre t1.desc avec Tconstr (_, [], _) -> t1' | _ -> t1),
      (filtre t2.desc avec Tconstr (_, [], _) -> t2' | _ -> t2)
    sinon (t1, t2)
  dans
  si unify_eq !env t1 t1' || not (unify_eq !env t2 t2') alors
    unify3 env t1 t1' t2 t2'
  sinon
    essaie unify3 env t2 t2' t1 t1' avec Unify trace ->
      raise (Unify (List.map (fonc (x, y) -> (y, x)) trace))

et unify3 env t1 t1' t2 t2' =
  (* Third step: truly unification *)
  (* Assumes either [t1 == t1'] or [t2 != t2'] *)
  soit d1 = t1'.desc et d2 = t2'.desc dans
  soit create_recursion = (t2 != t2') && (deep_occur t1' t2) dans

  début filtre (d1, d2) avec (* handle vars and univars specially *)
    (Tunivar _, Tunivar _) ->
      unify_univar t1' t2' !univar_pairs;
      link_type t1' t2'
  | (Tvar _, _) ->
      occur !env t1' t2;
      occur_univar !env t2;
      link_type t1' t2;
  | (_, Tvar _) ->
      occur !env t2' t1;
      occur_univar !env t1;
      link_type t2' t1;
  | (Tfield _, Tfield _) -> (* special case for GADTs *)
      unify_fields env t1' t2'
  | _ ->
    début filtre !umode avec
    | Expression ->
        occur !env t1' t2';
        link_type t1' t2
    | Pattern ->
        add_type_equality t1' t2'
    fin;
    essaie
      début filtre (d1, d2) avec
        (Tarrow (l1, t1, u1, c1), Tarrow (l2, t2, u2, c2)) quand l1 = l2 ||
        !Clflags.classic && not (is_optional l1 || is_optional l2) ->
          unify  env t1 t2; unify env  u1 u2;
          début filtre commu_repr c1, commu_repr c2 avec
            Clink r, c2 -> set_commu r c2
          | c1, Clink r -> set_commu r c1
          | _ -> ()
          fin
      | (Ttuple tl1, Ttuple tl2) ->
          unify_list env tl1 tl2
      | (Tconstr (p1, tl1, _), Tconstr (p2, tl2, _)) quand Path.same p1 p2 ->
          si !umode = Expression || not !generate_equations
          || in_current_module p1 (* || in_pervasives p1 *)
          || essaie is_datatype (Env.find_type p1 !env) avec Not_found -> faux
          alors
            unify_list env tl1 tl2
          sinon
            soit inj =
              essaie List.map Variance.(mem Inj)
                    (Env.find_type p1 !env).type_variance
              avec Not_found -> List.map (fonc _ -> faux) tl1
            dans
            List.iter2
              (fonc i (t1, t2) ->
                si i alors unify env t1 t2 sinon
                set_mode Pattern ~generate:faux
                  début fonc () ->
                    soit snap = snapshot () dans
                    essaie unify env t1 t2 avec Unify _ ->
                      backtrack snap;
                      reify env t1; reify env t2
                  fin)
              inj (List.combine tl1 tl2)
      | (Tconstr ((Path.Pident p) tel path,[],_),
         Tconstr ((Path.Pident p') tel path',[],_))
        quand is_newtype !env path && is_newtype !env path'
        && !generate_equations ->
          soit source,destination =
            si find_newtype_level !env path > find_newtype_level !env path'
            alors  p,t2'
            sinon  p',t1'
          dans add_gadt_equation env source destination
      | (Tconstr ((Path.Pident p) tel path,[],_), _)
        quand is_newtype !env path && !generate_equations ->
          reify env t2';
          local_non_recursive_abbrev !env (Path.Pident p) t2';
          add_gadt_equation env p t2'
      | (_, Tconstr ((Path.Pident p) tel path,[],_))
        quand is_newtype !env path && !generate_equations ->
          reify env t1' ;
          local_non_recursive_abbrev !env (Path.Pident p) t1';
          add_gadt_equation env p t1'
      | (Tconstr (_,_,_), _) | (_, Tconstr (_,_,_)) quand !umode = Pattern ->
          reify env t1';
          reify env t2';
          si !generate_equations alors mcomp !env t1' t2'
      | (Tobject (fi1, nm1), Tobject (fi2, _)) ->
          unify_fields env fi1 fi2;
          (* Type [t2'] may have been instantiated by [unify_fields] *)
          (* XXX One should do some kind of unification... *)
          début filtre (repr t2').desc avec
            Tobject (_, {contents = Some (_, va::_)}) quand
              (filtre (repr va).desc avec
                Tvar _|Tunivar _|Tnil -> vrai | _ -> faux) -> ()
          | Tobject (_, nm2) -> set_name nm2 !nm1
          | _ -> ()
          fin
      | (Tvariant row1, Tvariant row2) ->
          si !umode = Expression alors
            unify_row env row1 row2
          sinon début
            soit snap = snapshot () dans
            essaie unify_row env row1 row2
            avec Unify _ ->
              backtrack snap;
              reify env t1';
              reify env t2';
              si !generate_equations alors mcomp !env t1' t2'
          fin
      | (Tfield(f,kind,_,rem), Tnil) | (Tnil, Tfield(f,kind,_,rem)) ->
          début filtre field_kind_repr kind avec
            Fvar r quand f <> dummy_method ->
              set_kind r Fabsent;
              si d2 = Tnil alors unify env rem t2'
              sinon unify env (newty2 rem.level Tnil) rem
          | _      -> raise (Unify [])
          fin
      | (Tnil, Tnil) ->
          ()
      | (Tpoly (t1, []), Tpoly (t2, [])) ->
          unify env t1 t2
      | (Tpoly (t1, tl1), Tpoly (t2, tl2)) ->
          enter_poly !env univar_pairs t1 tl1 t2 tl2 (unify env)
      | (Tpackage (p1, n1, tl1), Tpackage (p2, n2, tl2)) ->
          début essaie
            unify_package !env (unify_list env)
              t1.level p1 n1 tl1 t2.level p2 n2 tl2
          avec Not_found ->
            si !umode = Expression alors raise (Unify []);
            List.iter (reify env) (tl1 @ tl2);
            (* if !generate_equations then List.iter2 (mcomp !env) tl1 tl2 *)
          fin
      | (_, _) ->
          raise (Unify [])
      fin;
      (* XXX Commentaires + changer "create_recursion" *)
      si create_recursion alors
        filtre t2.desc avec
          Tconstr (p, tl, abbrev) ->
            forget_abbrev abbrev p;
            soit t2'' = expand_head_unif !env t2 dans
            si not (closed_parameterized_type tl t2'') alors
              link_type (repr t2) (repr t2')
        | _ ->
            () (* t2 has already been expanded by update_level *)
    avec Unify trace ->
      t1'.desc <- d1;
      raise (Unify trace)
  fin

et unify_list env tl1 tl2 =
  si List.length tl1 <> List.length tl2 alors
    raise (Unify []);
  List.iter2 (unify env) tl1 tl2

(* Build a fresh row variable for unification *)
et make_rowvar level use1 rest1 use2 rest2  =
  soit set_name ty name =
    filtre ty.desc avec
      Tvar None -> log_type ty; ty.desc <- Tvar name
    | _ -> ()
  dans
  soit name =
    filtre rest1.desc, rest2.desc avec
      Tvar (Some _ tel name1), Tvar (Some _ tel name2) ->
        si rest1.level <= rest2.level alors name1 sinon name2
    | Tvar (Some _ tel name), _ ->
        si use2 alors set_name rest2 name; name
    | _, Tvar (Some _ tel name) ->
        si use1 alors set_name rest2 name; name
    | _ -> None
  dans
  si use1 alors rest1 sinon
  si use2 alors rest2 sinon newvar2 ?name level

et unify_fields env ty1 ty2 =          (* Optimization *)
  soit (fields1, rest1) = flatten_fields ty1
  et (fields2, rest2) = flatten_fields ty2 dans
  soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
  soit l1 = (repr ty1).level et l2 = (repr ty2).level dans
  soit va = make_rowvar (min l1 l2) (miss2=[]) rest1 (miss1=[]) rest2 dans
  soit d1 = rest1.desc et d2 = rest2.desc dans
  essaie
    unify env (build_fields l1 miss1 va) rest2;
    unify env rest1 (build_fields l2 miss2 va);
    List.iter
      (fonc (n, k1, t1, k2, t2) ->
        unify_kind k1 k2;
        essaie
          si !trace_gadt_instances alors update_level !env va.level t1;
          unify env t1 t2
        avec Unify trace ->
          raise (Unify ((newty (Tfield(n, k1, t1, newty Tnil)),
                         newty (Tfield(n, k2, t2, newty Tnil)))::trace)))
      pairs
  avec exn ->
    log_type rest1; rest1.desc <- d1;
    log_type rest2; rest2.desc <- d2;
    raise exn

et unify_kind k1 k2 =
  soit k1 = field_kind_repr k1 dans
  soit k2 = field_kind_repr k2 dans
  si k1 == k2 alors () sinon
  filtre k1, k2 avec
    (Fvar r, (Fvar _ | Fpresent)) -> set_kind r k2
  | (Fpresent, Fvar r)            -> set_kind r k1
  | (Fpresent, Fpresent)          -> ()
  | _                             -> affirme faux

et unify_pairs mode env tpl =
  List.iter (fonc (t1, t2) -> unify env t1 t2) tpl

et unify_row env row1 row2 =
  soit row1 = row_repr row1 et row2 = row_repr row2 dans
  soit rm1 = row_more row1 et rm2 = row_more row2 dans
  si unify_eq !env rm1 rm2 alors () sinon
  soit r1, r2, pairs = merge_row_fields row1.row_fields row2.row_fields dans
  si r1 <> [] && r2 <> [] alors début
    soit ht = Hashtbl.create (List.length r1) dans
    List.iter (fonc (l,_) -> Hashtbl.add ht (hash_variant l) l) r1;
    List.iter
      (fonc (l,_) ->
        essaie raise (Tags(l, Hashtbl.find ht (hash_variant l)))
        avec Not_found -> ())
      r2
  fin;
  soit fixed1 = row_fixed row1 et fixed2 = row_fixed row2 dans
  soit more =
    si fixed1 alors rm1 sinon
    si fixed2 alors rm2 sinon
    newty2 (min rm1.level rm2.level) (Tvar None) dans
  soit fixed = fixed1 || fixed2
  et closed = row1.row_closed || row2.row_closed dans
  soit keep switch =
    List.for_all
      (fonc (_,f1,f2) ->
        soit f1, f2 = switch f1 f2 dans
        row_field_repr f1 = Rabsent || row_field_repr f2 <> Rabsent)
      pairs
  dans
  soit empty fields =
    List.for_all (fonc (_,f) -> row_field_repr f = Rabsent) fields dans
  (* Check whether we are going to build an empty type *)
  si closed && (empty r1 || row2.row_closed) && (empty r2 || row1.row_closed)
  && List.for_all
      (fonc (_,f1,f2) ->
        row_field_repr f1 = Rabsent || row_field_repr f2 = Rabsent)
      pairs
  alors raise (Unify [mkvariant [] vrai, mkvariant [] vrai]);
  soit name =
    si row1.row_name <> None && (row1.row_closed || empty r2) &&
      (not row2.row_closed || keep (fonc f1 f2 -> f1, f2) && empty r1)
    alors row1.row_name
    sinon si row2.row_name <> None && (row2.row_closed || empty r1) &&
      (not row1.row_closed || keep (fonc f1 f2 -> f2, f1) && empty r2)
    alors row2.row_name
    sinon None
  dans
  soit row0 = {row_fields = []; row_more = more; row_bound = ();
              row_closed = closed; row_fixed = fixed; row_name = name} dans
  soit set_more row rest =
    soit rest =
      si closed alors
        filter_row_fields row.row_closed rest
      sinon rest dans
    si rest <> [] && (row.row_closed || row_fixed row)
    || closed && row_fixed row && not row.row_closed alors début
      soit t1 = mkvariant [] vrai et t2 = mkvariant rest faux dans
      raise (Unify [si row == row1 alors (t1,t2) sinon (t2,t1)])
    fin;
    (* The following test is not principal... should rather use Tnil *)
    soit rm = row_more row dans
    si !trace_gadt_instances && rm.desc = Tnil alors () sinon
    si !trace_gadt_instances alors
      update_level !env rm.level (newgenty (Tvariant row));
    si row_fixed row alors
      si more == rm alors () sinon
      si is_Tvar rm alors link_type rm more sinon unify env rm more
    sinon
      soit ty = newgenty (Tvariant {row0 avec row_fields = rest}) dans
      update_level !env rm.level ty;
      link_type rm ty
  dans
  soit md1 = rm1.desc et md2 = rm2.desc dans
  début essaie
    set_more row2 r1;
    set_more row1 r2;
    List.iter
      (fonc (l,f1,f2) ->
        essaie unify_row_field env fixed1 fixed2 more l f1 f2
        avec Unify trace ->
          raise (Unify ((mkvariant [l,f1] vrai,
                         mkvariant [l,f2] vrai) :: trace)))
      pairs;
  avec exn ->
    log_type rm1; rm1.desc <- md1; log_type rm2; rm2.desc <- md2; raise exn
  fin

et unify_row_field env fixed1 fixed2 more l f1 f2 =
  soit f1 = row_field_repr f1 et f2 = row_field_repr f2 dans
  si f1 == f2 alors () sinon
  filtre f1, f2 avec
    Rpresent(Some t1), Rpresent(Some t2) -> unify env t1 t2
  | Rpresent None, Rpresent None -> ()
  | Reither(c1, tl1, m1, e1), Reither(c2, tl2, m2, e2) ->
      si e1 == e2 alors () sinon
      soit redo =
        (m1 || m2 || fixed1 || fixed2 ||
         !rigid_variants && (List.length tl1 = 1 || List.length tl2 = 1)) &&
        début filtre tl1 @ tl2 avec [] -> faux
        | t1 :: tl ->
            si c1 || c2 alors raise (Unify []);
            List.iter (unify env t1) tl;
            !e1 <> None || !e2 <> None
        fin dans
      si redo alors unify_row_field env fixed1 fixed2 more l f1 f2 sinon
      soit tl1 = List.map repr tl1 et tl2 = List.map repr tl2 dans
      soit rec remq tl = fonction [] -> []
        | ty :: tl' ->
            si List.memq ty tl alors remq tl tl' sinon ty :: remq tl tl'
      dans
      soit tl2' = remq tl2 tl1 et tl1' = remq tl1 tl2 dans
      (* Is this handling of levels really principal? *)
      List.iter (update_level !env (repr more).level) (tl1' @ tl2');
      soit e = ref None dans
      soit f1' = Reither(c1 || c2, tl1', m1 || m2, e)
      et f2' = Reither(c1 || c2, tl2', m1 || m2, e) dans
      set_row_field e1 f1'; set_row_field e2 f2';
  | Reither(_, _, faux, e1), Rabsent quand not fixed1 -> set_row_field e1 f2
  | Rabsent, Reither(_, _, faux, e2) quand not fixed2 -> set_row_field e2 f1
  | Rabsent, Rabsent -> ()
  | Reither(faux, tl, _, e1), Rpresent(Some t2) quand not fixed1 ->
      set_row_field e1 f2;
      update_level !env (repr more).level t2;
      (essaie List.iter (fonc t1 -> unify env t1 t2) tl
      avec exn -> e1 := None; raise exn)
  | Rpresent(Some t1), Reither(faux, tl, _, e2) quand not fixed2 ->
      set_row_field e2 f1;
      update_level !env (repr more).level t1;
      (essaie List.iter (unify env t1) tl
      avec exn -> e2 := None; raise exn)
  | Reither(vrai, [], _, e1), Rpresent None quand not fixed1 ->
      set_row_field e1 f2
  | Rpresent None, Reither(vrai, [], _, e2) quand not fixed2 ->
      set_row_field e2 f1
  | _ -> raise (Unify [])


soit unify env ty1 ty2 =
  essaie
    unify env ty1 ty2
  avec
    Unify trace ->
      raise (Unify (expand_trace !env trace))
  | Recursive_abbrev ->
      raise (Unification_recursive_abbrev (expand_trace !env [(ty1,ty2)]))

soit unify_gadt ~newtype_level:lev (env:Env.t ref) ty1 ty2 =
  essaie
    univar_pairs := [];
    newtype_level := Some lev;
    set_mode Pattern (fonc () -> unify env ty1 ty2);
    newtype_level := None;
    TypePairs.clear unify_eq_set;
  avec e ->
    TypePairs.clear unify_eq_set;
    filtre e avec
      Unify e -> raise (Unify e)
    | e -> newtype_level := None; raise e

soit unify_var env t1 t2 =
  soit t1 = repr t1 et t2 = repr t2 dans
  si t1 == t2 alors () sinon
  filtre t1.desc avec
    Tvar _ ->
      soit reset_tracing = check_trace_gadt_instances env dans
      début essaie
        occur env t1 t2;
        update_level env t1.level t2;
        link_type t1 t2;
        reset_trace_gadt_instances reset_tracing;
      avec Unify trace ->
        reset_trace_gadt_instances reset_tracing;
        soit expanded_trace = expand_trace env ((t1,t2)::trace) dans
        raise (Unify expanded_trace)
      fin
  | _ ->
      unify (ref env) t1 t2

soit _ = unify' := unify_var

soit unify_pairs env ty1 ty2 pairs =
  univar_pairs := pairs;
  unify env ty1 ty2

soit unify env ty1 ty2 =
  unify_pairs (ref env) ty1 ty2 []



(**** Special cases of unification ****)

soit expand_head_trace env t =
  soit reset_tracing = check_trace_gadt_instances env dans
  soit t = expand_head_unif env t dans
  reset_trace_gadt_instances reset_tracing;
  t

(*
   Unify [t] and [l:'a -> 'b]. Return ['a] and ['b].
   In label mode, label mismatch is accepted when
   (1) the requested label is ""
   (2) the original label is not optional
*)

soit filter_arrow env t l =
  soit t = expand_head_trace env t dans
  filtre t.desc avec
    Tvar _ ->
      soit lv = t.level dans
      soit t1 = newvar2 lv et t2 = newvar2 lv dans
      soit t' = newty2 lv (Tarrow (l, t1, t2, Cok)) dans
      link_type t t';
      (t1, t2)
  | Tarrow(l', t1, t2, _)
    quand l = l' || !Clflags.classic && l = "" && not (is_optional l') ->
      (t1, t2)
  | _ ->
      raise (Unify [])

(* Used by [filter_method]. *)
soit rec filter_method_field env name priv ty =
  soit ty = expand_head_trace env ty dans
  filtre ty.desc avec
    Tvar _ ->
      soit level = ty.level dans
      soit ty1 = newvar2 level et ty2 = newvar2 level dans
      soit ty' = newty2 level (Tfield (name,
                                      début filtre priv avec
                                        Private -> Fvar (ref None)
                                      | Public  -> Fpresent
                                      fin,
                                      ty1, ty2))
      dans
      link_type ty ty';
      ty1
  | Tfield(n, kind, ty1, ty2) ->
      soit kind = field_kind_repr kind dans
      si (n = name) && (kind <> Fabsent) alors début
        si priv = Public alors
          unify_kind kind Fpresent;
        ty1
      fin sinon
        filter_method_field env name priv ty2
  | _ ->
      raise (Unify [])

(* Unify [ty] and [< name : 'a; .. >]. Return ['a]. *)
soit filter_method env name priv ty =
  soit ty = expand_head_trace env ty dans
  filtre ty.desc avec
    Tvar _ ->
      soit ty1 = newvar () dans
      soit ty' = newobj ty1 dans
      update_level env ty.level ty';
      link_type ty ty';
      filter_method_field env name priv ty1
  | Tobject(f, _) ->
      filter_method_field env name priv f
  | _ ->
      raise (Unify [])

soit check_filter_method env name priv ty =
  ignore(filter_method env name priv ty)

soit filter_self_method env lab priv meths ty =
  soit ty' = filter_method env lab priv ty dans
  essaie
    Meths.find lab !meths
  avec Not_found ->
    soit pair = (Ident.create lab, ty') dans
    meths := Meths.add lab pair !meths;
    pair


                        (***********************************)
                        (*  Matching between type schemes  *)
                        (***********************************)

(*
   Update the level of [ty]. First check that the levels of generic
   variables from the subject are not lowered.
*)
soit moregen_occur env level ty =
  soit rec occur ty =
    soit ty = repr ty dans
    si ty.level > level alors début
      si is_Tvar ty && ty.level >= generic_level - 1 alors raise Occur;
      ty.level <- pivot_level - ty.level;
      filtre ty.desc avec
        Tvariant row quand static_row row ->
          iter_row occur row
      | _ ->
          iter_type_expr occur ty
    fin
  dans
  début essaie
    occur ty; unmark_type ty
  avec Occur ->
    unmark_type ty; raise (Unify [])
  fin;
  (* also check for free univars *)
  occur_univar env ty;
  update_level env level ty

soit may_instantiate inst_nongen t1 =
  si inst_nongen alors t1.level <> generic_level - 1
                 sinon t1.level =  generic_level

soit rec moregen inst_nongen type_pairs env t1 t2 =
  si t1 == t2 alors () sinon
  soit t1 = repr t1 dans
  soit t2 = repr t2 dans
  si t1 == t2 alors () sinon

  essaie
    filtre (t1.desc, t2.desc) avec
      (Tvar _, _) quand may_instantiate inst_nongen t1 ->
        moregen_occur env t1.level t2;
        occur env t1 t2;
        link_type t1 t2
    | (Tconstr (p1, [], _), Tconstr (p2, [], _)) quand Path.same p1 p2 ->
        ()
    | _ ->
        soit t1' = expand_head env t1 dans
        soit t2' = expand_head env t2 dans
        (* Expansion may have changed the representative of the types... *)
        soit t1' = repr t1' et t2' = repr t2' dans
        si t1' == t2' alors () sinon
        début essaie
          TypePairs.find type_pairs (t1', t2')
        avec Not_found ->
          TypePairs.add type_pairs (t1', t2') ();
          filtre (t1'.desc, t2'.desc) avec
            (Tvar _, _) quand may_instantiate inst_nongen t1' ->
              moregen_occur env t1'.level t2;
              link_type t1' t2
          | (Tarrow (l1, t1, u1, _), Tarrow (l2, t2, u2, _)) quand l1 = l2
            || !Clflags.classic && not (is_optional l1 || is_optional l2) ->
              moregen inst_nongen type_pairs env t1 t2;
              moregen inst_nongen type_pairs env u1 u2
          | (Ttuple tl1, Ttuple tl2) ->
              moregen_list inst_nongen type_pairs env tl1 tl2
          | (Tconstr (p1, tl1, _), Tconstr (p2, tl2, _))
                quand Path.same p1 p2 ->
              moregen_list inst_nongen type_pairs env tl1 tl2
          | (Tpackage (p1, n1, tl1), Tpackage (p2, n2, tl2)) ->
              début essaie
                unify_package env (moregen_list inst_nongen type_pairs env)
                  t1'.level p1 n1 tl1 t2'.level p2 n2 tl2
              avec Not_found -> raise (Unify [])
              fin
          | (Tvariant row1, Tvariant row2) ->
              moregen_row inst_nongen type_pairs env row1 row2
          | (Tobject (fi1, nm1), Tobject (fi2, nm2)) ->
              moregen_fields inst_nongen type_pairs env fi1 fi2
          | (Tfield _, Tfield _) ->           (* Actually unused *)
              moregen_fields inst_nongen type_pairs env t1' t2'
          | (Tnil, Tnil) ->
              ()
          | (Tpoly (t1, []), Tpoly (t2, [])) ->
              moregen inst_nongen type_pairs env t1 t2
          | (Tpoly (t1, tl1), Tpoly (t2, tl2)) ->
              enter_poly env univar_pairs t1 tl1 t2 tl2
                (moregen inst_nongen type_pairs env)
          | (Tunivar _, Tunivar _) ->
              unify_univar t1' t2' !univar_pairs
          | (_, _) ->
              raise (Unify [])
        fin
  avec Unify trace ->
    raise (Unify ((t1, t2)::trace))

et moregen_list inst_nongen type_pairs env tl1 tl2 =
  si List.length tl1 <> List.length tl2 alors
    raise (Unify []);
  List.iter2 (moregen inst_nongen type_pairs env) tl1 tl2

et moregen_fields inst_nongen type_pairs env ty1 ty2 =
  soit (fields1, rest1) = flatten_fields ty1
  et (fields2, rest2) = flatten_fields ty2 dans
  soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
  si miss1 <> [] alors raise (Unify []);
  moregen inst_nongen type_pairs env rest1
    (build_fields (repr ty2).level miss2 rest2);
  List.iter
    (fonc (n, k1, t1, k2, t2) ->
       moregen_kind k1 k2;
       essaie moregen inst_nongen type_pairs env t1 t2 avec Unify trace ->
         raise (Unify ((newty (Tfield(n, k1, t1, rest2)),
                        newty (Tfield(n, k2, t2, rest2)))::trace)))
    pairs

et moregen_kind k1 k2 =
  soit k1 = field_kind_repr k1 dans
  soit k2 = field_kind_repr k2 dans
  si k1 == k2 alors () sinon
  filtre k1, k2 avec
    (Fvar r, (Fvar _ | Fpresent))  -> set_kind r k2
  | (Fpresent, Fpresent)           -> ()
  | _                              -> raise (Unify [])

et moregen_row inst_nongen type_pairs env row1 row2 =
  soit row1 = row_repr row1 et row2 = row_repr row2 dans
  soit rm1 = repr row1.row_more et rm2 = repr row2.row_more dans
  si rm1 == rm2 alors () sinon
  soit may_inst =
    is_Tvar rm1 && may_instantiate inst_nongen rm1 || rm1.desc = Tnil dans
  soit r1, r2, pairs = merge_row_fields row1.row_fields row2.row_fields dans
  soit r1, r2 =
    si row2.row_closed alors
      filter_row_fields may_inst r1, filter_row_fields faux r2
    sinon r1, r2
  dans
  si r1 <> [] || row1.row_closed && (not row2.row_closed || r2 <> [])
  alors raise (Unify []);
  début filtre rm1.desc, rm2.desc avec
    Tunivar _, Tunivar _ ->
      unify_univar rm1 rm2 !univar_pairs
  | Tunivar _, _ | _, Tunivar _ ->
      raise (Unify [])
  | _ quand static_row row1 -> ()
  | _ quand may_inst ->
      soit ext = newgenty (Tvariant {row2 avec row_fields = r2}) dans
      moregen_occur env rm1.level ext;
      link_type rm1 ext
  | Tconstr _, Tconstr _ ->
      moregen inst_nongen type_pairs env rm1 rm2
  | _ -> raise (Unify [])
  fin;
  List.iter
    (fonc (l,f1,f2) ->
      soit f1 = row_field_repr f1 et f2 = row_field_repr f2 dans
      si f1 == f2 alors () sinon
      filtre f1, f2 avec
        Rpresent(Some t1), Rpresent(Some t2) ->
          moregen inst_nongen type_pairs env t1 t2
      | Rpresent None, Rpresent None -> ()
      | Reither(faux, tl1, _, e1), Rpresent(Some t2) quand may_inst ->
          set_row_field e1 f2;
          List.iter (fonc t1 -> moregen inst_nongen type_pairs env t1 t2) tl1
      | Reither(c1, tl1, _, e1), Reither(c2, tl2, m2, e2) ->
          si e1 != e2 alors début
            si c1 && not c2 alors raise(Unify []);
            set_row_field e1 (Reither (c2, [], m2, e2));
            si List.length tl1 = List.length tl2 alors
              List.iter2 (moregen inst_nongen type_pairs env) tl1 tl2
            sinon filtre tl2 avec
              t2 :: _ ->
                List.iter (fonc t1 -> moregen inst_nongen type_pairs env t1 t2)
                  tl1
            | [] ->
                si tl1 <> [] alors raise (Unify [])
          fin
      | Reither(vrai, [], _, e1), Rpresent None quand may_inst ->
          set_row_field e1 f2
      | Reither(_, _, _, e1), Rabsent quand may_inst ->
          set_row_field e1 f2
      | Rabsent, Rabsent -> ()
      | _ -> raise (Unify []))
    pairs

(* Must empty univar_pairs first *)
soit moregen inst_nongen type_pairs env patt subj =
  univar_pairs := [];
  moregen inst_nongen type_pairs env patt subj

(*
   Non-generic variable can be instanciated only if [inst_nongen] is
   true. So, [inst_nongen] should be set to false if the subject might
   contain non-generic variables (and we do not want them to be
   instanciated).
   Usually, the subject is given by the user, and the pattern
   is unimportant.  So, no need to propagate abbreviations.
*)
soit moregeneral env inst_nongen pat_sch subj_sch =
  soit old_level = !current_level dans
  current_level := generic_level - 1;
  (*
     Generic variables are first duplicated with [instance].  So,
     their levels are lowered to [generic_level - 1].  The subject is
     then copied with [duplicate_type].  That way, its levels won't be
     changed.
  *)
  soit subj = duplicate_type (instance env subj_sch) dans
  current_level := generic_level;
  (* Duplicate generic variables *)
  soit patt = instance env pat_sch dans
  soit res =
    essaie moregen inst_nongen (TypePairs.create 13) env patt subj; vrai avec
      Unify _ -> faux
  dans
  current_level := old_level;
  res


(* Alternative approach: "rigidify" a type scheme,
   and check validity after unification *)
(* Simpler, no? *)

soit rec rigidify_rec vars ty =
  soit ty = repr ty dans
  si ty.level >= lowest_level alors début
    ty.level <- pivot_level - ty.level;
    filtre ty.desc avec
    | Tvar _ ->
        si not (List.memq ty !vars) alors vars := ty :: !vars
    | Tvariant row ->
        soit row = row_repr row dans
        soit more = repr row.row_more dans
        si is_Tvar more && not (row_fixed row) alors début
          soit more' = newty2 more.level more.desc dans
          soit row' = {row avec row_fixed=vrai; row_fields=[]; row_more=more'}
          dans link_type more (newty2 ty.level (Tvariant row'))
        fin;
        iter_row (rigidify_rec vars) row;
        (* only consider the row variable if the variant is not static *)
        si not (static_row row) alors rigidify_rec vars (row_more row)
    | _ ->
        iter_type_expr (rigidify_rec vars) ty
  fin

soit rigidify ty =
  soit vars = ref [] dans
  rigidify_rec vars ty;
  unmark_type ty;
  !vars

soit all_distinct_vars env vars =
  soit tyl = ref [] dans
  List.for_all
    (fonc ty ->
      soit ty = expand_head env ty dans
      si List.memq ty !tyl alors faux sinon
      (tyl := ty :: !tyl; is_Tvar ty))
    vars

soit matches env ty ty' =
  soit snap = snapshot () dans
  soit vars = rigidify ty dans
  cleanup_abbrev ();
  soit ok =
    essaie unify env ty ty'; all_distinct_vars env vars
    avec Unify _ -> faux
  dans
  backtrack snap;
  ok


                 (*********************************************)
                 (*  Equivalence between parameterized types  *)
                 (*********************************************)

soit rec get_object_row ty =
  filtre repr ty avec
  | {desc=Tfield (_, _, _, tl)} -> get_object_row tl
  | ty -> ty

soit expand_head_rigid env ty =
  soit old = !rigid_variants dans
  rigid_variants := vrai;
  soit ty' = expand_head env ty dans
  rigid_variants := old; ty'

soit normalize_subst subst =
  si List.exists
      (fonction {desc=Tlink _}, _ | _, {desc=Tlink _} -> vrai | _ -> faux)
      !subst
  alors subst := List.map (fonc (t1,t2) -> repr t1, repr t2) !subst

soit rec eqtype rename type_pairs subst env t1 t2 =
  si t1 == t2 alors () sinon
  soit t1 = repr t1 dans
  soit t2 = repr t2 dans
  si t1 == t2 alors () sinon

  essaie
    filtre (t1.desc, t2.desc) avec
      (Tvar _, Tvar _) quand rename ->
        début essaie
          normalize_subst subst;
          si List.assq t1 !subst != t2 alors raise (Unify [])
        avec Not_found ->
          si List.exists (fonc (_, t) -> t == t2) !subst alors raise (Unify []);
          subst := (t1, t2) :: !subst
        fin
    | (Tconstr (p1, [], _), Tconstr (p2, [], _)) quand Path.same p1 p2 ->
        ()
    | _ ->
        soit t1' = expand_head_rigid env t1 dans
        soit t2' = expand_head_rigid env t2 dans
        (* Expansion may have changed the representative of the types... *)
        soit t1' = repr t1' et t2' = repr t2' dans
        si t1' == t2' alors () sinon
        début essaie
          TypePairs.find type_pairs (t1', t2')
        avec Not_found ->
          TypePairs.add type_pairs (t1', t2') ();
          filtre (t1'.desc, t2'.desc) avec
            (Tvar _, Tvar _) quand rename ->
              début essaie
                normalize_subst subst;
                si List.assq t1' !subst != t2' alors raise (Unify [])
              avec Not_found ->
                si List.exists (fonc (_, t) -> t == t2') !subst
                alors raise (Unify []);
                subst := (t1', t2') :: !subst
              fin
          | (Tarrow (l1, t1, u1, _), Tarrow (l2, t2, u2, _)) quand l1 = l2
            || !Clflags.classic && not (is_optional l1 || is_optional l2) ->
              eqtype rename type_pairs subst env t1 t2;
              eqtype rename type_pairs subst env u1 u2;
          | (Ttuple tl1, Ttuple tl2) ->
              eqtype_list rename type_pairs subst env tl1 tl2
          | (Tconstr (p1, tl1, _), Tconstr (p2, tl2, _))
                quand Path.same p1 p2 ->
              eqtype_list rename type_pairs subst env tl1 tl2
          | (Tpackage (p1, n1, tl1), Tpackage (p2, n2, tl2)) ->
              début essaie
                unify_package env (eqtype_list rename type_pairs subst env)
                  t1'.level p1 n1 tl1 t2'.level p2 n2 tl2
              avec Not_found -> raise (Unify [])
              fin
          | (Tvariant row1, Tvariant row2) ->
              eqtype_row rename type_pairs subst env row1 row2
          | (Tobject (fi1, nm1), Tobject (fi2, nm2)) ->
              eqtype_fields rename type_pairs subst env fi1 fi2
          | (Tfield _, Tfield _) ->       (* Actually unused *)
              eqtype_fields rename type_pairs subst env t1' t2'
          | (Tnil, Tnil) ->
              ()
          | (Tpoly (t1, []), Tpoly (t2, [])) ->
              eqtype rename type_pairs subst env t1 t2
          | (Tpoly (t1, tl1), Tpoly (t2, tl2)) ->
              enter_poly env univar_pairs t1 tl1 t2 tl2
                (eqtype rename type_pairs subst env)
          | (Tunivar _, Tunivar _) ->
              unify_univar t1' t2' !univar_pairs
          | (_, _) ->
              raise (Unify [])
        fin
  avec Unify trace ->
    raise (Unify ((t1, t2)::trace))

et eqtype_list rename type_pairs subst env tl1 tl2 =
  si List.length tl1 <> List.length tl2 alors
    raise (Unify []);
  List.iter2 (eqtype rename type_pairs subst env) tl1 tl2

et eqtype_fields rename type_pairs subst env ty1 ty2 =
  soit (fields1, rest1) = flatten_fields ty1 dans
  soit (fields2, rest2) = flatten_fields ty2 dans
  (* First check if same row => already equal *)
  soit same_row =
    rest1 == rest2 || TypePairs.mem type_pairs (rest1,rest2) ||
    (rename && List.mem (rest1, rest2) !subst)
  dans
  si same_row alors () sinon
  (* Try expansion, needed when called from Includecore.type_manifest *)
  filtre expand_head_rigid env rest2 avec
    {desc=Tobject(ty2,_)} -> eqtype_fields rename type_pairs subst env ty1 ty2
  | _ ->
  soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
  eqtype rename type_pairs subst env rest1 rest2;
  si (miss1 <> []) || (miss2 <> []) alors raise (Unify []);
  List.iter
    (fonction (n, k1, t1, k2, t2) ->
       eqtype_kind k1 k2;
       essaie eqtype rename type_pairs subst env t1 t2 avec Unify trace ->
         raise (Unify ((newty (Tfield(n, k1, t1, rest2)),
                        newty (Tfield(n, k2, t2, rest2)))::trace)))
    pairs

et eqtype_kind k1 k2 =
  soit k1 = field_kind_repr k1 dans
  soit k2 = field_kind_repr k2 dans
  filtre k1, k2 avec
    (Fvar _, Fvar _)
  | (Fpresent, Fpresent) -> ()
  | _                    -> raise (Unify [])

et eqtype_row rename type_pairs subst env row1 row2 =
  (* Try expansion, needed when called from Includecore.type_manifest *)
  filtre expand_head_rigid env (row_more row2) avec
    {desc=Tvariant row2} -> eqtype_row rename type_pairs subst env row1 row2
  | _ ->
  soit row1 = row_repr row1 et row2 = row_repr row2 dans
  soit r1, r2, pairs = merge_row_fields row1.row_fields row2.row_fields dans
  si row1.row_closed <> row2.row_closed
  || not row1.row_closed && (r1 <> [] || r2 <> [])
  || filter_row_fields faux (r1 @ r2) <> []
  alors raise (Unify []);
  si not (static_row row1) alors
    eqtype rename type_pairs subst env row1.row_more row2.row_more;
  List.iter
    (fonc (_,f1,f2) ->
      filtre row_field_repr f1, row_field_repr f2 avec
        Rpresent(Some t1), Rpresent(Some t2) ->
          eqtype rename type_pairs subst env t1 t2
      | Reither(vrai, [], _, _), Reither(vrai, [], _, _) ->
          ()
      | Reither(faux, t1::tl1, _, _), Reither(faux, t2::tl2, _, _) ->
          eqtype rename type_pairs subst env t1 t2;
          si List.length tl1 = List.length tl2 alors
            (* if same length allow different types (meaning?) *)
            List.iter2 (eqtype rename type_pairs subst env) tl1 tl2
          sinon début
            (* otherwise everything must be equal *)
            List.iter (eqtype rename type_pairs subst env t1) tl2;
            List.iter (fonc t1 -> eqtype rename type_pairs subst env t1 t2) tl1
          fin
      | Rpresent None, Rpresent None -> ()
      | Rabsent, Rabsent -> ()
      | _ -> raise (Unify []))
    pairs

(* Two modes: with or without renaming of variables *)
soit equal env rename tyl1 tyl2 =
  essaie
    univar_pairs := [];
    eqtype_list rename (TypePairs.create 11) (ref []) env tyl1 tyl2; vrai
  avec
    Unify _ -> faux

(* Must empty univar_pairs first *)
soit eqtype rename type_pairs subst env t1 t2 =
  univar_pairs := [];
  eqtype rename type_pairs subst env t1 t2


                          (*************************)
                          (*  Class type matching  *)
                          (*************************)


type class_match_failure =
    CM_Virtual_class
  | CM_Parameter_arity_mismatch de int * int
  | CM_Type_parameter_mismatch de Env.t * (type_expr * type_expr) list
  | CM_Class_type_mismatch de Env.t * class_type * class_type
  | CM_Parameter_mismatch de Env.t * (type_expr * type_expr) list
  | CM_Val_type_mismatch de string * Env.t * (type_expr * type_expr) list
  | CM_Meth_type_mismatch de string * Env.t * (type_expr * type_expr) list
  | CM_Non_mutable_value de string
  | CM_Non_concrete_value de string
  | CM_Missing_value de string
  | CM_Missing_method de string
  | CM_Hide_public de string
  | CM_Hide_virtual de string * string
  | CM_Public_method de string
  | CM_Private_method de string
  | CM_Virtual_method de string

exception Failure de class_match_failure list

soit rec moregen_clty trace type_pairs env cty1 cty2 =
  essaie
    filtre cty1, cty2 avec
      Cty_constr (_, _, cty1), _ ->
        moregen_clty vrai type_pairs env cty1 cty2
    | _, Cty_constr (_, _, cty2) ->
        moregen_clty vrai type_pairs env cty1 cty2
    | Cty_arrow (l1, ty1, cty1'), Cty_arrow (l2, ty2, cty2') quand l1 = l2 ->
        début essaie moregen vrai type_pairs env ty1 ty2 avec Unify trace ->
          raise (Failure [CM_Parameter_mismatch (env, expand_trace env trace)])
        fin;
        moregen_clty faux type_pairs env cty1' cty2'
    | Cty_signature sign1, Cty_signature sign2 ->
        soit ty1 = object_fields (repr sign1.csig_self) dans
        soit ty2 = object_fields (repr sign2.csig_self) dans
        soit (fields1, rest1) = flatten_fields ty1
        et (fields2, rest2) = flatten_fields ty2 dans
        soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
        List.iter
          (fonc (lab, k1, t1, k2, t2) ->
            début essaie moregen vrai type_pairs env t1 t2 avec Unify trace ->
              raise (Failure [CM_Meth_type_mismatch
                                 (lab, env, expand_trace env trace)])
           fin)
        pairs;
      Vars.iter
        (fonc lab (mut, v, ty) ->
           soit (mut', v', ty') = Vars.find lab sign1.csig_vars dans
           essaie moregen vrai type_pairs env ty' ty avec Unify trace ->
             raise (Failure [CM_Val_type_mismatch
                                (lab, env, expand_trace env trace)]))
        sign2.csig_vars
  | _ ->
      raise (Failure [])
  avec
    Failure error quand trace || error = [] ->
      raise (Failure (CM_Class_type_mismatch (env, cty1, cty2)::error))

soit match_class_types ?(trace=vrai) env pat_sch subj_sch =
  soit type_pairs = TypePairs.create 53 dans
  soit old_level = !current_level dans
  current_level := generic_level - 1;
  (*
     Generic variables are first duplicated with [instance].  So,
     their levels are lowered to [generic_level - 1].  The subject is
     then copied with [duplicate_type].  That way, its levels won't be
     changed.
  *)
  soit (_, subj_inst) = instance_class [] subj_sch dans
  soit subj = duplicate_class_type subj_inst dans
  current_level := generic_level;
  (* Duplicate generic variables *)
  soit (_, patt) = instance_class [] pat_sch dans
  soit res =
    soit sign1 = signature_of_class_type patt dans
    soit sign2 = signature_of_class_type subj dans
    soit t1 = repr sign1.csig_self dans
    soit t2 = repr sign2.csig_self dans
    TypePairs.add type_pairs (t1, t2) ();
    soit (fields1, rest1) = flatten_fields (object_fields t1)
    et (fields2, rest2) = flatten_fields (object_fields t2) dans
    soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
    soit error =
      List.fold_right
        (fonc (lab, k, _) err ->
           soit err =
             soit k = field_kind_repr k dans
             début filtre k avec
               Fvar r -> set_kind r Fabsent; err
             | _      -> CM_Hide_public lab::err
             fin
           dans
           si Concr.mem lab sign1.csig_concr alors err
           sinon CM_Hide_virtual ("method", lab) :: err)
        miss1 []
    dans
    soit missing_method = List.map (fonc (m, _, _) -> m) miss2 dans
    soit error =
      (List.map (fonc m -> CM_Missing_method m) missing_method) @ error
    dans
    (* Always succeeds *)
    moregen vrai type_pairs env rest1 rest2;
    soit error =
      List.fold_right
        (fonc (lab, k1, t1, k2, t2) err ->
           essaie moregen_kind k1 k2; err avec
             Unify _ -> CM_Public_method lab::err)
        pairs error
    dans
    soit error =
      Vars.fold
        (fonc lab (mut, vr, ty) err ->
          essaie
            soit (mut', vr', ty') = Vars.find lab sign1.csig_vars dans
            si mut = Mutable && mut' <> Mutable alors
              CM_Non_mutable_value lab::err
            sinon si vr = Concrete && vr' <> Concrete alors
              CM_Non_concrete_value lab::err
            sinon
              err
          avec Not_found ->
            CM_Missing_value lab::err)
        sign2.csig_vars error
    dans
    soit error =
      Vars.fold
        (fonc lab (_,vr,_) err ->
          si vr = Virtual && not (Vars.mem lab sign2.csig_vars) alors
            CM_Hide_virtual ("instance variable", lab) :: err
          sinon err)
        sign1.csig_vars error
    dans
    soit error =
      List.fold_right
        (fonc e l ->
           si List.mem e missing_method alors l sinon CM_Virtual_method e::l)
        (Concr.elements (Concr.diff sign2.csig_concr sign1.csig_concr))
        error
    dans
    filtre error avec
      [] ->
        début essaie
          moregen_clty trace type_pairs env patt subj;
          []
        avec
          Failure r -> r
        fin
    | error ->
        CM_Class_type_mismatch (env, patt, subj)::error
  dans
  current_level := old_level;
  res

soit rec equal_clty trace type_pairs subst env cty1 cty2 =
  essaie
    filtre cty1, cty2 avec
      Cty_constr (_, _, cty1), Cty_constr (_, _, cty2) ->
        equal_clty vrai type_pairs subst env cty1 cty2
    | Cty_constr (_, _, cty1), _ ->
        equal_clty vrai type_pairs subst env cty1 cty2
    | _, Cty_constr (_, _, cty2) ->
        equal_clty vrai type_pairs subst env cty1 cty2
    | Cty_arrow (l1, ty1, cty1'), Cty_arrow (l2, ty2, cty2') quand l1 = l2 ->
        début essaie eqtype vrai type_pairs subst env ty1 ty2 avec Unify trace ->
          raise (Failure [CM_Parameter_mismatch (env, expand_trace env trace)])
        fin;
        equal_clty faux type_pairs subst env cty1' cty2'
    | Cty_signature sign1, Cty_signature sign2 ->
        soit ty1 = object_fields (repr sign1.csig_self) dans
        soit ty2 = object_fields (repr sign2.csig_self) dans
        soit (fields1, rest1) = flatten_fields ty1
        et (fields2, rest2) = flatten_fields ty2 dans
        soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
        List.iter
          (fonc (lab, k1, t1, k2, t2) ->
             début essaie eqtype vrai type_pairs subst env t1 t2 avec
               Unify trace ->
                 raise (Failure [CM_Meth_type_mismatch
                                    (lab, env, expand_trace env trace)])
             fin)
          pairs;
        Vars.iter
          (fonc lab (_, _, ty) ->
             soit (_, _, ty') = Vars.find lab sign1.csig_vars dans
             essaie eqtype vrai type_pairs subst env ty' ty avec Unify trace ->
               raise (Failure [CM_Val_type_mismatch
                                  (lab, env, expand_trace env trace)]))
          sign2.csig_vars
    | _ ->
        raise
          (Failure (si trace alors []
                    sinon [CM_Class_type_mismatch (env, cty1, cty2)]))
  avec
    Failure error quand trace ->
      raise (Failure (CM_Class_type_mismatch (env, cty1, cty2)::error))

soit match_class_declarations env patt_params patt_type subj_params subj_type =
  soit type_pairs = TypePairs.create 53 dans
  soit subst = ref [] dans
  soit sign1 = signature_of_class_type patt_type dans
  soit sign2 = signature_of_class_type subj_type dans
  soit t1 = repr sign1.csig_self dans
  soit t2 = repr sign2.csig_self dans
  TypePairs.add type_pairs (t1, t2) ();
  soit (fields1, rest1) = flatten_fields (object_fields t1)
  et (fields2, rest2) = flatten_fields (object_fields t2) dans
  soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
  soit error =
    List.fold_right
      (fonc (lab, k, _) err ->
        soit err =
          soit k = field_kind_repr k dans
          début filtre k avec
            Fvar r -> err
          | _      -> CM_Hide_public lab::err
          fin
        dans
        si Concr.mem lab sign1.csig_concr alors err
        sinon CM_Hide_virtual ("method", lab) :: err)
      miss1 []
  dans
  soit missing_method = List.map (fonc (m, _, _) -> m) miss2 dans
  soit error =
    (List.map (fonc m -> CM_Missing_method m) missing_method) @ error
  dans
  (* Always succeeds *)
  eqtype vrai type_pairs subst env rest1 rest2;
  soit error =
    List.fold_right
      (fonc (lab, k1, t1, k2, t2) err ->
        soit k1 = field_kind_repr k1 dans
        soit k2 = field_kind_repr k2 dans
        filtre k1, k2 avec
          (Fvar _, Fvar _)
        | (Fpresent, Fpresent) -> err
        | (Fvar _, Fpresent)   -> CM_Private_method lab::err
        | (Fpresent, Fvar _)  -> CM_Public_method lab::err
        | _                    -> affirme faux)
      pairs error
  dans
  soit error =
    Vars.fold
      (fonc lab (mut, vr, ty) err ->
         essaie
           soit (mut', vr', ty') = Vars.find lab sign1.csig_vars dans
           si mut = Mutable && mut' <> Mutable alors
             CM_Non_mutable_value lab::err
           sinon si vr = Concrete && vr' <> Concrete alors
             CM_Non_concrete_value lab::err
           sinon
             err
         avec Not_found ->
           CM_Missing_value lab::err)
      sign2.csig_vars error
  dans
  soit error =
    Vars.fold
      (fonc lab (_,vr,_) err ->
        si vr = Virtual && not (Vars.mem lab sign2.csig_vars) alors
          CM_Hide_virtual ("instance variable", lab) :: err
        sinon err)
      sign1.csig_vars error
  dans
  soit error =
    List.fold_right
      (fonc e l ->
        si List.mem e missing_method alors l sinon CM_Virtual_method e::l)
      (Concr.elements (Concr.diff sign2.csig_concr sign1.csig_concr))
      error
  dans
  filtre error avec
    [] ->
      début essaie
        soit lp = List.length patt_params dans
        soit ls = List.length subj_params dans
        si lp  <> ls alors
          raise (Failure [CM_Parameter_arity_mismatch (lp, ls)]);
        List.iter2 (fonc p s ->
          essaie eqtype vrai type_pairs subst env p s avec Unify trace ->
            raise (Failure [CM_Type_parameter_mismatch
                               (env, expand_trace env trace)]))
          patt_params subj_params;
     (* old code: equal_clty false type_pairs subst env patt_type subj_type; *)
        equal_clty faux type_pairs subst env
          (Cty_signature sign1) (Cty_signature sign2);
        (* Use moregeneral for class parameters, need to recheck everything to
           keeps relationships (PR#4824) *)
        soit clty_params =
          List.fold_right (fonc ty cty -> Cty_arrow ("*",ty,cty)) dans
        match_class_types ~trace:faux env
          (clty_params patt_params patt_type)
          (clty_params subj_params subj_type)
      avec
        Failure r -> r
      fin
  | error ->
      error


                              (***************)
                              (*  Subtyping  *)
                              (***************)


(**** Build a subtype of a given type. ****)

(* build_subtype:
   [visited] traces traversed object and variant types
   [loops] is a mapping from variables to variables, to reproduce
     positive loops in a class type
   [posi] true if the current variance is positive
   [level] number of expansions/enlargement allowed on this branch *)

soit warn = ref faux  (* whether double coercion might do better *)
soit pred_expand n = si n mod 2 = 0 && n > 0 alors pred n sinon n
soit pred_enlarge n = si n mod 2 = 1 alors pred n sinon n

type change = Unchanged | Equiv | Changed
soit collect l = List.fold_left (fonc c1 (_, c2) -> max c1 c2) Unchanged l

soit rec filter_visited = fonction
    [] -> []
  | {desc=Tobject _|Tvariant _} :: _ tel l -> l
  | _ :: l -> filter_visited l

soit memq_warn t visited =
  si List.memq t visited alors (warn := vrai; vrai) sinon faux

soit rec lid_of_path ?(sharp="") = fonction
    Path.Pident id ->
      Longident.Lident (sharp ^ Ident.name id)
  | Path.Pdot (p1, s, _) ->
      Longident.Ldot (lid_of_path p1, sharp ^ s)
  | Path.Papply (p1, p2) ->
      Longident.Lapply (lid_of_path ~sharp p1, lid_of_path p2)

soit find_cltype_for_path env p =
  soit path, cl_abbr = Env.lookup_type (lid_of_path ~sharp:"#" p) env dans
  filtre cl_abbr.type_manifest avec
    Some ty ->
      début filtre (repr ty).desc avec
        Tobject(_,{contents=Some(p',_)}) quand Path.same p p' -> cl_abbr, ty
      | _ -> raise Not_found
      fin
  | None -> affirme faux

soit has_constr_row' env t =
  has_constr_row (expand_abbrev env t)

soit rec build_subtype env visited loops posi level t =
  soit t = repr t dans
  filtre t.desc avec
    Tvar _ ->
      si posi alors
        essaie
          soit t' = List.assq t loops dans
          warn := vrai;
          (t', Equiv)
        avec Not_found ->
          (t, Unchanged)
      sinon
        (t, Unchanged)
  | Tarrow(l, t1, t2, _) ->
      si memq_warn t visited alors (t, Unchanged) sinon
      soit visited = t :: visited dans
      soit (t1', c1) = build_subtype env visited loops (not posi) level t1 dans
      soit (t2', c2) = build_subtype env visited loops posi level t2 dans
      soit c = max c1 c2 dans
      si c > Unchanged alors (newty (Tarrow(l, t1', t2', Cok)), c)
      sinon (t, Unchanged)
  | Ttuple tlist ->
      si memq_warn t visited alors (t, Unchanged) sinon
      soit visited = t :: visited dans
      soit tlist' =
        List.map (build_subtype env visited loops posi level) tlist
      dans
      soit c = collect tlist' dans
      si c > Unchanged alors (newty (Ttuple (List.map fst tlist')), c)
      sinon (t, Unchanged)
  | Tconstr(p, tl, abbrev)
    quand level > 0 && generic_abbrev env p && safe_abbrev env t
    && not (has_constr_row' env t) ->
      soit t' = repr (expand_abbrev env t) dans
      soit level' = pred_expand level dans
      début essaie filtre t'.desc avec
        Tobject _ quand posi && not (opened_object t') ->
          soit cl_abbr, body = find_cltype_for_path env p dans
          soit ty =
            subst env !current_level Public abbrev None
              cl_abbr.type_params tl body dans
          soit ty = repr ty dans
          soit ty1, tl1 =
            filtre ty.desc avec
              Tobject(ty1,{contents=Some(p',tl1)}) quand Path.same p p' ->
                ty1, tl1
            | _ -> raise Not_found
          dans
          (* Fix PR4505: do not set ty to Tvar when it appears in tl1,
             as this occurence might break the occur check.
             XXX not clear whether this correct anyway... *)
          si List.exists (deep_occur ty) tl1 alors raise Not_found;
          ty.desc <- Tvar None;
          soit t'' = newvar () dans
          soit loops = (ty, t'') :: loops dans
          (* May discard [visited] as level is going down *)
          soit (ty1', c) =
            build_subtype env [t'] loops posi (pred_enlarge level') ty1 dans
          affirme (is_Tvar t'');
          soit nm =
            si c > Equiv || deep_occur ty ty1' alors None sinon Some(p,tl1) dans
          t''.desc <- Tobject (ty1', ref nm);
          (essaie unify_var env ty t avec Unify _ -> affirme faux);
          (t'', Changed)
      | _ -> raise Not_found
      avec Not_found ->
        soit (t'',c) = build_subtype env visited loops posi level' t' dans
        si c > Unchanged alors (t'',c)
        sinon (t, Unchanged)
      fin
  | Tconstr(p, tl, abbrev) ->
      (* Must check recursion on constructors, since we do not always
         expand them *)
      si memq_warn t visited alors (t, Unchanged) sinon
      soit visited = t :: visited dans
      début essaie
        soit decl = Env.find_type p env dans
        si level = 0 && generic_abbrev env p && safe_abbrev env t
        && not (has_constr_row' env t)
        alors warn := vrai;
        soit tl' =
          List.map2
            (fonc v t ->
              soit (co,cn) = Variance.get_upper v dans
              si cn alors
                si co alors (t, Unchanged)
                sinon build_subtype env visited loops (not posi) level t
              sinon
                si co alors build_subtype env visited loops posi level t
                sinon (newvar(), Changed))
            decl.type_variance tl
        dans
        soit c = collect tl' dans
        si c > Unchanged alors (newconstr p (List.map fst tl'), c)
        sinon (t, Unchanged)
      avec Not_found ->
        (t, Unchanged)
      fin
  | Tvariant row ->
      soit row = row_repr row dans
      si memq_warn t visited || not (static_row row) alors (t, Unchanged) sinon
      soit level' = pred_enlarge level dans
      soit visited =
        t :: si level' < level alors [] sinon filter_visited visited dans
      soit fields = filter_row_fields faux row.row_fields dans
      soit fields =
        List.map
          (fonc (l,f tel orig) -> filtre row_field_repr f avec
            Rpresent None ->
              si posi alors
                (l, Reither(vrai, [], faux, ref None)), Unchanged
              sinon
                orig, Unchanged
          | Rpresent(Some t) ->
              soit (t', c) = build_subtype env visited loops posi level' t dans
              soit f =
                si posi && level > 0
                alors Reither(faux, [t'], faux, ref None)
                sinon Rpresent(Some t')
              dans (l, f), c
          | _ -> affirme faux)
          fields
      dans
      soit c = collect fields dans
      soit row =
        { row_fields = List.map fst fields; row_more = newvar();
          row_bound = (); row_closed = posi; row_fixed = faux;
          row_name = si c > Unchanged alors None sinon row.row_name }
      dans
      (newty (Tvariant row), Changed)
  | Tobject (t1, _) ->
      si memq_warn t visited || opened_object t1 alors (t, Unchanged) sinon
      soit level' = pred_enlarge level dans
      soit visited =
        t :: si level' < level alors [] sinon filter_visited visited dans
      soit (t1', c) = build_subtype env visited loops posi level' t1 dans
      si c > Unchanged alors (newty (Tobject (t1', ref None)), c)
      sinon (t, Unchanged)
  | Tfield(s, _, t1, t2) (* Always present *) ->
      soit (t1', c1) = build_subtype env visited loops posi level t1 dans
      soit (t2', c2) = build_subtype env visited loops posi level t2 dans
      soit c = max c1 c2 dans
      si c > Unchanged alors (newty (Tfield(s, Fpresent, t1', t2')), c)
      sinon (t, Unchanged)
  | Tnil ->
      si posi alors
        soit v = newvar () dans
        (v, Changed)
      sinon début
        warn := vrai;
        (t, Unchanged)
      fin
  | Tsubst _ | Tlink _ ->
      affirme faux
  | Tpoly(t1, tl) ->
      soit (t1', c) = build_subtype env visited loops posi level t1 dans
      si c > Unchanged alors (newty (Tpoly(t1', tl)), c)
      sinon (t, Unchanged)
  | Tunivar _ | Tpackage _ ->
      (t, Unchanged)

soit enlarge_type env ty =
  warn := faux;
  (* [level = 4] allows 2 expansions involving objects/variants *)
  soit (ty', _) = build_subtype env [] [] vrai 4 ty dans
  (ty', !warn)

(**** Check whether a type is a subtype of another type. ****)

(*
    During the traversal, a trace of visited types is maintained. It
    is printed in case of error.
    Constraints (pairs of types that must be equals) are accumulated
    rather than being enforced straight. Indeed, the result would
    otherwise depend on the order in which these constraints are
    enforced.
    A function enforcing these constraints is returned. That way, type
    variables can be bound to their actual values before this function
    is called (see Typecore).
    Only well-defined abbreviations are expanded (hence the tests
    [generic_abbrev ...]).
*)

soit subtypes = TypePairs.create 17

soit subtype_error env trace =
  raise (Subtype (expand_trace env (List.rev trace), []))

(* check list inclusion, assuming lists are ordered *)
soit rec included nl1 nl2 =
  filtre nl1, nl2 avec
    (a::nl1', b::nl2') ->
      si a = b alors included nl1' nl2' sinon
      a > b && included nl1 nl2'
  | ([], _) -> vrai
  | (_, []) -> faux

soit rec extract_assoc nl1 nl2 tl2 =
  filtre (nl1, nl2, tl2) avec
    (a::nl1', b::nl2, t::tl2) ->
      si a = b alors t :: extract_assoc nl1' nl2 tl2
      sinon extract_assoc nl1 nl2 tl2
  | ([], _, _) -> []
  | _ -> affirme faux

soit rec subtype_rec env trace t1 t2 cstrs =
  soit t1 = repr t1 dans
  soit t2 = repr t2 dans
  si t1 == t2 alors cstrs sinon

  début essaie
    TypePairs.find subtypes (t1, t2);
    cstrs
  avec Not_found ->
    TypePairs.add subtypes (t1, t2) ();
    filtre (t1.desc, t2.desc) avec
      (Tvar _, _) | (_, Tvar _) ->
        (trace, t1, t2, !univar_pairs)::cstrs
    | (Tarrow(l1, t1, u1, _), Tarrow(l2, t2, u2, _)) quand l1 = l2
      || !Clflags.classic && not (is_optional l1 || is_optional l2) ->
        soit cstrs = subtype_rec env ((t2, t1)::trace) t2 t1 cstrs dans
        subtype_rec env ((u1, u2)::trace) u1 u2 cstrs
    | (Ttuple tl1, Ttuple tl2) ->
        subtype_list env trace tl1 tl2 cstrs
    | (Tconstr(p1, [], _), Tconstr(p2, [], _)) quand Path.same p1 p2 ->
        cstrs
    | (Tconstr(p1, tl1, abbrev1), _)
      quand generic_abbrev env p1 && safe_abbrev env t1 ->
        subtype_rec env trace (expand_abbrev env t1) t2 cstrs
    | (_, Tconstr(p2, tl2, abbrev2))
      quand generic_abbrev env p2 && safe_abbrev env t2 ->
        subtype_rec env trace t1 (expand_abbrev env t2) cstrs
    | (Tconstr(p1, tl1, _), Tconstr(p2, tl2, _)) quand Path.same p1 p2 ->
        début essaie
          soit decl = Env.find_type p1 env dans
          List.fold_left2
            (fonc cstrs v (t1, t2) ->
              soit (co, cn) = Variance.get_upper v dans
              si co alors
                si cn alors
                  (trace, newty2 t1.level (Ttuple[t1]),
                   newty2 t2.level (Ttuple[t2]), !univar_pairs) :: cstrs
                sinon subtype_rec env ((t1, t2)::trace) t1 t2 cstrs
              sinon
                si cn alors subtype_rec env ((t2, t1)::trace) t2 t1 cstrs
                sinon cstrs)
            cstrs decl.type_variance (List.combine tl1 tl2)
        avec Not_found ->
          (trace, t1, t2, !univar_pairs)::cstrs
        fin
    | (Tconstr(p1, _, _), _) quand generic_private_abbrev env p1 ->
        subtype_rec env trace (expand_abbrev_opt env t1) t2 cstrs
(*  | (_, Tconstr(p2, _, _)) when generic_private_abbrev false env p2 ->
        subtype_rec env trace t1 (expand_abbrev_opt env t2) cstrs *)
    | (Tobject (f1, _), Tobject (f2, _))
      quand is_Tvar (object_row f1) && is_Tvar (object_row f2) ->
        (* Same row variable implies same object. *)
        (trace, t1, t2, !univar_pairs)::cstrs
    | (Tobject (f1, _), Tobject (f2, _)) ->
        subtype_fields env trace f1 f2 cstrs
    | (Tvariant row1, Tvariant row2) ->
        début essaie
          subtype_row env trace row1 row2 cstrs
        avec Exit ->
          (trace, t1, t2, !univar_pairs)::cstrs
        fin
    | (Tpoly (u1, []), Tpoly (u2, [])) ->
        subtype_rec env trace u1 u2 cstrs
    | (Tpoly (u1, tl1), Tpoly (u2, [])) ->
        soit _, u1' = instance_poly faux tl1 u1 dans
        subtype_rec env trace u1' u2 cstrs
    | (Tpoly (u1, tl1), Tpoly (u2,tl2)) ->
        début essaie
          enter_poly env univar_pairs u1 tl1 u2 tl2
            (fonc t1 t2 -> subtype_rec env trace t1 t2 cstrs)
        avec Unify _ ->
          (trace, t1, t2, !univar_pairs)::cstrs
        fin
(*    | (Tpackage (p1, nl1, tl1), Tpackage (p2, nl2, tl2))
      when eq_package_path env p1 p2 && included nl2 nl1 ->
        List.map2 (fun t1 t2 -> (trace, t1, t2, !univar_pairs))
          (extract_assoc nl2 nl1 tl1) tl2
        @ cstrs *)
    | (Tpackage (p1, nl1, tl1), Tpackage (p2, nl2, tl2)) ->
        début essaie
          soit ntl1 = complete_type_list env nl2 t1.level (Mty_ident p1) nl1 tl1
          et ntl2 = complete_type_list env nl1 t2.level (Mty_ident p2) nl2 tl2
              ~allow_absent:vrai dans
          soit cstrs' =
            List.map
              (fonc (n2,t2) -> (trace, List.assoc n2 ntl1, t2, !univar_pairs))
              ntl2
          dans
          si eq_package_path env p1 p2 alors cstrs' @ cstrs
          sinon début
            (* need to check module subtyping *)
            soit snap = Btype.snapshot () dans
            essaie
              List.iter (fonc (_, t1, t2, _) -> unify env t1 t2) cstrs';
              si !package_subtype env p1 nl1 tl1 p2 nl2 tl2
              alors (Btype.backtrack snap; cstrs' @ cstrs)
              sinon raise (Unify [])
            avec Unify _ ->
              Btype.backtrack snap; raise Not_found
          fin
        avec Not_found ->
          (trace, t1, t2, !univar_pairs)::cstrs
        fin
    | (_, _) ->
        (trace, t1, t2, !univar_pairs)::cstrs
  fin

et subtype_list env trace tl1 tl2 cstrs =
  si List.length tl1 <> List.length tl2 alors
    subtype_error env trace;
  List.fold_left2
    (fonc cstrs t1 t2 -> subtype_rec env ((t1, t2)::trace) t1 t2 cstrs)
    cstrs tl1 tl2

et subtype_fields env trace ty1 ty2 cstrs =
  (* Assume that either rest1 or rest2 is not Tvar *)
  soit (fields1, rest1) = flatten_fields ty1 dans
  soit (fields2, rest2) = flatten_fields ty2 dans
  soit (pairs, miss1, miss2) = associate_fields fields1 fields2 dans
  soit cstrs =
    si rest2.desc = Tnil alors cstrs sinon
    si miss1 = [] alors
      subtype_rec env ((rest1, rest2)::trace) rest1 rest2 cstrs
    sinon
      (trace, build_fields (repr ty1).level miss1 rest1, rest2,
       !univar_pairs) :: cstrs
  dans
  soit cstrs =
    si miss2 = [] alors cstrs sinon
    (trace, rest1, build_fields (repr ty2).level miss2 (newvar ()),
     !univar_pairs) :: cstrs
  dans
  List.fold_left
    (fonc cstrs (_, k1, t1, k2, t2) ->
      (* Theses fields are always present *)
      subtype_rec env ((t1, t2)::trace) t1 t2 cstrs)
    cstrs pairs

et subtype_row env trace row1 row2 cstrs =
  soit row1 = row_repr row1 et row2 = row_repr row2 dans
  soit r1, r2, pairs =
    merge_row_fields row1.row_fields row2.row_fields dans
  soit more1 = repr row1.row_more
  et more2 = repr row2.row_more dans
  filtre more1.desc, more2.desc avec
    Tconstr(p1,_,_), Tconstr(p2,_,_) quand Path.same p1 p2 ->
      subtype_rec env ((more1,more2)::trace) more1 more2 cstrs
  | (Tvar _|Tconstr _|Tnil), (Tvar _|Tconstr _|Tnil)
    quand row1.row_closed && r1 = [] ->
      List.fold_left
        (fonc cstrs (_,f1,f2) ->
          filtre row_field_repr f1, row_field_repr f2 avec
            (Rpresent None|Reither(vrai,_,_,_)), Rpresent None ->
              cstrs
          | Rpresent(Some t1), Rpresent(Some t2) ->
              subtype_rec env ((t1, t2)::trace) t1 t2 cstrs
          | Reither(faux, t1::_, _, _), Rpresent(Some t2) ->
              subtype_rec env ((t1, t2)::trace) t1 t2 cstrs
          | Rabsent, _ -> cstrs
          | _ -> raise Exit)
        cstrs pairs
  | Tunivar _, Tunivar _
    quand row1.row_closed = row2.row_closed && r1 = [] && r2 = [] ->
      soit cstrs =
        subtype_rec env ((more1,more2)::trace) more1 more2 cstrs dans
      List.fold_left
        (fonc cstrs (_,f1,f2) ->
          filtre row_field_repr f1, row_field_repr f2 avec
            Rpresent None, Rpresent None
          | Reither(vrai,[],_,_), Reither(vrai,[],_,_)
          | Rabsent, Rabsent ->
              cstrs
          | Rpresent(Some t1), Rpresent(Some t2)
          | Reither(faux,[t1],_,_), Reither(faux,[t2],_,_) ->
              subtype_rec env ((t1, t2)::trace) t1 t2 cstrs
          | _ -> raise Exit)
        cstrs pairs
  | _ ->
      raise Exit

soit subtype env ty1 ty2 =
  TypePairs.clear subtypes;
  univar_pairs := [];
  (* Build constraint set. *)
  soit cstrs = subtype_rec env [(ty1, ty2)] ty1 ty2 [] dans
  TypePairs.clear subtypes;
  (* Enforce constraints. *)
  fonction () ->
    List.iter
      (fonction (trace0, t1, t2, pairs) ->
         essaie unify_pairs (ref env) t1 t2 pairs avec Unify trace ->
           raise (Subtype (expand_trace env (List.rev trace0),
                           List.tl (List.tl trace))))
      (List.rev cstrs)

                              (*******************)
                              (*  Miscellaneous  *)
                              (*******************)

(* Utility for printing. The resulting type is not used in computation. *)
soit rec unalias_object ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tfield (s, k, t1, t2) ->
      newty2 ty.level (Tfield (s, k, t1, unalias_object t2))
  | Tvar _ | Tnil ->
      newty2 ty.level ty.desc
  | Tunivar _ ->
      ty
  | Tconstr _ ->
      newvar2 ty.level
  | _ ->
      affirme faux

soit unalias ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tvar _ | Tunivar _ ->
      ty
  | Tvariant row ->
      soit row = row_repr row dans
      soit more = row.row_more dans
      newty2 ty.level
        (Tvariant {row avec row_more = newty2 more.level more.desc})
  | Tobject (ty, nm) ->
      newty2 ty.level (Tobject (unalias_object ty, nm))
  | _ ->
      newty2 ty.level ty.desc

(* Return the arity (as for curried functions) of the given type. *)
soit rec arity ty =
  filtre (repr ty).desc avec
    Tarrow(_, t1, t2, _) -> 1 + arity t2
  | _ -> 0

(* Check whether an abbreviation expands to itself. *)
soit cyclic_abbrev env id ty =
  soit rec check_cycle seen ty =
    soit ty = repr ty dans
    filtre ty.desc avec
      Tconstr (p, tl, abbrev) ->
        p = Path.Pident id || List.memq ty seen ||
        début essaie
          check_cycle (ty :: seen) (expand_abbrev_opt env ty)
        avec
          Cannot_expand -> faux
        | Unify _ -> vrai
        fin
    | _ ->
        faux
  dans check_cycle [] ty

(* Normalize a type before printing, saving... *)
(* Cannot use mark_type because deep_occur uses it too *)
soit rec normalize_type_rec env visited ty =
  soit ty = repr ty dans
  si not (TypeSet.mem ty !visited) alors début
    visited := TypeSet.add ty !visited;
    début filtre ty.desc avec
    | Tvariant row ->
      soit row = row_repr row dans
      soit fields = List.map
          (fonc (l,f0) ->
            soit f = row_field_repr f0 dans l,
            filtre f avec Reither(b, ty::(_::_ tel tyl), m, e) ->
              soit tyl' =
                List.fold_left
                  (fonc tyl ty ->
                    si List.exists (fonc ty' -> equal env faux [ty] [ty']) tyl
                    alors tyl sinon ty::tyl)
                  [ty] tyl
              dans
              si f != f0 || List.length tyl' < List.length tyl alors
                Reither(b, List.rev tyl', m, e)
              sinon f
            | _ -> f)
          row.row_fields dans
      soit fields =
        List.sort (fonc (p,_) (q,_) -> compare p q)
          (List.filter (fonc (_,fi) -> fi <> Rabsent) fields) dans
      log_type ty;
      ty.desc <- Tvariant {row avec row_fields = fields}
    | Tobject (fi, nm) ->
        début filtre !nm avec
        | None -> ()
        | Some (n, v :: l) ->
            si deep_occur ty (newgenty (Ttuple l)) alors
              (* The abbreviation may be hiding something, so remove it *)
              set_name nm None
            sinon soit v' = repr v dans
            début filtre v'.desc avec
            | Tvar _ | Tunivar _ ->
                si v' != v alors set_name nm (Some (n, v' :: l))
            | Tnil ->
                log_type ty; ty.desc <- Tconstr (n, l, ref Mnil)
            | _ -> set_name nm None
            fin
        | _ ->
            fatal_error "Ctype.normalize_type_rec"
        fin;
        soit fi = repr fi dans
        si fi.level < lowest_level alors () sinon
        soit fields, row = flatten_fields fi dans
        soit fi' = build_fields fi.level fields row dans
        log_type ty; fi.desc <- fi'.desc
    | _ -> ()
    fin;
    iter_type_expr (normalize_type_rec env visited) ty
  fin

soit normalize_type env ty =
  normalize_type_rec env (ref TypeSet.empty) ty


                              (*************************)
                              (*  Remove dependencies  *)
                              (*************************)


(*
   Variables are left unchanged. Other type nodes are duplicated, with
   levels set to generic level.
   We cannot use Tsubst here, because unification may be called by
   expand_abbrev.
*)

soit nondep_hash     = TypeHash.create 47
soit nondep_variants = TypeHash.create 17
soit clear_hash ()   =
  TypeHash.clear nondep_hash; TypeHash.clear nondep_variants

soit rec nondep_type_rec env id ty =
  filtre ty.desc avec
    Tvar _ | Tunivar _ -> ty
  | Tlink ty -> nondep_type_rec env id ty
  | _ -> essaie TypeHash.find nondep_hash ty
  avec Not_found ->
    soit ty' = newgenvar () dans        (* Stub *)
    TypeHash.add nondep_hash ty ty';
    ty'.desc <-
      début filtre ty.desc avec
      | Tconstr(p, tl, abbrev) ->
          si Path.isfree id p alors
            début essaie
              Tlink (nondep_type_rec env id
                       (expand_abbrev env (newty2 ty.level ty.desc)))
              (*
                 The [Tlink] is important. The expanded type may be a
                 variable, or may not be completely copied yet
                 (recursive type), so one cannot just take its
                 description.
               *)
            avec Cannot_expand | Unify _ ->
              raise Not_found
            fin
          sinon
            Tconstr(p, List.map (nondep_type_rec env id) tl, ref Mnil)
      | Tpackage(p, nl, tl) quand Path.isfree id p ->
          soit p' = normalize_package_path env p dans
          si Path.isfree id p' alors raise Not_found;
          Tpackage (p', nl, List.map (nondep_type_rec env id) tl)
      | Tobject (t1, name) ->
          Tobject (nondep_type_rec env id t1,
                 ref (filtre !name avec
                        None -> None
                      | Some (p, tl) ->
                          si Path.isfree id p alors None
                          sinon Some (p, List.map (nondep_type_rec env id) tl)))
      | Tvariant row ->
          soit row = row_repr row dans
          soit more = repr row.row_more dans
          (* We must keep sharing according to the row variable *)
          début essaie
            soit ty2 = TypeHash.find nondep_variants more dans
            (* This variant type has been already copied *)
            TypeHash.add nondep_hash ty ty2;
            Tlink ty2
          avec Not_found ->
            (* Register new type first for recursion *)
            TypeHash.add nondep_variants more ty';
            soit static = static_row row dans
            soit more' = si static alors newgenty Tnil sinon more dans
            (* Return a new copy *)
            soit row =
              copy_row (nondep_type_rec env id) vrai row vrai more' dans
            filtre row.row_name avec
              Some (p, tl) quand Path.isfree id p ->
                Tvariant {row avec row_name = None}
            | _ -> Tvariant row
          fin
      | _ -> copy_type_desc (nondep_type_rec env id) ty.desc
      fin;
    ty'

soit nondep_type env id ty =
  essaie
    soit ty' = nondep_type_rec env id ty dans
    clear_hash ();
    ty'
  avec Not_found ->
    clear_hash ();
    raise Not_found

soit () = nondep_type' := nondep_type

soit unroll_abbrev id tl ty =
  soit ty = repr ty et path = Path.Pident id dans
  si is_Tvar ty || (List.exists (deep_occur ty) tl)
  || is_object_type path alors
    ty
  sinon
    soit ty' = newty2 ty.level ty.desc dans
    link_type ty (newty2 ty.level (Tconstr (path, tl, ref Mnil)));
    ty'

(* Preserve sharing inside type declarations. *)
soit nondep_type_decl env mid id is_covariant decl =
  essaie
    soit params = List.map (nondep_type_rec env mid) decl.type_params dans
    soit tk =
      essaie filtre decl.type_kind avec
        Type_abstract ->
          Type_abstract
      | Type_variant cstrs ->
          Type_variant
            (List.map
               (fonc c ->
                 {c avec
                  cd_args = List.map (nondep_type_rec env mid) c.cd_args;
                  cd_res = may_map (nondep_type_rec env mid) c.cd_res;
                 }
               )
               cstrs)
      | Type_record(lbls, rep) ->
          Type_record
            (List.map
               (fonc l ->
                  {l avec ld_type = nondep_type_rec env mid l.ld_type}
               )
               lbls,
             rep)
      avec Not_found quand is_covariant -> Type_abstract
    et tm =
      essaie filtre decl.type_manifest avec
        None -> None
      | Some ty ->
          Some (unroll_abbrev id params (nondep_type_rec env mid ty))
      avec Not_found quand is_covariant ->
        None
    dans
    clear_hash ();
    soit priv =
      filtre tm avec
      | Some ty quand Btype.has_constr_row ty -> Private
      | _ -> decl.type_private
    dans
    { type_params = params;
      type_arity = decl.type_arity;
      type_kind = tk;
      type_manifest = tm;
      type_private = priv;
      type_variance = decl.type_variance;
      type_newtype_level = None;
      type_loc = decl.type_loc;
      type_attributes = decl.type_attributes;
    }
  avec Not_found ->
    clear_hash ();
    raise Not_found

(* Preserve sharing inside class types. *)
soit nondep_class_signature env id sign =
  { csig_self = nondep_type_rec env id sign.csig_self;
    csig_vars =
      Vars.map (fonction (m, v, t) -> (m, v, nondep_type_rec env id t))
        sign.csig_vars;
    csig_concr = sign.csig_concr;
    csig_inher =
      List.map (fonc (p,tl) -> (p, List.map (nondep_type_rec env id) tl))
        sign.csig_inher }

soit rec nondep_class_type env id =
  fonction
    Cty_constr (p, _, cty) quand Path.isfree id p ->
      nondep_class_type env id cty
  | Cty_constr (p, tyl, cty) ->
      Cty_constr (p, List.map (nondep_type_rec env id) tyl,
                   nondep_class_type env id cty)
  | Cty_signature sign ->
      Cty_signature (nondep_class_signature env id sign)
  | Cty_arrow (l, ty, cty) ->
      Cty_arrow (l, nondep_type_rec env id ty, nondep_class_type env id cty)

soit nondep_class_declaration env id decl =
  affirme (not (Path.isfree id decl.cty_path));
  soit decl =
    { cty_params = List.map (nondep_type_rec env id) decl.cty_params;
      cty_variance = decl.cty_variance;
      cty_type = nondep_class_type env id decl.cty_type;
      cty_path = decl.cty_path;
      cty_new =
        début filtre decl.cty_new avec
          None    -> None
        | Some ty -> Some (nondep_type_rec env id ty)
        fin;
      cty_loc = decl.cty_loc;
      cty_attributes = decl.cty_attributes;
    }
  dans
  clear_hash ();
  decl

soit nondep_cltype_declaration env id decl =
  affirme (not (Path.isfree id decl.clty_path));
  soit decl =
    { clty_params = List.map (nondep_type_rec env id) decl.clty_params;
      clty_variance = decl.clty_variance;
      clty_type = nondep_class_type env id decl.clty_type;
      clty_path = decl.clty_path;
      clty_loc = decl.clty_loc;
      clty_attributes = decl.clty_attributes;
    }
  dans
  clear_hash ();
  decl

(* collapse conjonctive types in class parameters *)
soit rec collapse_conj env visited ty =
  soit ty = repr ty dans
  si List.memq ty visited alors () sinon
  soit visited = ty :: visited dans
  filtre ty.desc avec
    Tvariant row ->
      soit row = row_repr row dans
      List.iter
        (fonc (l,fi) ->
          filtre row_field_repr fi avec
            Reither (c, t1::(_::_ tel tl), m, e) ->
              List.iter (unify env t1) tl;
              set_row_field e (Reither (c, [t1], m, ref None))
          | _ ->
              ())
        row.row_fields;
      iter_row (collapse_conj env visited) row
  | _ ->
      iter_type_expr (collapse_conj env visited) ty

soit collapse_conj_params env params =
  List.iter (collapse_conj env []) params
