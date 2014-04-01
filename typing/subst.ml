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

(* Substitutions *)

ouvre Misc
ouvre Path
ouvre Types
ouvre Btype

type t =
  { types: (Ident.t, Path.t) Tbl.t;
    modules: (Ident.t, Path.t) Tbl.t;
    modtypes: (Ident.t, module_type) Tbl.t;
    for_saving: bool }

soit identity =
  { types = Tbl.empty; modules = Tbl.empty; modtypes = Tbl.empty;
    for_saving = faux }

soit add_type id p s = { s avec types = Tbl.add id p s.types }

soit add_module id p s = { s avec modules = Tbl.add id p s.modules }

soit add_modtype id ty s = { s avec modtypes = Tbl.add id ty s.modtypes }

soit for_saving s = { s avec for_saving = vrai }

soit loc s x =
  si s.for_saving && not !Clflags.keep_locs alors Location.none sinon x

soit remove_loc =
  soit ouvre Ast_mapper dans
  {default_mapper avec location = (fonc _this _loc -> Location.none)}

soit attrs s x =
  si s.for_saving && not !Clflags.keep_locs
  alors remove_loc.Ast_mapper.attributes remove_loc x
  sinon x


soit rec module_path s = fonction
    Pident id tel p ->
      début essaie Tbl.find id s.modules avec Not_found -> p fin
  | Pdot(p, n, pos) ->
      Pdot(module_path s p, n, pos)
  | Papply(p1, p2) ->
      Papply(module_path s p1, module_path s p2)

soit modtype_path s = fonction
    Pident id tel p ->
      début essaie
        filtre Tbl.find id s.modtypes avec
          | Mty_ident p -> p
          | _ -> fatal_error "Subst.modtype_path"
      avec Not_found -> p fin
  | Pdot(p, n, pos) ->
      Pdot(module_path s p, n, pos)
  | Papply(p1, p2) ->
      fatal_error "Subst.modtype_path"

soit type_path s = fonction
    Pident id tel p ->
      début essaie Tbl.find id s.types avec Not_found -> p fin
  | Pdot(p, n, pos) ->
      Pdot(module_path s p, n, pos)
  | Papply(p1, p2) ->
      fatal_error "Subst.type_path"

(* Special type ids for saved signatures *)

soit new_id = ref (-1)
soit reset_for_saving () = new_id := -1

soit newpersty desc =
  decr new_id;
  { desc = desc; level = generic_level; id = !new_id }

(* ensure that all occurrences of 'Tvar None' are physically shared *)
soit tvar_none = Tvar None
soit tunivar_none = Tunivar None
soit norm = fonction
  | Tvar None -> tvar_none
  | Tunivar None -> tunivar_none
  | d -> d

(* Similar to [Ctype.nondep_type_rec]. *)
soit rec typexp s ty =
  soit ty = repr ty dans
  filtre ty.desc avec
    Tvar _ | Tunivar _ tel desc ->
      si s.for_saving || ty.id < 0 alors
        soit ty' =
          si s.for_saving alors newpersty (norm desc)
          sinon newty2 ty.level desc
        dans
        save_desc ty desc; ty.desc <- Tsubst ty'; ty'
      sinon ty
  | Tsubst ty ->
      ty
(* cannot do it, since it would omit subsitution
  | Tvariant row when not (static_row row) ->
      ty
*)
  | _ ->
    soit desc = ty.desc dans
    save_desc ty desc;
    (* Make a stub *)
    soit ty' = si s.for_saving alors newpersty (Tvar None) sinon newgenvar () dans
    ty.desc <- Tsubst ty';
    ty'.desc <-
      début filtre desc avec
      | Tconstr(p, tl, abbrev) ->
          Tconstr(type_path s p, List.map (typexp s) tl, ref Mnil)
      | Tpackage(p, n, tl) ->
          Tpackage(modtype_path s p, n, List.map (typexp s) tl)
      | Tobject (t1, name) ->
          Tobject (typexp s t1,
                 ref (filtre !name avec
                        None -> None
                      | Some (p, tl) ->
                          Some (type_path s p, List.map (typexp s) tl)))
      | Tfield (m, k, t1, t2)
        quand s == identity && ty.level < generic_level && m = dummy_method ->
          (* not allowed to lower the level of the dummy method *)
          Tfield (m, k, t1, typexp s t2)
      | Tvariant row ->
          soit row = row_repr row dans
          soit more = repr row.row_more dans
          (* We must substitute in a subtle way *)
          (* Tsubst takes a tuple containing the row var and the variant *)
          début filtre more.desc avec
            Tsubst {desc = Ttuple [_;ty2]} ->
              (* This variant type has been already copied *)
              ty.desc <- Tsubst ty2; (* avoid Tlink in the new type *)
              Tlink ty2
          | _ ->
              soit dup =
                s.for_saving || more.level = generic_level || static_row row ||
                filtre more.desc avec Tconstr _ -> vrai | _ -> faux dans
              (* Various cases for the row variable *)
              soit more' =
                filtre more.desc avec
                  Tsubst ty -> ty
                | Tconstr _ | Tnil -> typexp s more
                | Tunivar _ | Tvar _ ->
                    save_desc more more.desc;
                    si s.for_saving alors newpersty (norm more.desc) sinon
                    si dup && is_Tvar more alors newgenty more.desc sinon more
                | _ -> affirme faux
              dans
              (* Register new type first for recursion *)
              more.desc <- Tsubst(newgenty(Ttuple[more';ty']));
              (* Return a new copy *)
              soit row =
                copy_row (typexp s) vrai row (not dup) more' dans
              filtre row.row_name avec
                Some (p, tl) ->
                  Tvariant {row avec row_name = Some (type_path s p, tl)}
              | None ->
                  Tvariant row
          fin
      | Tfield(label, kind, t1, t2) quand field_kind_repr kind = Fabsent ->
          Tlink (typexp s t2)
      | _ -> copy_type_desc (typexp s) desc
      fin;
    ty'

(*
   Always make a copy of the type. If this is not done, type levels
   might not be correct.
*)
soit type_expr s ty =
  soit ty' = typexp s ty dans
  cleanup_types ();
  ty'

soit type_declaration s decl =
  soit decl =
    { type_params = List.map (typexp s) decl.type_params;
      type_arity = decl.type_arity;
      type_kind =
        début filtre decl.type_kind avec
          Type_abstract -> Type_abstract
        | Type_variant cstrs ->
            Type_variant
              (List.map
                 (fonc c ->
                    {
                      cd_id = c.cd_id;
                      cd_args = List.map (typexp s) c.cd_args;
                      cd_res = may_map (typexp s) c.cd_res;
                      cd_loc = loc s c.cd_loc;
                      cd_attributes = attrs s c.cd_attributes;
                    }
                 )
                 cstrs)
        | Type_record(lbls, rep) ->
            Type_record
              (List.map (fonc l ->
                   {
                     ld_id = l.ld_id;
                     ld_mutable = l.ld_mutable;
                     ld_type = typexp s l.ld_type;
                     ld_loc = loc s l.ld_loc;
                     ld_attributes = attrs s l.ld_attributes;
                   }
                 )
                  lbls,
               rep)
        fin;
      type_manifest =
        début
          filtre decl.type_manifest avec
            None -> None
          | Some ty -> Some(typexp s ty)
        fin;
      type_private = decl.type_private;
      type_variance = decl.type_variance;
      type_newtype_level = None;
      type_loc = loc s decl.type_loc;
      type_attributes = attrs s decl.type_attributes;
    }
  dans
  cleanup_types ();
  decl

soit class_signature s sign =
  { csig_self = typexp s sign.csig_self;
    csig_vars =
      Vars.map (fonction (m, v, t) -> (m, v, typexp s t)) sign.csig_vars;
    csig_concr = sign.csig_concr;
    csig_inher =
      List.map (fonc (p, tl) -> (type_path s p, List.map (typexp s) tl))
        sign.csig_inher;
  }

soit rec class_type s =
  fonction
    Cty_constr (p, tyl, cty) ->
      Cty_constr (type_path s p, List.map (typexp s) tyl, class_type s cty)
  | Cty_signature sign ->
      Cty_signature (class_signature s sign)
  | Cty_arrow (l, ty, cty) ->
      Cty_arrow (l, typexp s ty, class_type s cty)

soit class_declaration s decl =
  soit decl =
    { cty_params = List.map (typexp s) decl.cty_params;
      cty_variance = decl.cty_variance;
      cty_type = class_type s decl.cty_type;
      cty_path = type_path s decl.cty_path;
      cty_new =
        début filtre decl.cty_new avec
          None    -> None
        | Some ty -> Some (typexp s ty)
        fin;
      cty_loc = loc s decl.cty_loc;
      cty_attributes = attrs s decl.cty_attributes;
    }
  dans
  (* Do not clean up if saving: next is cltype_declaration *)
  si not s.for_saving alors cleanup_types ();
  decl

soit cltype_declaration s decl =
  soit decl =
    { clty_params = List.map (typexp s) decl.clty_params;
      clty_variance = decl.clty_variance;
      clty_type = class_type s decl.clty_type;
      clty_path = type_path s decl.clty_path;
      clty_loc = loc s decl.clty_loc;
      clty_attributes = attrs s decl.clty_attributes;
    }
  dans
  (* Do clean up even if saving: type_declaration may be recursive *)
  cleanup_types ();
  decl

soit class_type s cty =
  soit cty = class_type s cty dans
  cleanup_types ();
  cty

soit value_description s descr =
  { val_type = type_expr s descr.val_type;
    val_kind = descr.val_kind;
    val_loc = loc s descr.val_loc;
    val_attributes = attrs s descr.val_attributes;
   }

soit exception_declaration s descr =
  { exn_args = List.map (type_expr s) descr.exn_args;
    exn_loc = loc s descr.exn_loc;
    exn_attributes = attrs s descr.exn_attributes;
   }

soit rec rename_bound_idents s idents = fonction
    [] -> (List.rev idents, s)
  | Sig_type(id, d, _) :: sg ->
      soit id' = Ident.rename id dans
      rename_bound_idents (add_type id (Pident id') s) (id' :: idents) sg
  | Sig_module(id, mty, _) :: sg ->
      soit id' = Ident.rename id dans
      rename_bound_idents (add_module id (Pident id') s) (id' :: idents) sg
  | Sig_modtype(id, d) :: sg ->
      soit id' = Ident.rename id dans
      rename_bound_idents (add_modtype id (Mty_ident(Pident id')) s)
                          (id' :: idents) sg
  | (Sig_value(id, _) | Sig_exception(id, _) |
     Sig_class(id, _, _) | Sig_class_type(id, _, _)) :: sg ->
      soit id' = Ident.rename id dans
      rename_bound_idents s (id' :: idents) sg

soit rec modtype s = fonction
    Mty_ident p tel mty ->
      début filtre p avec
        Pident id ->
          début essaie Tbl.find id s.modtypes avec Not_found -> mty fin
      | Pdot(p, n, pos) ->
          Mty_ident(Pdot(module_path s p, n, pos))
      | Papply(p1, p2) ->
          fatal_error "Subst.modtype"
      fin
  | Mty_signature sg ->
      Mty_signature(signature s sg)
  | Mty_functor(id, arg, res) ->
      soit id' = Ident.rename id dans
      Mty_functor(id', may_map (modtype s) arg,
                       modtype (add_module id (Pident id') s) res)
  | Mty_alias p ->
      Mty_alias(module_path s p)

et signature s sg =
  (* Components of signature may be mutually recursive (e.g. type declarations
     or class and type declarations), so first build global renaming
     substitution... *)
  soit (new_idents, s') = rename_bound_idents s [] sg dans
  (* ... then apply it to each signature component in turn *)
  List.map2 (signature_component s') sg new_idents

et signature_component s comp newid =
  filtre comp avec
    Sig_value(id, d) ->
      Sig_value(newid, value_description s d)
  | Sig_type(id, d, rs) ->
      Sig_type(newid, type_declaration s d, rs)
  | Sig_exception(id, d) ->
      Sig_exception(newid, exception_declaration s d)
  | Sig_module(id, d, rs) ->
      Sig_module(newid, module_declaration s d, rs)
  | Sig_modtype(id, d) ->
      Sig_modtype(newid, modtype_declaration s d)
  | Sig_class(id, d, rs) ->
      Sig_class(newid, class_declaration s d, rs)
  | Sig_class_type(id, d, rs) ->
      Sig_class_type(newid, cltype_declaration s d, rs)

et module_declaration s decl =
  {
    md_type = modtype s decl.md_type;
    md_attributes = attrs s decl.md_attributes;
    md_loc = loc s decl.md_loc;
  }

et modtype_declaration s decl  =
  {
    mtd_type = may_map (modtype s) decl.mtd_type;
    mtd_attributes = attrs s decl.mtd_attributes;
    mtd_loc = loc s decl.mtd_loc;
  }

(* For every binding k |-> d of m1, add k |-> f d to m2
   and return resulting merged map. *)

soit merge_tbls f m1 m2 =
  Tbl.fold (fonc k d accu -> Tbl.add k (f d) accu) m1 m2

(* Composition of substitutions:
     apply (compose s1 s2) x = apply s2 (apply s1 x) *)

soit compose s1 s2 =
  { types = merge_tbls (type_path s2) s1.types s2.types;
    modules = merge_tbls (module_path s2) s1.modules s2.modules;
    modtypes = merge_tbls (modtype s2) s1.modtypes s2.modtypes;
    for_saving = faux }
