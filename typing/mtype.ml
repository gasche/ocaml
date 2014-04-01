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

(* Operations on module types *)

ouvre Asttypes
ouvre Path
ouvre Types


soit rec scrape env mty =
  filtre mty avec
    Mty_ident p ->
      début essaie
        scrape env (Env.find_modtype_expansion p env)
      avec Not_found ->
        mty
      fin
  | _ -> mty

soit freshen mty =
  Subst.modtype Subst.identity mty

soit rec strengthen env mty p =
  filtre scrape env mty avec
    Mty_signature sg ->
      Mty_signature(strengthen_sig env sg p)
  | Mty_functor(param, arg, res)
    quand !Clflags.applicative_functors && Ident.name param <> "*" ->
      Mty_functor(param, arg, strengthen env res (Papply(p, Pident param)))
  | mty ->
      mty

et strengthen_sig env sg p =
  filtre sg avec
    [] -> []
  | (Sig_value(id, desc) tel sigelt) :: rem ->
      sigelt :: strengthen_sig env rem p
  | Sig_type(id, decl, rs) :: rem ->
      soit newdecl =
        filtre decl.type_manifest, decl.type_private, decl.type_kind avec
          Some _, Public, _ -> decl
        | Some _, Private, (Type_record _ | Type_variant _) -> decl
        | _ ->
            soit manif =
              Some(Btype.newgenty(Tconstr(Pdot(p, Ident.name id, nopos),
                                          decl.type_params, ref Mnil))) dans
            si decl.type_kind = Type_abstract alors
              { decl avec type_private = Public; type_manifest = manif }
            sinon
              { decl avec type_manifest = manif }
      dans
      Sig_type(id, newdecl, rs) :: strengthen_sig env rem p
  | (Sig_exception(id, d) tel sigelt) :: rem ->
      sigelt :: strengthen_sig env rem p
  | Sig_module(id, md, rs) :: rem ->
      soit str = strengthen_decl env md (Pdot(p, Ident.name id, nopos)) dans
      Sig_module(id, str, rs)
      :: strengthen_sig (Env.add_module_declaration id md env) rem p
      (* Need to add the module in case it defines manifest module types *)
  | Sig_modtype(id, decl) :: rem ->
      soit newdecl =
        filtre decl.mtd_type avec
          None ->
            {decl avec mtd_type = Some(Mty_ident(Pdot(p, Ident.name id, nopos)))}
        | Some _ ->
            decl
      dans
      Sig_modtype(id, newdecl) ::
      strengthen_sig (Env.add_modtype id decl env) rem p
      (* Need to add the module type in case it is manifest *)
  | (Sig_class(id, decl, rs) tel sigelt) :: rem ->
      sigelt :: strengthen_sig env rem p
  | (Sig_class_type(id, decl, rs) tel sigelt) :: rem ->
      sigelt :: strengthen_sig env rem p

et strengthen_decl env md p =
  {md avec md_type = strengthen env md.md_type p}

soit () = Env.strengthen := strengthen

(* In nondep_supertype, env is only used for the type it assigns to id.
   Hence there is no need to keep env up-to-date by adding the bindings
   traversed. *)

type variance = Co | Contra | Strict

soit nondep_supertype env mid mty =

  soit rec nondep_mty env va mty =
    filtre mty avec
      Mty_ident p ->
        si Path.isfree mid p alors
          nondep_mty env va (Env.find_modtype_expansion p env)
        sinon mty
    | Mty_alias p ->
        si Path.isfree mid p alors
          nondep_mty env va (Env.find_module p env).md_type
        sinon mty
    | Mty_signature sg ->
        Mty_signature(nondep_sig env va sg)
    | Mty_functor(param, arg, res) ->
        soit var_inv =
          filtre va avec Co -> Contra | Contra -> Co | Strict -> Strict dans
        Mty_functor(param, Misc.may_map (nondep_mty env var_inv) arg,
                    nondep_mty
                      (Env.add_module ~arg:vrai param
                         (Btype.default_mty arg) env) va res)

  et nondep_sig env va = fonction
    [] -> []
  | item :: rem ->
      soit rem' = nondep_sig env va rem dans
      filtre item avec
        Sig_value(id, d) ->
          Sig_value(id,
                    {d avec val_type = Ctype.nondep_type env mid d.val_type})
          :: rem'
      | Sig_type(id, d, rs) ->
          Sig_type(id, Ctype.nondep_type_decl env mid id (va = Co) d, rs)
          :: rem'
      | Sig_exception(id, d) ->
          soit d =
            {d avec
             exn_args = List.map (Ctype.nondep_type env mid) d.exn_args
            }
          dans
          Sig_exception(id, d) :: rem'
      | Sig_module(id, md, rs) ->
          Sig_module(id, {md avec md_type=nondep_mty env va md.md_type}, rs)
          :: rem'
      | Sig_modtype(id, d) ->
          début essaie
            Sig_modtype(id, nondep_modtype_decl env d) :: rem'
          avec Not_found ->
            filtre va avec
              Co -> Sig_modtype(id, {mtd_type=None; mtd_loc=Location.none;
                                     mtd_attributes=[]}) :: rem'
            | _  -> raise Not_found
          fin
      | Sig_class(id, d, rs) ->
          Sig_class(id, Ctype.nondep_class_declaration env mid d, rs)
          :: rem'
      | Sig_class_type(id, d, rs) ->
          Sig_class_type(id, Ctype.nondep_cltype_declaration env mid d, rs)
          :: rem'

  et nondep_modtype_decl env mtd =
    {mtd avec mtd_type = Misc.may_map (nondep_mty env Strict) mtd.mtd_type}

  dans
    nondep_mty env Co mty

soit enrich_typedecl env p decl =
  filtre decl.type_manifest avec
    Some ty -> decl
  | None ->
      essaie
        soit orig_decl = Env.find_type p env dans
        si orig_decl.type_arity <> decl.type_arity
        alors decl
        sinon {decl avec type_manifest =
                Some(Btype.newgenty(Tconstr(p, decl.type_params, ref Mnil)))}
      avec Not_found ->
        decl

soit rec enrich_modtype env p mty =
  filtre mty avec
    Mty_signature sg ->
      Mty_signature(List.map (enrich_item env p) sg)
  | _ ->
      mty

et enrich_item env p = fonction
    Sig_type(id, decl, rs) ->
      Sig_type(id,
                enrich_typedecl env (Pdot(p, Ident.name id, nopos)) decl, rs)
  | Sig_module(id, md, rs) ->
      Sig_module(id,
                  {md avec
                   md_type = enrich_modtype env
                       (Pdot(p, Ident.name id, nopos)) md.md_type},
                 rs)
  | item -> item

soit rec type_paths env p mty =
  filtre scrape env mty avec
    Mty_ident p -> []
  | Mty_alias p -> []
  | Mty_signature sg -> type_paths_sig env p 0 sg
  | Mty_functor(param, arg, res) -> []

et type_paths_sig env p pos sg =
  filtre sg avec
    [] -> []
  | Sig_value(id, decl) :: rem ->
      soit pos' = filtre decl.val_kind avec Val_prim _ -> pos | _ -> pos + 1 dans
      type_paths_sig env p pos' rem
  | Sig_type(id, decl, _) :: rem ->
      Pdot(p, Ident.name id, nopos) :: type_paths_sig env p pos rem
  | Sig_module(id, md, _) :: rem ->
      type_paths env (Pdot(p, Ident.name id, pos)) md.md_type @
      type_paths_sig (Env.add_module_declaration id md env) p (pos+1) rem
  | Sig_modtype(id, decl) :: rem ->
      type_paths_sig (Env.add_modtype id decl env) p pos rem
  | (Sig_exception _ | Sig_class _) :: rem ->
      type_paths_sig env p (pos+1) rem
  | (Sig_class_type _) :: rem ->
      type_paths_sig env p pos rem

soit rec no_code_needed env mty =
  filtre scrape env mty avec
    Mty_ident p -> faux
  | Mty_signature sg -> no_code_needed_sig env sg
  | Mty_functor(_, _, _) -> faux
  | Mty_alias p -> vrai

et no_code_needed_sig env sg =
  filtre sg avec
    [] -> vrai
  | Sig_value(id, decl) :: rem ->
      début filtre decl.val_kind avec
      | Val_prim _ -> no_code_needed_sig env rem
      | _ -> faux
      fin
  | Sig_module(id, md, _) :: rem ->
      no_code_needed env md.md_type &&
      no_code_needed_sig (Env.add_module_declaration id md env) rem
  | (Sig_type _ | Sig_modtype _ | Sig_class_type _) :: rem ->
      no_code_needed_sig env rem
  | (Sig_exception _ | Sig_class _) :: rem ->
      faux


(* Check whether a module type may return types *)

soit rec contains_type env = fonction
    Mty_ident path ->
      (essaie Misc.may (contains_type env) (Env.find_modtype path env).mtd_type
       avec Not_found -> raise Exit)
  | Mty_signature sg ->
      contains_type_sig env sg
  | Mty_functor (_, _, body) ->
      contains_type env body
  | Mty_alias _ ->
      ()

et contains_type_sig env = List.iter (contains_type_item env)

et contains_type_item env = fonction
    Sig_type (_,({type_manifest = None} |
                 {type_kind = Type_abstract; type_private = Private}),_)
  | Sig_modtype _ ->
      raise Exit
  | Sig_module (_, {md_type = mty}, _) ->
      contains_type env mty
  | Sig_value _
  | Sig_type _
  | Sig_exception _
  | Sig_class _
  | Sig_class_type _ ->
      ()

soit contains_type env mty =
  essaie contains_type env mty; faux avec Exit -> vrai


(* Remove module aliases from a signature *)

module P = struct
  type t = Path.t
  soit compare p1 p2 =
    si Path.same p1 p2 alors 0 sinon compare p1 p2
fin
module PathSet = Set.Make (P)
module PathMap = Map.Make (P)
module IdentSet = Set.Make (struct type t = Ident.t soit compare = compare fin)

soit rec get_prefixes = fonction
    Pident _ -> PathSet.empty
  | Pdot (p, _, _)
  | Papply (p, _) -> PathSet.add p (get_prefixes p)

soit rec get_arg_paths = fonction
    Pident _ -> PathSet.empty
  | Pdot (p, _, _) -> get_arg_paths p
  | Papply (p1, p2) ->
      PathSet.add p2
        (PathSet.union (get_prefixes p2)
           (PathSet.union (get_arg_paths p1) (get_arg_paths p2)))

soit rec rollback_path subst p =
  essaie Pident (PathMap.find p subst)
  avec Not_found ->
    filtre p avec
      Pident _ | Papply _ -> p
    | Pdot (p1, s, n) ->
        soit p1' = rollback_path subst p1 dans
        si Path.same p1 p1' alors p sinon rollback_path subst (Pdot (p1', s, n))

soit rec collect_ids subst bindings p =
    début filtre rollback_path subst p avec
      Pident id ->
        soit ids =
          essaie collect_ids subst bindings (Ident.find_same id bindings)
          avec Not_found -> IdentSet.empty
        dans
        IdentSet.add id ids
    | _ -> IdentSet.empty
    fin

soit collect_arg_paths mty =
  soit ouvre Btype dans
  soit paths = ref PathSet.empty
  et subst = ref PathMap.empty
  et bindings = ref Ident.empty dans
  (* let rt = Ident.create "Root" in
     and prefix = ref (Path.Pident rt) in *)
  soit it_path p = paths := PathSet.union (get_arg_paths p) !paths
  et it_signature_item it sign =
    type_iterators.it_signature_item it sign;
    filtre sign avec
      Sig_module (id, {md_type=Mty_alias p}, _) ->
        bindings := Ident.add id p !bindings
    | Sig_module (id, {md_type=Mty_signature sg}, _) ->
        List.iter
          (fonction Sig_module (id', _, _) ->
              subst :=
                PathMap.add (Pdot (Pident id, Ident.name id', -1)) id' !subst
            | _ -> ())
          sg
    | _ -> ()
  dans
  soit it = {type_iterators avec it_path; it_signature_item} dans
  it.it_module_type it mty;
  PathSet.fold (fonc p -> IdentSet.union (collect_ids !subst !bindings p))
    !paths IdentSet.empty

soit rec remove_aliases env excl mty =
  filtre mty avec
    Mty_signature sg ->
      Mty_signature (remove_aliases_sig env excl sg)
  | Mty_alias _ ->
      remove_aliases env excl (Env.scrape_alias env mty)
  | mty ->
      mty

et remove_aliases_sig env excl sg =
  filtre sg avec
    [] -> []
  | Sig_module(id, md, rs) :: rem  ->
      soit mty =
        filtre md.md_type avec
          Mty_alias _ quand IdentSet.mem id excl ->
            md.md_type
        | mty ->
            remove_aliases env excl mty
      dans
      Sig_module(id, {md avec md_type = mty} , rs) ::
      remove_aliases_sig (Env.add_module id mty env) excl rem
  | Sig_modtype(id, mtd) :: rem ->
      Sig_modtype(id, mtd) ::
      remove_aliases_sig (Env.add_modtype id mtd env) excl rem
  | it :: rem ->
      it :: remove_aliases_sig env excl rem

soit remove_aliases env sg =
  soit excl = collect_arg_paths sg dans
  (* PathSet.iter (fun p -> Format.eprintf "%a@ " Printtyp.path p) excl;
  Format.eprintf "@."; *)
  remove_aliases env excl sg
