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
ouvre Longident
ouvre Path
ouvre Asttypes
ouvre Parsetree
ouvre Types
ouvre Format

type error =
    Cannot_apply de module_type
  | Not_included de Includemod.error list
  | Cannot_eliminate_dependency de module_type
  | Signature_expected
  | Structure_expected de module_type
  | With_no_component de Longident.t
  | With_mismatch de Longident.t * Includemod.error list
  | Repeated_name de string * string
  | Non_generalizable de type_expr
  | Non_generalizable_class de Ident.t * class_declaration
  | Non_generalizable_module de module_type
  | Implementation_is_required de string
  | Interface_not_compiled de string
  | Not_allowed_in_functor_body
  | With_need_typeconstr
  | Not_a_packed_module de type_expr
  | Incomplete_packed_module de type_expr
  | Scoping_pack de Longident.t * type_expr
  | Extension de string
  | Recursive_module_require_explicit_type
  | Apply_generative

exception Error de Location.t * Env.t * error

ouvre Typedtree

soit fst3 (x,_,_) = x

soit rec path_concat head p =
  filtre p avec
    Pident tail -> Pdot (Pident head, Ident.name tail, 0)
  | Pdot (pre, s, pos) -> Pdot (path_concat head pre, s, pos)
  | Papply _ -> affirme faux

(* Extract a signature from a module type *)

soit extract_sig env loc mty =
  filtre Env.scrape_alias env mty avec
    Mty_signature sg -> sg
  | _ -> raise(Error(loc, env, Signature_expected))

soit extract_sig_open env loc mty =
  filtre Env.scrape_alias env mty avec
    Mty_signature sg -> sg
  | _ -> raise(Error(loc, env, Structure_expected mty))

(* Compute the environment after opening a module *)

soit type_open ?toplevel ovf env loc lid =
  soit path = Typetexp.find_module env loc lid.txt dans
  soit md = Env.find_module path env dans
  soit sg = extract_sig_open env loc md.md_type dans
  path, Env.open_signature ~loc ?toplevel ovf path sg env

(* Record a module type *)
soit rm node =
  Stypes.record (Stypes.Ti_mod node);
  node

(* Forward declaration, to be filled in by type_module_type_of *)
soit type_module_type_of_fwd :
    (Env.t -> Parsetree.module_expr ->
      Typedtree.module_expr * Types.module_type) ref
  = ref (fonc env m -> affirme faux)

(* Merge one "with" constraint in a signature *)

soit rec add_rec_types env = fonction
    Sig_type(id, decl, Trec_next) :: rem ->
      add_rec_types (Env.add_type ~check:vrai id decl env) rem
  | _ -> env

soit check_type_decl env loc id row_id newdecl decl rs rem =
  soit env = Env.add_type ~check:vrai id newdecl env dans
  soit env =
    filtre row_id avec
    | None -> env
    | Some id -> Env.add_type ~check:vrai id newdecl env
  dans
  soit env = si rs = Trec_not alors env sinon add_rec_types env rem dans
  Includemod.type_declarations env id newdecl decl;
  Typedecl.check_coherence env loc id newdecl

soit rec make_params n = fonction
    [] -> []
  | _ :: l -> ("a" ^ string_of_int n) :: make_params (n+1) l

soit make_next_first rs rem =
  si rs = Trec_first alors
    filtre rem avec
      Sig_type (id, decl, Trec_next) :: rem ->
        Sig_type (id, decl, Trec_first) :: rem
    | Sig_module (id, mty, Trec_next) :: rem ->
        Sig_module (id, mty, Trec_first) :: rem
    | _ -> rem
  sinon rem

soit sig_item desc typ env loc = {
  Typedtree.sig_desc = desc; sig_loc = loc; sig_env = env
}

soit make p n i =
  soit ouvre Variance dans
  set May_pos p (set May_neg n (set May_weak n (set Inj i null)))

soit merge_constraint initial_env loc sg constr =
  soit lid =
    filtre constr avec
    | Pwith_type (lid, _) | Pwith_module (lid, _) -> lid
    | Pwith_typesubst {ptype_name=s} | Pwith_modsubst (s, _) ->
        {loc = s.loc; txt=Lident s.txt}
  dans
  soit real_id = ref None dans
  soit rec merge env sg namelist row_id =
    filtre (sg, namelist, constr) avec
      ([], _, _) ->
        raise(Error(loc, env, With_no_component lid.txt))
    | (Sig_type(id, decl, rs) :: rem, [s],
       Pwith_type (_, ({ptype_kind = Ptype_abstract} tel sdecl)))
      quand Ident.name id = s && Typedecl.is_fixed_type sdecl ->
        soit decl_row =
          { type_params =
              List.map (fonc _ -> Btype.newgenvar()) sdecl.ptype_params;
            type_arity = List.length sdecl.ptype_params;
            type_kind = Type_abstract;
            type_private = Private;
            type_manifest = None;
            type_variance =
              List.map
                (fonc (_, v) ->
                   soit (c, n) =
                     filtre v avec
                     | Covariant -> vrai, faux
                     | Contravariant -> faux, vrai
                     | Invariant -> faux, faux
                   dans
                   make (not n) (not c) faux
                )
                sdecl.ptype_params;
            type_loc = sdecl.ptype_loc;
            type_newtype_level = None;
            type_attributes = [];
          }
        et id_row = Ident.create (s^"#row") dans
        soit initial_env =
          Env.add_type ~check:vrai id_row decl_row initial_env
        dans
        soit tdecl = Typedecl.transl_with_constraint
                        initial_env id (Some(Pident id_row)) decl sdecl dans
        soit newdecl = tdecl.typ_type dans
        check_type_decl env sdecl.ptype_loc id row_id newdecl decl rs rem;
        soit decl_row = {decl_row avec type_params = newdecl.type_params} dans
        soit rs' = si rs = Trec_first alors Trec_not sinon rs dans
        (Pident id, lid, Twith_type tdecl),
        Sig_type(id_row, decl_row, rs') :: Sig_type(id, newdecl, rs) :: rem
    | (Sig_type(id, decl, rs) :: rem , [s], Pwith_type (_, sdecl))
      quand Ident.name id = s ->
        soit tdecl =
          Typedecl.transl_with_constraint initial_env id None decl sdecl dans
        soit newdecl = tdecl.typ_type dans
        check_type_decl env sdecl.ptype_loc id row_id newdecl decl rs rem;
        (Pident id, lid, Twith_type tdecl), Sig_type(id, newdecl, rs) :: rem
    | (Sig_type(id, decl, rs) :: rem, [s], (Pwith_type _ | Pwith_typesubst _))
      quand Ident.name id = s ^ "#row" ->
        merge env rem namelist (Some id)
    | (Sig_type(id, decl, rs) :: rem, [s], Pwith_typesubst sdecl)
      quand Ident.name id = s ->
        (* Check as for a normal with constraint, but discard definition *)
        soit tdecl =
          Typedecl.transl_with_constraint initial_env id None decl sdecl dans
        soit newdecl = tdecl.typ_type dans
        check_type_decl env sdecl.ptype_loc id row_id newdecl decl rs rem;
        real_id := Some id;
        (Pident id, lid, Twith_typesubst tdecl),
        make_next_first rs rem
    | (Sig_module(id, md, rs) :: rem, [s], Pwith_module (_, lid))
      quand Ident.name id = s ->
        soit path = Typetexp.find_module initial_env loc lid.txt dans
        soit md' = Env.find_module path env dans
        soit newmd = Mtype.strengthen_decl env md' path dans
        ignore(Includemod.modtypes env newmd.md_type md.md_type);
        (Pident id, lid, Twith_module (path, lid)),
        Sig_module(id, newmd, rs) :: rem
    | (Sig_module(id, md, rs) :: rem, [s], Pwith_modsubst (_, lid))
      quand Ident.name id = s ->
        soit path = Typetexp.find_module initial_env loc lid.txt dans
        soit md' = Env.find_module path env dans
        soit newmd = Mtype.strengthen_decl env md' path dans
        ignore(Includemod.modtypes env newmd.md_type md.md_type);
        real_id := Some id;
        (Pident id, lid, Twith_modsubst (path, lid)),
        make_next_first rs rem
    | (Sig_module(id, md, rs) :: rem, s :: namelist, _)
      quand Ident.name id = s ->
        soit ((path, path_loc, tcstr), newsg) =
          merge env (extract_sig env loc md.md_type) namelist None dans
        (path_concat id path, lid, tcstr),
        Sig_module(id, {md avec md_type=Mty_signature newsg}, rs) :: rem
    | (item :: rem, _, _) ->
        soit (cstr, items) = merge (Env.add_item item env) rem namelist row_id
        dans
        cstr, item :: items
  dans
  essaie
    soit names = Longident.flatten lid.txt dans
    soit (tcstr, sg) = merge initial_env sg names None dans
    soit sg =
    filtre names, constr avec
      [s], Pwith_typesubst sdecl ->
        soit id =
          filtre !real_id avec None -> affirme faux | Some id -> id dans
        soit lid =
          essaie filtre sdecl.ptype_manifest avec
          | Some {ptyp_desc = Ptyp_constr (lid, stl)}
            quand List.length stl = List.length sdecl.ptype_params ->
              soit params =
                List.map
                  (fonction {ptyp_desc=Ptyp_var s} -> s | _ -> raise Exit)
                  stl dans
              List.iter2 (fonc x (ox, _) ->
                filtre ox avec
                    Some y quand x = y.txt -> ()
                  | _ -> raise Exit
              ) params sdecl.ptype_params;
              lid
          | _ -> raise Exit
          avec Exit ->
            raise(Error(sdecl.ptype_loc, initial_env, With_need_typeconstr))
        dans
        soit (path, _) =
          essaie Env.lookup_type lid.txt initial_env avec Not_found -> affirme faux
        dans
        soit sub = Subst.add_type id path Subst.identity dans
        Subst.signature sub sg
    | [s], Pwith_modsubst (_, lid) ->
        soit id =
          filtre !real_id avec None -> affirme faux | Some id -> id dans
        soit path = Typetexp.find_module initial_env loc lid.txt dans
        soit sub = Subst.add_module id path Subst.identity dans
        Subst.signature sub sg
    | _ ->
          sg
    dans
    (tcstr, sg)
  avec Includemod.Error explanation ->
    raise(Error(loc, initial_env, With_mismatch(lid.txt, explanation)))

(* Add recursion flags on declarations arising from a mutually recursive
   block. *)

soit map_rec fn decls rem =
  filtre decls avec
  | [] -> rem
  | d1 :: dl -> fn Trec_first d1 :: map_end (fn Trec_next) dl rem

soit map_rec' = map_rec
(*
let rec map_rec' fn decls rem =
  match decls with
  | (id,_ as d1) :: dl when Btype.is_row_name (Ident.name id) ->
      fn Trec_not d1 :: map_rec' fn dl rem
  | _ -> map_rec fn decls rem
*)

soit rec map_rec'' fn decls rem =
  filtre decls avec
  | d1 :: dl quand Btype.is_row_name (Ident.name d1.typ_id) ->
      fn Trec_not d1 :: map_rec'' fn dl rem
  | _ -> map_rec fn decls rem

(* Auxiliary for translating recursively-defined module types.
   Return a module type that approximates the shape of the given module
   type AST.  Retain only module, type, and module type
   components of signatures.  For types, retain only their arity,
   making them abstract otherwise. *)

soit rec approx_modtype env smty =
  filtre smty.pmty_desc avec
    Pmty_ident lid ->
      soit (path, info) = Typetexp.find_modtype env smty.pmty_loc lid.txt dans
      Mty_ident path
  | Pmty_alias lid ->
      soit path = Typetexp.find_module env smty.pmty_loc lid.txt dans
      Mty_alias path
  | Pmty_signature ssg ->
      Mty_signature(approx_sig env ssg)
  | Pmty_functor(param, sarg, sres) ->
      soit arg = may_map (approx_modtype env) sarg dans
      soit (id, newenv) =
        Env.enter_module ~arg:vrai param.txt (Btype.default_mty arg) env dans
      soit res = approx_modtype newenv sres dans
      Mty_functor(id, arg, res)
  | Pmty_with(sbody, constraints) ->
      approx_modtype env sbody
  | Pmty_typeof smod ->
      soit (_, mty) = !type_module_type_of_fwd env smod dans
      mty
  | Pmty_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))

et approx_module_declaration env pmd =
  {
    Types.md_type = approx_modtype env pmd.pmd_type;
    md_attributes = pmd.pmd_attributes;
    md_loc = pmd.pmd_loc;
  }

et approx_sig env ssg =
  filtre ssg avec
    [] -> []
  | item :: srem ->
      filtre item.psig_desc avec
      | Psig_type sdecls ->
          soit decls = Typedecl.approx_type_decl env sdecls dans
          soit rem = approx_sig env srem dans
          map_rec' (fonc rs (id, info) -> Sig_type(id, info, rs)) decls rem
      | Psig_module pmd ->
          soit md = approx_module_declaration env pmd dans
          soit (id, newenv) =
            Env.enter_module_declaration pmd.pmd_name.txt md env
          dans
          Sig_module(id, md, Trec_not) :: approx_sig newenv srem
      | Psig_recmodule sdecls ->
          soit decls =
            List.map
              (fonc pmd ->
                 (Ident.create pmd.pmd_name.txt,
                  approx_module_declaration env pmd)
              )
              sdecls
          dans
          soit newenv =
            List.fold_left
              (fonc env (id, md) -> Env.add_module_declaration id md env)
              env decls dans
          map_rec (fonc rs (id, md) -> Sig_module(id, md, rs)) decls
                  (approx_sig newenv srem)
      | Psig_modtype d ->
          soit info = approx_modtype_info env d dans
          soit (id, newenv) = Env.enter_modtype d.pmtd_name.txt info env dans
          Sig_modtype(id, info) :: approx_sig newenv srem
      | Psig_open (ovf, lid, _attrs) ->
          soit (path, mty) = type_open ovf env item.psig_loc lid dans
          approx_sig mty srem
      | Psig_include (smty, _attrs) ->
          soit mty = approx_modtype env smty dans
          soit sg = Subst.signature Subst.identity
                     (extract_sig env smty.pmty_loc mty) dans
          soit newenv = Env.add_signature sg env dans
          sg @ approx_sig newenv srem
      | Psig_class sdecls | Psig_class_type sdecls ->
          soit decls = Typeclass.approx_class_declarations env sdecls dans
          soit rem = approx_sig env srem dans
          List.flatten
            (map_rec
              (fonc rs (i1, _, d1, i2, d2, i3, d3, _) ->
                [Sig_class_type(i1, d1, rs);
                 Sig_type(i2, d2, rs);
                 Sig_type(i3, d3, rs)])
              decls [rem])
      | _ ->
          approx_sig env srem

et approx_modtype_info env sinfo =
  {
   mtd_type = may_map (approx_modtype env) sinfo.pmtd_type;
   mtd_attributes = sinfo.pmtd_attributes;
   mtd_loc = sinfo.pmtd_loc;
  }

(* Additional validity checks on type definitions arising from
   recursive modules *)

soit check_recmod_typedecls env sdecls decls =
  soit recmod_ids = List.map fst3 decls dans
  List.iter2
    (fonc pmd (id, _, mty) ->
       soit mty = mty.mty_type dans
      List.iter
        (fonc path ->
          Typedecl.check_recmod_typedecl env pmd.pmd_type.pmty_loc recmod_ids
                                         path (Env.find_type path env))
        (Mtype.type_paths env (Pident id) mty))
    sdecls decls

(* Auxiliaries for checking uniqueness of names in signatures and structures *)

module StringSet =
  Set.Make(struct type t = string soit compare (x:t) y = compare x y fin)

soit check cl loc set_ref name =
  si StringSet.mem name !set_ref
  alors raise(Error(loc, Env.empty, Repeated_name(cl, name)))
  sinon set_ref := StringSet.add name !set_ref

soit check_sig_item type_names module_names modtype_names loc = fonction
    Sig_type(id, _, _) ->
      check "type" loc type_names (Ident.name id)
  | Sig_module(id, _, _) ->
      check "module" loc module_names (Ident.name id)
  | Sig_modtype(id, _) ->
      check "module type" loc modtype_names (Ident.name id)
  | _ -> ()

soit rec remove_duplicates val_ids exn_ids  = fonction
    [] -> []
  | Sig_value (id, _) :: rem
    quand List.exists (Ident.equal id) val_ids ->
      remove_duplicates val_ids exn_ids rem
  | Sig_exception(id, _) :: rem
    quand List.exists (Ident.equal id) exn_ids ->
      remove_duplicates val_ids exn_ids rem
  | f :: rem -> f :: remove_duplicates val_ids exn_ids rem

soit rec get_values = fonction
    [] -> []
  | Sig_value (id, _) :: rem -> id :: get_values rem
  | f :: rem -> get_values rem

soit rec get_exceptions = fonction
    [] -> []
  | Sig_exception (id, _) :: rem -> id :: get_exceptions rem
  | f :: rem -> get_exceptions rem


(* Check and translate a module type expression *)

soit transl_modtype_longident loc env lid =
  soit (path, info) = Typetexp.find_modtype env loc lid dans
  path

soit transl_module_alias loc env lid =
  Typetexp.find_module env loc lid

soit mkmty desc typ env loc attrs =
  soit mty = {
    mty_desc = desc;
    mty_type = typ;
    mty_loc = loc;
    mty_env = env;
    mty_attributes = attrs;
    } dans
  Cmt_format.add_saved_type (Cmt_format.Partial_module_type mty);
  mty

soit mksig desc env loc =
  soit sg = { sig_desc = desc; sig_loc = loc; sig_env = env } dans
  Cmt_format.add_saved_type (Cmt_format.Partial_signature_item sg);
  sg

(* let signature sg = List.map (fun item -> item.sig_type) sg *)

soit rec transl_modtype env smty =
  soit loc = smty.pmty_loc dans
  filtre smty.pmty_desc avec
    Pmty_ident lid ->
      soit path = transl_modtype_longident loc env lid.txt dans
      mkmty (Tmty_ident (path, lid)) (Mty_ident path) env loc
        smty.pmty_attributes
  | Pmty_alias lid ->
      soit path = transl_module_alias loc env lid.txt dans
      mkmty (Tmty_alias (path, lid)) (Mty_alias path) env loc
        smty.pmty_attributes
  | Pmty_signature ssg ->
      soit sg = transl_signature env ssg dans
      mkmty (Tmty_signature sg) (Mty_signature sg.sig_type) env loc
        smty.pmty_attributes
  | Pmty_functor(param, sarg, sres) ->
      soit arg = Misc.may_map (transl_modtype env) sarg dans
      soit ty_arg = Misc.may_map (fonc m -> m.mty_type) arg dans
      soit (id, newenv) =
        Env.enter_module ~arg:vrai param.txt (Btype.default_mty ty_arg) env dans
      soit res = transl_modtype newenv sres dans
      mkmty (Tmty_functor (id, param, arg, res))
      (Mty_functor(id, ty_arg, res.mty_type)) env loc
        smty.pmty_attributes
  | Pmty_with(sbody, constraints) ->
      soit body = transl_modtype env sbody dans
      soit init_sg = extract_sig env sbody.pmty_loc body.mty_type dans
      soit (tcstrs, final_sg) =
        List.fold_left
          (fonc (tcstrs,sg) sdecl ->
            soit (tcstr, sg) = merge_constraint env smty.pmty_loc sg sdecl
            dans
            (tcstr :: tcstrs, sg)
        )
        ([],init_sg) constraints dans
      mkmty (Tmty_with ( body, tcstrs))
        (Mtype.freshen (Mty_signature final_sg)) env loc
        smty.pmty_attributes
  | Pmty_typeof smod ->
      soit tmty, mty = !type_module_type_of_fwd env smod dans
      mkmty (Tmty_typeof tmty) mty env loc smty.pmty_attributes
  | Pmty_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))


et transl_signature env sg =
  soit type_names = ref StringSet.empty
  et module_names = ref StringSet.empty
  et modtype_names = ref StringSet.empty dans
  soit rec transl_sig env sg =
    Ctype.init_def(Ident.current_time());
    filtre sg avec
      [] -> [], [], env
    | item :: srem ->
        soit loc = item.psig_loc dans
        filtre item.psig_desc avec
        | Psig_value sdesc ->
            soit (tdesc, newenv) =
              Typedecl.transl_value_decl env item.psig_loc sdesc dans
            soit (trem,rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_value tdesc) env loc :: trem,
            (si List.exists (Ident.equal tdesc.val_id) (get_values rem) alors rem
            sinon Sig_value(tdesc.val_id, tdesc.val_val) :: rem),
              final_env
        | Psig_type sdecls ->
            List.iter
              (fonc decl ->
                check "type" item.psig_loc type_names decl.ptype_name.txt)
              sdecls;
            soit (decls, newenv) = Typedecl.transl_type_decl env sdecls dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_type decls) env loc :: trem,
            map_rec'' (fonc rs td ->
                Sig_type(td.typ_id, td.typ_type, rs)) decls rem,
            final_env
        | Psig_exception sarg ->
            soit (arg, decl, newenv) = Typedecl.transl_exception env sarg dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            soit id = arg.cd_id dans
            mksig (Tsig_exception arg) env loc :: trem,
            (si List.exists (Ident.equal id) (get_exceptions rem) alors rem
             sinon Sig_exception(id, decl) :: rem),
            final_env
        | Psig_module pmd ->
            check "module" item.psig_loc module_names pmd.pmd_name.txt;
            soit tmty = transl_modtype env pmd.pmd_type dans
            soit md = {
              md_type=tmty.mty_type;
              md_attributes=pmd.pmd_attributes;
              md_loc=pmd.pmd_loc;
            }
            dans
            soit (id, newenv) =
              Env.enter_module_declaration pmd.pmd_name.txt md env dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_module {md_id=id; md_name=pmd.pmd_name; md_type=tmty;
                                md_loc=pmd.pmd_loc;
                                md_attributes=pmd.pmd_attributes})
              env loc :: trem,
            Sig_module(id, md, Trec_not) :: rem,
            final_env
        | Psig_recmodule sdecls ->
            List.iter
              (fonc pmd ->
                 check "module" item.psig_loc module_names pmd.pmd_name.txt)
              sdecls;
            soit (decls, newenv) =
              transl_recmodule_modtypes item.psig_loc env sdecls dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_recmodule decls) env loc :: trem,
            map_rec (fonc rs md ->
                soit d = {Types.md_type = md.md_type.mty_type;
                         md_attributes = md.md_attributes;
                         md_loc = md.md_loc;
                        } dans
                Sig_module(md.md_id, d, rs))
              decls rem,
            final_env
        | Psig_modtype pmtd ->
            soit newenv, mtd, sg =
              transl_modtype_decl modtype_names env item.psig_loc pmtd
            dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_modtype mtd) env loc :: trem,
            sg :: rem,
            final_env
        | Psig_open (ovf, lid, attrs) ->
            soit (path, newenv) = type_open ovf env item.psig_loc lid dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_open (ovf, path,lid,attrs)) env loc :: trem,
            rem, final_env
        | Psig_include (smty, attrs) ->
            soit tmty = transl_modtype env smty dans
            soit mty = tmty.mty_type dans
            soit sg = Subst.signature Subst.identity
                       (extract_sig env smty.pmty_loc mty) dans
            List.iter
              (check_sig_item type_names module_names modtype_names
                              item.psig_loc)
              sg;
            soit newenv = Env.add_signature sg env dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_include (tmty, sg, attrs)) env loc :: trem,
            remove_duplicates (get_values rem) (get_exceptions rem) sg @ rem,
            final_env
        | Psig_class cl ->
            List.iter
              (fonc {pci_name = name} ->
                 check "type" item.psig_loc type_names name.txt )
              cl;
            soit (classes, newenv) = Typeclass.class_descriptions env cl dans
            soit (trem, rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_class
                     (List.map2
                        (fonc pcl tcl ->
                          soit (_, _, _, _, _, _, _, _, _, _, _, tcl) = tcl dans
                          tcl)
                        cl classes)) env loc
            :: trem,
            List.flatten
              (map_rec
                 (fonc rs (i, _, d, i', d', i'', d'', i''', d''', _, _, _) ->
                   [Sig_class(i, d, rs);
                    Sig_class_type(i', d', rs);
                    Sig_type(i'', d'', rs);
                    Sig_type(i''', d''', rs)])
                 classes [rem]),
            final_env
        | Psig_class_type cl ->
            List.iter
              (fonc {pci_name = name} ->
                 check "type" item.psig_loc type_names name.txt)
              cl;
            soit (classes, newenv) = Typeclass.class_type_declarations env cl dans
            soit (trem,rem, final_env) = transl_sig newenv srem dans
            mksig (Tsig_class_type (List.map2 (fonc pcl tcl ->
              soit (_, _, _, _, _, _, _, tcl) = tcl dans
              tcl
            ) cl classes)) env loc :: trem,
            List.flatten
              (map_rec
                 (fonc rs (i, _, d, i', d', i'', d'', _) ->
                   [Sig_class_type(i, d, rs);
                    Sig_type(i', d', rs);
                    Sig_type(i'', d'', rs)])
                 classes [rem]),
            final_env
        | Psig_attribute x ->
            soit _back = Typetexp.warning_attribute [x] dans
            soit (trem,rem, final_env) = transl_sig env srem dans
            mksig (Tsig_attribute x) env loc :: trem, rem, final_env
        | Psig_extension ((s, _), _) ->
            raise (Error (s.loc, env, Extension s.txt))
  dans
  soit previous_saved_types = Cmt_format.get_saved_types () dans
  soit (trem, rem, final_env) = transl_sig (Env.in_signature env) sg dans
  soit sg = { sig_items = trem; sig_type =  rem; sig_final_env = final_env } dans
  Cmt_format.set_saved_types
    ((Cmt_format.Partial_signature sg) :: previous_saved_types);
  sg

et transl_modtype_decl modtype_names env loc
    {pmtd_name; pmtd_type; pmtd_attributes; pmtd_loc} =
  check "module type" loc modtype_names pmtd_name.txt;
  soit tmty = Misc.may_map (transl_modtype env) pmtd_type dans
  soit decl =
    {
     Types.mtd_type=may_map (fonc t -> t.mty_type) tmty;
     mtd_attributes=pmtd_attributes;
     mtd_loc=pmtd_loc;
    }
  dans
  soit (id, newenv) = Env.enter_modtype pmtd_name.txt decl env dans
  soit mtd =
    {
     mtd_id=id;
     mtd_name=pmtd_name;
     mtd_type=tmty;
     mtd_attributes=pmtd_attributes;
     mtd_loc=pmtd_loc;
    }
  dans
  newenv, mtd, Sig_modtype(id, decl)

et transl_recmodule_modtypes loc env sdecls =
  soit make_env curr =
    List.fold_left
      (fonc env (id, _, mty) -> Env.add_module ~arg:vrai id mty env)
      env curr dans
  soit make_env2 curr =
    List.fold_left
      (fonc env (id, _, mty) -> Env.add_module ~arg:vrai id mty.mty_type env)
      env curr dans
  soit transition env_c curr =
    List.map2
      (fonc pmd (id, id_loc, mty) ->
        (id, id_loc, transl_modtype env_c pmd.pmd_type))
      sdecls curr dans
  soit ids = List.map (fonc x -> Ident.create x.pmd_name.txt) sdecls dans
  soit approx_env =
    (*
       cf #5965
       We use a dummy module type in order to detect a reference to one
       of the module being defined during the call to approx_modtype.
       It will be detected in Env.lookup_module.
    *)
    List.fold_left
      (fonc env id ->
         soit dummy = Mty_ident (Path.Pident (Ident.create "#recmod#")) dans
         Env.add_module ~arg:vrai id dummy env
      )
      env ids
  dans
  soit init =
    List.map2
      (fonc id pmd ->
        (id, pmd.pmd_name, approx_modtype approx_env pmd.pmd_type))
      ids sdecls
  dans
  soit env0 = make_env init dans
  soit dcl1 = transition env0 init dans
  soit env1 = make_env2 dcl1 dans
  check_recmod_typedecls env1 sdecls dcl1;
  soit dcl2 = transition env1 dcl1 dans
(*
  List.iter
    (fun (id, mty) ->
      Format.printf "%a: %a@." Printtyp.ident id Printtyp.modtype mty)
    dcl2;
*)
  soit env2 = make_env2 dcl2 dans
  check_recmod_typedecls env2 sdecls dcl2;
  soit dcl2 =
    List.map2
      (fonc pmd (id, id_loc, mty) ->
        {md_id=id; md_name=id_loc; md_type=mty;
         md_loc=pmd.pmd_loc;
         md_attributes=pmd.pmd_attributes})
      sdecls dcl2
  dans
  (dcl2, env2)

(* Try to convert a module expression to a module path. *)

exception Not_a_path

soit rec path_of_module mexp =
  filtre mexp.mod_desc avec
    Tmod_ident (p,_) -> p
  | Tmod_apply(funct, arg, coercion) quand !Clflags.applicative_functors ->
      Papply(path_of_module funct, path_of_module arg)
  | Tmod_constraint (mexp, _, _, _) ->
      path_of_module mexp
  | _ -> raise Not_a_path

(* Check that all core type schemes in a structure are closed *)

soit rec closed_modtype = fonction
    Mty_ident p -> vrai
  | Mty_alias p -> vrai
  | Mty_signature sg -> List.for_all closed_signature_item sg
  | Mty_functor(id, param, body) -> closed_modtype body

et closed_signature_item = fonction
    Sig_value(id, desc) -> Ctype.closed_schema desc.val_type
  | Sig_module(id, md, _) -> closed_modtype md.md_type
  | _ -> vrai

soit check_nongen_scheme env str =
  filtre str.str_desc avec
    Tstr_value(rec_flag, pat_exp_list) ->
      List.iter
        (fonc {vb_expr=exp} ->
          si not (Ctype.closed_schema exp.exp_type) alors
            raise(Error(exp.exp_loc, env, Non_generalizable exp.exp_type)))
        pat_exp_list
  | Tstr_module {mb_expr=md;_} ->
      si not (closed_modtype md.mod_type) alors
        raise(Error(md.mod_loc, env, Non_generalizable_module md.mod_type))
  | _ -> ()

soit check_nongen_schemes env str =
  List.iter (check_nongen_scheme env) str

(* Helpers for typing recursive modules *)

soit anchor_submodule name anchor =
  filtre anchor avec None -> None | Some p -> Some(Pdot(p, name, nopos))
soit anchor_recmodule id anchor =
  Some (Pident id)

soit enrich_type_decls anchor decls oldenv newenv =
  filtre anchor avec
    None -> newenv
  | Some p ->
      List.fold_left
        (fonc e info ->
          soit id = info.typ_id dans
          soit info' =
            Mtype.enrich_typedecl oldenv (Pdot(p, Ident.name id, nopos))
              info.typ_type
          dans
            Env.add_type ~check:vrai id info' e)
        oldenv decls

soit enrich_module_type anchor name mty env =
  filtre anchor avec
    None -> mty
  | Some p -> Mtype.enrich_modtype env (Pdot(p, name, nopos)) mty

soit check_recmodule_inclusion env bindings =
  (* PR#4450, PR#4470: consider
        module rec X : DECL = MOD  where MOD has inferred type ACTUAL
     The "natural" typing condition
        E, X: ACTUAL |- ACTUAL <: DECL
     leads to circularities through manifest types.
     Instead, we "unroll away" the potential circularities a finite number
     of times.  The (weaker) condition we implement is:
        E, X: DECL,
           X1: ACTUAL,
           X2: ACTUAL{X <- X1}/X1
           ...
           Xn: ACTUAL{X <- X(n-1)}/X(n-1)
        |- ACTUAL{X <- Xn}/Xn <: DECL{X <- Xn}
     so that manifest types rooted at X(n+1) are expanded in terms of X(n),
     avoiding circularities.  The strengthenings ensure that
     Xn.t = X(n-1).t = ... = X2.t = X1.t.
     N can be chosen arbitrarily; larger values of N result in more
     recursive definitions being accepted.  A good choice appears to be
     the number of mutually recursive declarations. *)

  soit subst_and_strengthen env s id mty =
    Mtype.strengthen env (Subst.modtype s mty)
                         (Subst.module_path s (Pident id)) dans

  soit rec check_incl first_time n env s =
    si n > 0 alors début
      (* Generate fresh names Y_i for the rec. bound module idents X_i *)
      soit bindings1 =
        List.map
          (fonc (id, _, mty_decl, modl, mty_actual, _attrs, _loc) ->
             (id, Ident.rename id, mty_actual))
          bindings dans
      (* Enter the Y_i in the environment with their actual types substituted
         by the input substitution s *)
      soit env' =
        List.fold_left
          (fonc env (id, id', mty_actual) ->
             soit mty_actual' =
               si first_time
               alors mty_actual
               sinon subst_and_strengthen env s id mty_actual dans
             Env.add_module ~arg:faux id' mty_actual' env)
          env bindings1 dans
      (* Build the output substitution Y_i <- X_i *)
      soit s' =
        List.fold_left
          (fonc s (id, id', mty_actual) ->
             Subst.add_module id (Pident id') s)
          Subst.identity bindings1 dans
      (* Recurse with env' and s' *)
      check_incl faux (n-1) env' s'
    fin sinon début
      (* Base case: check inclusion of s(mty_actual) in s(mty_decl)
         and insert coercion if needed *)
      soit check_inclusion (id, id_loc, mty_decl, modl, mty_actual, attrs, loc) =
        soit mty_decl' = Subst.modtype s mty_decl.mty_type
        et mty_actual' = subst_and_strengthen env s id mty_actual dans
        soit coercion =
          essaie
            Includemod.modtypes env mty_actual' mty_decl'
          avec Includemod.Error msg ->
            raise(Error(modl.mod_loc, env, Not_included msg)) dans
        soit modl' =
            { mod_desc = Tmod_constraint(modl, mty_decl.mty_type,
                Tmodtype_explicit mty_decl, coercion);
              mod_type = mty_decl.mty_type;
              mod_env = env;
              mod_loc = modl.mod_loc;
              mod_attributes = [];
             } dans
        {
         mb_id = id;
         mb_name = id_loc;
         mb_expr = modl';
         mb_attributes = attrs;
         mb_loc = loc;
        }
      dans
      List.map check_inclusion bindings
    fin
  dans check_incl vrai (List.length bindings) env Subst.identity

(* Helper for unpack *)

soit rec package_constraints env loc mty constrs =
  si constrs = [] alors mty
  sinon soit sg = extract_sig env loc mty dans
  soit sg' =
    List.map
      (fonction
        | Sig_type (id, ({type_params=[]} tel td), rs)
          quand List.mem_assoc [Ident.name id] constrs ->
            soit ty = List.assoc [Ident.name id] constrs dans
            Sig_type (id, {td avec type_manifest = Some ty}, rs)
        | Sig_module (id, md, rs) ->
            soit rec aux = fonction
              | (m :: ((_ :: _) tel l), t) :: rest quand m = Ident.name id ->
                  (l, t) :: aux rest
              | _ :: rest -> aux rest
              | [] -> []
            dans
            soit md =
              {md avec
               md_type = package_constraints env loc md.md_type (aux constrs)
              }
            dans
            Sig_module (id, md, rs)
        | item -> item
      )
      sg
  dans
  Mty_signature sg'

soit modtype_of_package env loc p nl tl =
  essaie filtre (Env.find_modtype p env).mtd_type avec
  | Some mty quand nl <> [] ->
      package_constraints env loc mty
        (List.combine (List.map Longident.flatten nl) tl)
  | _ ->
      si nl = [] alors Mty_ident p
      sinon raise(Error(loc, env, Signature_expected))
  avec Not_found ->
    soit error = Typetexp.Unbound_modtype (Ctype.lid_of_path p) dans
    raise(Typetexp.Error(loc, env, error))

soit package_subtype env p1 nl1 tl1 p2 nl2 tl2 =
  soit mkmty p nl tl =
    soit ntl =
      List.filter (fonc (n,t) -> Ctype.free_variables t = [])
        (List.combine nl tl) dans
    soit (nl, tl) = List.split ntl dans
    modtype_of_package env Location.none p nl tl
  dans
  soit mty1 = mkmty p1 nl1 tl1 et mty2 = mkmty p2 nl2 tl2 dans
  essaie Includemod.modtypes env mty1 mty2 = Tcoerce_none
  avec Includemod.Error msg -> faux
    (* raise(Error(Location.none, env, Not_included msg)) *)

soit () = Ctype.package_subtype := package_subtype

soit wrap_constraint env arg mty explicit =
  soit coercion =
    essaie
      Includemod.modtypes env arg.mod_type mty
    avec Includemod.Error msg ->
      raise(Error(arg.mod_loc, env, Not_included msg)) dans
  { mod_desc = Tmod_constraint(arg, mty, explicit, coercion);
    mod_type = mty;
    mod_env = env;
    mod_attributes = [];
    mod_loc = arg.mod_loc }

(* Type a module value expression *)

soit rec type_module ?(alias=faux) sttn funct_body anchor env smod =
  filtre smod.pmod_desc avec
    Pmod_ident lid ->
      soit path = Typetexp.find_module env smod.pmod_loc lid.txt dans
      soit md = { mod_desc = Tmod_ident (path, lid);
                 mod_type = Mty_alias path;
                 mod_env = env;
                 mod_attributes = smod.pmod_attributes;
                 mod_loc = smod.pmod_loc } dans
      soit md =
        si alias && not (Env.is_functor_arg path env) alors
          (Env.add_required_global (Path.head path); md)
        sinon filtre (Env.find_module path env).md_type avec
          Mty_alias p1 quand not alias ->
            soit p1 = Env.normalize_path (Some smod.pmod_loc) env p1 dans
            soit mty = Includemod.expand_module_alias env [] p1 dans
            { md avec
              mod_desc = Tmod_constraint (md, mty, Tmodtype_implicit,
                                          Tcoerce_alias (p1, Tcoerce_none));
              mod_type = si sttn alors Mtype.strengthen env mty p1 sinon mty }
        | mty ->
            soit mty =
              si sttn alors Mtype.strengthen env mty path sinon mty dans
            { md avec mod_type = mty }
      dans rm md
  | Pmod_structure sstr ->
      soit (str, sg, finalenv) =
        type_structure funct_body anchor env sstr smod.pmod_loc dans
      rm { mod_desc = Tmod_structure str;
           mod_type = Mty_signature sg;
           mod_env = env;
           mod_attributes = smod.pmod_attributes;
           mod_loc = smod.pmod_loc }
  | Pmod_functor(name, smty, sbody) ->
      soit mty = may_map (transl_modtype env) smty dans
      soit ty_arg = may_map (fonc m -> m.mty_type) mty dans
      soit (id, newenv), funct_body =
        filtre ty_arg avec None -> (Ident.create "*", env), faux
        | Some mty -> Env.enter_module ~arg:vrai name.txt mty env, vrai dans
      soit body = type_module sttn funct_body None newenv sbody dans
      rm { mod_desc = Tmod_functor(id, name, mty, body);
           mod_type = Mty_functor(id, ty_arg, body.mod_type);
           mod_env = env;
           mod_attributes = smod.pmod_attributes;
           mod_loc = smod.pmod_loc }
  | Pmod_apply(sfunct, sarg) ->
      soit arg = type_module vrai funct_body None env sarg dans
      soit path = essaie Some (path_of_module arg) avec Not_a_path -> None dans
      soit funct =
        type_module (sttn && path <> None) funct_body None env sfunct dans
      début filtre Env.scrape_alias env funct.mod_type avec
        Mty_functor(param, mty_param, mty_res) tel mty_functor ->
          soit generative, mty_param =
            (mty_param = None, Btype.default_mty mty_param) dans
          si generative alors début
            si sarg.pmod_desc <> Pmod_structure [] alors
              raise (Error (sfunct.pmod_loc, env, Apply_generative));
            si funct_body && Mtype.contains_type env funct.mod_type alors
              raise (Error (smod.pmod_loc, env, Not_allowed_in_functor_body));
          fin;
          soit coercion =
            essaie
              Includemod.modtypes env arg.mod_type mty_param
            avec Includemod.Error msg ->
              raise(Error(sarg.pmod_loc, env, Not_included msg)) dans
          soit mty_appl =
            filtre path avec
              Some path ->
                Subst.modtype (Subst.add_module param path Subst.identity)
                              mty_res
            | None ->
                si generative alors mty_res sinon
                essaie
                  Mtype.nondep_supertype
                    (Env.add_module ~arg:vrai param arg.mod_type env)
                    param mty_res
                avec Not_found ->
                  raise(Error(smod.pmod_loc, env,
                              Cannot_eliminate_dependency mty_functor))
          dans
          rm { mod_desc = Tmod_apply(funct, arg, coercion);
               mod_type = mty_appl;
               mod_env = env;
               mod_attributes = smod.pmod_attributes;
               mod_loc = smod.pmod_loc }
      | _ ->
          raise(Error(sfunct.pmod_loc, env, Cannot_apply funct.mod_type))
      fin
  | Pmod_constraint(sarg, smty) ->
      soit arg = type_module ~alias vrai funct_body anchor env sarg dans
      soit mty = transl_modtype env smty dans
      rm {(wrap_constraint env arg mty.mty_type (Tmodtype_explicit mty)) avec
          mod_loc = smod.pmod_loc;
          mod_attributes = smod.pmod_attributes;
         }

  | Pmod_unpack sexp ->
      si !Clflags.principal alors Ctype.begin_def ();
      soit exp = Typecore.type_exp env sexp dans
      si !Clflags.principal alors début
        Ctype.end_def ();
        Ctype.generalize_structure exp.exp_type
      fin;
      soit mty =
        filtre Ctype.expand_head env exp.exp_type avec
          {desc = Tpackage (p, nl, tl)} ->
            si List.exists (fonc t -> Ctype.free_variables t <> []) tl alors
              raise (Error (smod.pmod_loc, env,
                            Incomplete_packed_module exp.exp_type));
            si !Clflags.principal &&
              not (Typecore.generalizable (Btype.generic_level-1) exp.exp_type)
            alors
              Location.prerr_warning smod.pmod_loc
                (Warnings.Not_principal "this module unpacking");
            modtype_of_package env smod.pmod_loc p nl tl
        | {desc = Tvar _} ->
            raise (Typecore.Error
                     (smod.pmod_loc, env, Typecore.Cannot_infer_signature))
        | _ ->
            raise (Error(smod.pmod_loc, env, Not_a_packed_module exp.exp_type))
      dans
      si funct_body && Mtype.contains_type env mty alors
        raise (Error (smod.pmod_loc, env, Not_allowed_in_functor_body));
      rm { mod_desc = Tmod_unpack(exp, mty);
           mod_type = mty;
           mod_env = env;
           mod_attributes = smod.pmod_attributes;
           mod_loc = smod.pmod_loc }
  | Pmod_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))

et type_structure ?(toplevel = faux) funct_body anchor env sstr scope =
  soit type_names = ref StringSet.empty
  et module_names = ref StringSet.empty
  et modtype_names = ref StringSet.empty dans

  soit type_str_item env srem {pstr_loc = loc; pstr_desc = desc} =
    filtre desc avec
    | Pstr_eval (sexpr, attrs) ->
        soit expr = Typecore.type_expression env sexpr dans
        Tstr_eval (expr, attrs), [], env
    | Pstr_value(rec_flag, sdefs) ->
        soit scope =
          filtre rec_flag avec
          | Recursive ->
              Some (Annot.Idef {scope avec
                                Location.loc_start = loc.Location.loc_start})
          | Nonrecursive ->
              soit start =
                filtre srem avec
                | [] -> loc.Location.loc_end
                | {pstr_loc = loc2} :: _ -> loc2.Location.loc_start
              dans
              Some (Annot.Idef {scope avec Location.loc_start = start})
        dans
        soit (defs, newenv) =
          Typecore.type_binding env rec_flag sdefs scope dans
        (* Note: Env.find_value does not trigger the value_used event. Values
           will be marked as being used during the signature inclusion test. *)
        Tstr_value(rec_flag, defs),
        List.map (fonc id -> Sig_value(id, Env.find_value (Pident id) newenv))
          (let_bound_idents defs),
        newenv
    | Pstr_primitive sdesc ->
        soit (desc, newenv) = Typedecl.transl_value_decl env loc sdesc dans
        Tstr_primitive desc, [Sig_value(desc.val_id, desc.val_val)], newenv
    | Pstr_type sdecls ->
        List.iter
          (fonc decl -> check "type" loc type_names decl.ptype_name.txt)
          sdecls;
        soit (decls, newenv) = Typedecl.transl_type_decl env sdecls dans
        Tstr_type decls,
        map_rec'' (fonc rs info -> Sig_type(info.typ_id, info.typ_type, rs))
          decls [],
        enrich_type_decls anchor decls env newenv
    | Pstr_exception sarg ->
        soit (arg, decl, newenv) = Typedecl.transl_exception env sarg dans
        Tstr_exception arg, [Sig_exception(arg.cd_id, decl)], newenv
    | Pstr_exn_rebind(name, longid, attrs) ->
        soit (path, arg) = Typedecl.transl_exn_rebind env loc longid.txt dans
        soit (id, newenv) = Env.enter_exception name.txt arg env dans
        Tstr_exn_rebind(id, name, path, longid, attrs),
        [Sig_exception(id, arg)],
        newenv
    | Pstr_module {pmb_name = name; pmb_expr = smodl; pmb_attributes = attrs;
                   pmb_loc;
                  } ->
        check "module" loc module_names name.txt;
        soit modl =
          type_module ~alias:vrai vrai funct_body
            (anchor_submodule name.txt anchor) env smodl dans
        soit md =
          { md_type = enrich_module_type anchor name.txt modl.mod_type env;
            md_attributes = attrs;
            md_loc = pmb_loc;
          }
        dans
        soit (id, newenv) = Env.enter_module_declaration name.txt md env dans
        Tstr_module {mb_id=id; mb_name=name; mb_expr=modl;
                     mb_attributes=attrs;  mb_loc=pmb_loc;
                    },
        [Sig_module(id,
                    {md_type = modl.mod_type;
                     md_attributes = attrs;
                     md_loc = pmb_loc;
                    }, Trec_not)],
        newenv
    | Pstr_recmodule sbind ->
        soit sbind =
          List.map
            (fonction
              | {pmb_name = name;
                 pmb_expr = {pmod_desc=Pmod_constraint(expr, typ)};
                 pmb_attributes = attrs;
                 pmb_loc = loc;
                } ->
                  name, typ, expr, attrs, loc
              | mb ->
                  raise (Error (mb.pmb_expr.pmod_loc, env,
                                Recursive_module_require_explicit_type))
            )
            sbind
        dans
        List.iter
          (fonc (name, _, _, _, _) -> check "module" loc module_names name.txt)
          sbind;
        soit (decls, newenv) =
          transl_recmodule_modtypes loc env
            (List.map (fonc (name, smty, smodl, attrs, loc) ->
                 {pmd_name=name; pmd_type=smty;
                  pmd_attributes=attrs; pmd_loc=loc}) sbind
            ) dans
        soit bindings1 =
          List.map2
            (fonc {md_id=id; md_type=mty} (name, _, smodl, attrs, loc) ->
               soit modl =
                 type_module vrai funct_body (anchor_recmodule id anchor) newenv
                   smodl dans
               soit mty' =
                 enrich_module_type anchor (Ident.name id) modl.mod_type newenv
               dans
               (id, name, mty, modl, mty', attrs, loc))
            decls sbind dans
        soit newenv = (* allow aliasing recursive modules from outside *)
          List.fold_left
            (fonc env md -> Env.add_module md.md_id md.md_type.mty_type env)
            env decls
        dans
        soit bindings2 =
          check_recmodule_inclusion newenv bindings1 dans
        Tstr_recmodule bindings2,
        map_rec (fonc rs mb ->
            Sig_module(mb.mb_id, {
                md_type=mb.mb_expr.mod_type;
                md_attributes=mb.mb_attributes;
                md_loc=mb.mb_loc;
              }, rs))
           bindings2 [],
        newenv
    | Pstr_modtype pmtd ->
        (* check that it is non-abstract *)
        soit newenv, mtd, sg =
          transl_modtype_decl modtype_names env loc pmtd
        dans
        Tstr_modtype mtd, [sg], newenv
    | Pstr_open (ovf, lid, attrs) ->
        soit (path, newenv) = type_open ovf ~toplevel env loc lid dans
        Tstr_open (ovf, path, lid, attrs), [], newenv
    | Pstr_class cl ->
        List.iter
          (fonc {pci_name = name} -> check "type" loc type_names name.txt)
          cl;
        soit (classes, new_env) = Typeclass.class_declarations env cl dans
        Tstr_class
          (List.map (fonc (i, _, d, _,_,_,_,_,_, s, m, c) ->
               soit vf = si d.cty_new = None alors Virtual sinon Concrete dans
               (* (i, s, m, c, vf) *) (c, m, vf))
              classes),
(* TODO: check with Jacques why this is here
      Tstr_class_type
          (List.map (fun (_,_, i, d, _,_,_,_,_,_,c) -> (i, c)) classes) ::
      Tstr_type
          (List.map (fun (_,_,_,_, i, d, _,_,_,_,_) -> (i, d)) classes) ::
      Tstr_type
          (List.map (fun (_,_,_,_,_,_, i, d, _,_,_) -> (i, d)) classes) ::
*)
        List.flatten
          (map_rec
             (fonc rs (i, _, d, i', d', i'', d'', i''', d''', _, _, _) ->
                [Sig_class(i, d, rs);
                 Sig_class_type(i', d', rs);
                 Sig_type(i'', d'', rs);
                 Sig_type(i''', d''', rs)])
             classes []),
        new_env
    | Pstr_class_type cl ->
        List.iter
          (fonc {pci_name = name} -> check "type" loc type_names name.txt)
          cl;
        soit (classes, new_env) = Typeclass.class_type_declarations env cl dans
        Tstr_class_type
          (List.map (fonc (i, i_loc, d, _, _, _, _, c) ->
               (i, i_loc, c)) classes),
(*  TODO: check with Jacques why this is here
           Tstr_type
             (List.map (fun (_, _, i, d, _, _) -> (i, d)) classes) ::
           Tstr_type
             (List.map (fun (_, _, _, _, i, d) -> (i, d)) classes) :: *)
        List.flatten
          (map_rec
             (fonc rs (i, _, d, i', d', i'', d'', _) ->
                [Sig_class_type(i, d, rs);
                 Sig_type(i', d', rs);
                 Sig_type(i'', d'', rs)])
             classes []),
        new_env
    | Pstr_include (smodl, attrs) ->
        soit modl = type_module vrai funct_body None env smodl dans
        (* Rename all identifiers bound by this signature to avoid clashes *)
        soit sg = Subst.signature Subst.identity
            (extract_sig_open env smodl.pmod_loc modl.mod_type) dans
        soit sg =
          filtre modl.mod_desc avec
            Tmod_ident (p, _) quand not (Env.is_functor_arg p env) ->
              Env.add_required_global (Path.head p);
              soit pos = ref 0 dans
              List.map
                (fonction
                  | Sig_module (id, md, rs) ->
                      soit n = !pos dans incr pos;
                      Sig_module (id, {md avec md_type =
                                       Mty_alias (Pdot(p,Ident.name id,n))},
                                  rs)
                  | Sig_value (_, {val_kind=Val_reg}) | Sig_exception _
                  | Sig_class _ tel it ->
                      incr pos; it
                  | Sig_value _ | Sig_type _ | Sig_modtype _
                  | Sig_class_type _ tel it ->
                      it)
                sg
          | _ -> sg
        dans
        List.iter
          (check_sig_item type_names module_names modtype_names loc) sg;
        soit new_env = Env.add_signature sg env dans
        Tstr_include (modl, sg, attrs), sg, new_env
    | Pstr_extension ((s, _), _) ->
        raise (Error (s.loc, env, Extension s.txt))
    | Pstr_attribute x ->
        soit _back = Typetexp.warning_attribute [x] dans
        Tstr_attribute x, [], env
  dans
  soit rec type_struct env sstr =
    Ctype.init_def(Ident.current_time());
    filtre sstr avec
    | [] -> ([], [], env)
    | pstr :: srem ->
        soit previous_saved_types = Cmt_format.get_saved_types () dans
        soit desc, sg, new_env = type_str_item env srem pstr dans
        soit str = { str_desc = desc; str_loc = pstr.pstr_loc; str_env = env } dans
        Cmt_format.set_saved_types (Cmt_format.Partial_structure_item str
                                    :: previous_saved_types);
        soit (str_rem, sig_rem, final_env) = type_struct new_env srem dans
        (str :: str_rem, sg @ sig_rem, final_env)
  dans
  si !Clflags.annotations alors
    (* moved to genannot *)
    List.iter (fonction {pstr_loc = l} -> Stypes.record_phrase l) sstr;
  soit previous_saved_types = Cmt_format.get_saved_types () dans
  soit (items, sg, final_env) = type_struct env sstr dans
  soit str = { str_items = items; str_type = sg; str_final_env = final_env } dans
  Cmt_format.set_saved_types
    (Cmt_format.Partial_structure str :: previous_saved_types);
  str, sg, final_env

soit type_toplevel_phrase env s =
  Env.reset_required_globals ();
  type_structure ~toplevel:vrai faux None env s Location.none
(*let type_module_alias = type_module ~alias:true true false None*)
soit type_module = type_module vrai faux None
soit type_structure = type_structure faux None

(* Normalize types in a signature *)

soit rec normalize_modtype env = fonction
    Mty_ident p -> ()
  | Mty_alias p -> ()
  | Mty_signature sg -> normalize_signature env sg
  | Mty_functor(id, param, body) -> normalize_modtype env body

et normalize_signature env = List.iter (normalize_signature_item env)

et normalize_signature_item env = fonction
    Sig_value(id, desc) -> Ctype.normalize_type env desc.val_type
  | Sig_module(id, md, _) -> normalize_modtype env md.md_type
  | _ -> ()

(* Simplify multiple specifications of a value or an exception in a signature.
   (Other signature components, e.g. types, modules, etc, are checked for
   name uniqueness.)  If multiple specifications with the same name,
   keep only the last (rightmost) one. *)

soit rec simplify_modtype mty =
  filtre mty avec
    Mty_ident path -> mty
  | Mty_alias path -> mty
  | Mty_functor(id, arg, res) -> Mty_functor(id, arg, simplify_modtype res)
  | Mty_signature sg -> Mty_signature(simplify_signature sg)

et simplify_signature sg =
  soit rec simplif val_names exn_names res = fonction
    [] -> res
  | (Sig_value(id, descr) tel component) :: sg ->
      soit name = Ident.name id dans
      simplif (StringSet.add name val_names) exn_names
              (si StringSet.mem name val_names alors res sinon component :: res)
              sg
  | (Sig_exception(id, decl) tel component) :: sg ->
      soit name = Ident.name id dans
      simplif val_names (StringSet.add name exn_names)
              (si StringSet.mem name exn_names alors res sinon component :: res)
              sg
  | Sig_module(id, md, rs) :: sg ->
      soit md = {md avec md_type = simplify_modtype md.md_type} dans
      simplif val_names exn_names
              (Sig_module(id, md, rs) :: res) sg
  | component :: sg ->
      simplif val_names exn_names (component :: res) sg
  dans
    simplif StringSet.empty StringSet.empty [] (List.rev sg)

(* Extract the module type of a module expression *)

soit type_module_type_of env smod =
  soit tmty =
    filtre smod.pmod_desc avec
    | Pmod_ident lid -> (* turn off strengthening in this case *)
        soit path = Typetexp.find_module env smod.pmod_loc lid.txt dans
        soit md = Env.find_module path env dans
        rm { mod_desc = Tmod_ident (path, lid);
             mod_type = md.md_type;
             mod_env = env;
             mod_attributes = smod.pmod_attributes;
             mod_loc = smod.pmod_loc }
    | _ -> type_module env smod dans
  soit mty = tmty.mod_type dans
  (* PR#6307: expand aliases at root and submodules *)
  soit mty = Mtype.remove_aliases env mty dans
  (* PR#5037: clean up inferred signature to remove duplicate specs *)
  soit mty = simplify_modtype mty dans
  (* PR#5036: must not contain non-generalized type variables *)
  si not (closed_modtype mty) alors
    raise(Error(smod.pmod_loc, env, Non_generalizable_module mty));
  tmty, mty

(* For Typecore *)

soit rec get_manifest_types = fonction
    [] -> []
  | Sig_type (id, {type_params=[]; type_manifest=Some ty}, _) :: rem ->
      (Ident.name id, ty) :: get_manifest_types rem
  | _ :: rem -> get_manifest_types rem

soit type_package env m p nl tl =
  (* Same as Pexp_letmodule *)
  (* remember original level *)
  soit lv = Ctype.get_current_level () dans
  Ctype.begin_def ();
  Ident.set_current_time lv;
  soit context = Typetexp.narrow () dans
  soit modl = type_module env m dans
  Ctype.init_def(Ident.current_time());
  Typetexp.widen context;
  soit (mp, env) =
    filtre modl.mod_desc avec
      Tmod_ident (mp,_) -> (mp, env)
    | _ ->
      soit (id, new_env) = Env.enter_module ~arg:vrai "%M" modl.mod_type env dans
      (Pident id, new_env)
  dans
  soit rec mkpath mp = fonction
    | Lident name -> Pdot(mp, name, nopos)
    | Ldot (m, name) -> Pdot(mkpath mp m, name, nopos)
    | _ -> affirme faux
  dans
  soit tl' =
    List.map
      (fonc name -> Btype.newgenty (Tconstr (mkpath mp name,[],ref Mnil)))
      nl dans
  (* go back to original level *)
  Ctype.end_def ();
  si nl = [] alors
    (wrap_constraint env modl (Mty_ident p) Tmodtype_implicit, [])
  sinon soit mty = modtype_of_package env modl.mod_loc p nl tl' dans
  List.iter2
    (fonc n ty ->
      essaie Ctype.unify env ty (Ctype.newvar ())
      avec Ctype.Unify _ ->
        raise (Error(m.pmod_loc, env, Scoping_pack (n,ty))))
    nl tl';
  (wrap_constraint env modl mty Tmodtype_implicit, tl')

(* Fill in the forward declarations *)
soit () =
  Typecore.type_module := type_module;
  Typetexp.transl_modtype_longident := transl_modtype_longident;
  Typetexp.transl_modtype := transl_modtype;
  Typecore.type_open := type_open ?toplevel:None;
  Typecore.type_package := type_package;
  type_module_type_of_fwd := type_module_type_of

(* Typecheck an implementation file *)

soit type_implementation sourcefile outputprefix modulename initial_env ast =
  Cmt_format.clear ();
  essaie
  Typecore.reset_delayed_checks ();
  Env.reset_required_globals ();
  soit (str, sg, finalenv) =
    type_structure initial_env ast (Location.in_file sourcefile) dans
  soit simple_sg = simplify_signature sg dans
  si !Clflags.print_types alors début
    Printtyp.wrap_printing_env initial_env
      (fonc () -> fprintf std_formatter "%a@." Printtyp.signature simple_sg);
    (str, Tcoerce_none)   (* result is ignored by Compile.implementation *)
  fin sinon début
    soit sourceintf =
      Misc.chop_extension_if_any sourcefile ^ !Config.interface_suffix dans
    si Sys.file_exists sourceintf alors début
      soit intf_file =
        essaie
          find_in_path_uncap !Config.load_path (modulename ^ ".cmi")
        avec Not_found ->
          raise(Error(Location.in_file sourcefile, Env.empty,
                      Interface_not_compiled sourceintf)) dans
      soit dclsig = Env.read_signature modulename intf_file dans
      soit coercion = Includemod.compunit sourcefile sg intf_file dclsig dans
      Typecore.force_delayed_checks ();
      (* It is important to run these checks after the inclusion test above,
         so that value declarations which are not used internally but exported
         are not reported as being unused. *)
      Cmt_format.save_cmt (outputprefix ^ ".cmt") modulename
        (Cmt_format.Implementation str) (Some sourcefile) initial_env None;
      (str, coercion)
    fin sinon début
      check_nongen_schemes finalenv str.str_items;
      normalize_signature finalenv simple_sg;
      soit coercion =
        Includemod.compunit sourcefile sg
                            "(inferred signature)" simple_sg dans
      Typecore.force_delayed_checks ();
      (* See comment above. Here the target signature contains all
         the value being exported. We can still capture unused
         declarations like "let x = true;; let x = 1;;", because in this
         case, the inferred signature contains only the last declaration. *)
      si not !Clflags.dont_write_files alors début
        soit sg =
          Env.save_signature simple_sg modulename (outputprefix ^ ".cmi") dans
        Cmt_format.save_cmt  (outputprefix ^ ".cmt") modulename
          (Cmt_format.Implementation str)
          (Some sourcefile) initial_env (Some sg);
      fin;
      (str, coercion)
    fin
    fin
  avec e ->
    Cmt_format.save_cmt  (outputprefix ^ ".cmt") modulename
      (Cmt_format.Partial_implementation
         (Array.of_list (Cmt_format.get_saved_types ())))
      (Some sourcefile) initial_env None;
    raise e


soit save_signature modname tsg outputprefix source_file initial_env cmi =
  Cmt_format.save_cmt  (outputprefix ^ ".cmti") modname
    (Cmt_format.Interface tsg) (Some source_file) initial_env (Some cmi)

(* "Packaging" of several compilation units into one unit
   having them as sub-modules.  *)

soit rec package_signatures subst = fonction
    [] -> []
  | (name, sg) :: rem ->
      soit sg' = Subst.signature subst sg dans
      soit oldid = Ident.create_persistent name
      et newid = Ident.create name dans
      Sig_module(newid, {md_type=Mty_signature sg';
                         md_attributes=[];
                         md_loc=Location.none;
                        },
                 Trec_not) ::
      package_signatures (Subst.add_module oldid (Pident newid) subst) rem

soit package_units objfiles cmifile modulename =
  (* Read the signatures of the units *)
  soit units =
    List.map
      (fonc f ->
         soit pref = chop_extensions f dans
         soit modname = String.capitalize(Filename.basename pref) dans
         soit sg = Env.read_signature modname (pref ^ ".cmi") dans
         si Filename.check_suffix f ".cmi" &&
            not(Mtype.no_code_needed_sig Env.initial sg)
         alors raise(Error(Location.none, Env.empty,
                          Implementation_is_required f));
         (modname, Env.read_signature modname (pref ^ ".cmi")))
      objfiles dans
  (* Compute signature of packaged unit *)
  Ident.reinit();
  soit sg = package_signatures Subst.identity units dans
  (* See if explicit interface is provided *)
  soit prefix = chop_extension_if_any cmifile dans
  soit mlifile = prefix ^ !Config.interface_suffix dans
  si Sys.file_exists mlifile alors début
    si not (Sys.file_exists cmifile) alors début
      raise(Error(Location.in_file mlifile, Env.empty,
                  Interface_not_compiled mlifile))
    fin;
    soit dclsig = Env.read_signature modulename cmifile dans
    Cmt_format.save_cmt  (prefix ^ ".cmt") modulename
      (Cmt_format.Packed (sg, objfiles)) None Env.initial None ;
    Includemod.compunit "(obtained by packing)" sg mlifile dclsig
  fin sinon début
    (* Determine imports *)
    soit unit_names = List.map fst units dans
    soit imports =
      List.filter
        (fonc (name, crc) -> not (List.mem name unit_names))
        (Env.imported_units()) dans
    (* Write packaged signature *)
    si not !Clflags.dont_write_files alors début
      soit sg =
        Env.save_signature_with_imports sg modulename
          (prefix ^ ".cmi") imports dans
      Cmt_format.save_cmt (prefix ^ ".cmt")  modulename
        (Cmt_format.Packed (sg, objfiles)) None Env.initial (Some sg)
    fin;
    Tcoerce_none
  fin

(* Error report *)

ouvre Printtyp

soit report_error ppf = fonction
    Cannot_apply mty ->
      fprintf ppf
        "@[Ce module n'est pas un foncteur; il a le type@ %a@]" modtype mty
  | Not_included errs ->
      fprintf ppf
        "@[<v>Différence dans les signatures :@ %a@]" Includemod.report_error errs
  | Cannot_eliminate_dependency mty ->
      fprintf ppf
        "@[Ce foncteur a pour type@ %a@ \
           Le paramètre ne peut pas être éliminé dans le type de résultat.@  \
           Veuillez lier l'argument à un identifiant de module.@]" modtype mty
  | Signature_expected -> fprintf ppf "Ce type de module n'est pas une signature"
  | Structure_expected mty ->
      fprintf ppf
        "@[Ce module n'est pas une structure ; il a pour type@ %a" modtype mty
  | With_no_component lid ->
      fprintf ppf
        "@[La signature contrainte par `avec' n'a pas de composante nomée %a@]"
        longident lid
  | With_mismatch(lid, explanation) ->
      fprintf ppf
        "@[<v>\
           @[Dans cette contrainte `avec', la nouvelle définition de %a@ \
             ne correspond pas à sa définition originale@ \
             dans la signature contrainte :@]@ \
           %a@]"
        longident lid Includemod.report_error explanation
  | Repeated_name(kind, name) ->
      fprintf ppf
        "@[Définition multiple du nom de %s %s.@ \
           Les noms doivent être uniques dans une structure ou signature donnée.@]" kind name
  | Non_generalizable typ ->
      fprintf ppf
        "@[Le type de cette expression,@ %a,@ \
           contient des variables de type qui ne peuvent pas être généralisées@]" type_scheme typ
  | Non_generalizable_class (id, desc) ->
      fprintf ppf
        "@[Le type de cette classe,@ %a,@ \
           contient des variables de type qui ne peuvent pas être généralisées@]"
        (class_declaration id) desc
  | Non_generalizable_module mty ->
      fprintf ppf
        "@[Le type de ce module,@ %a,@ \
           contient des variables de type qui ne peuvent pas être généralisées@]" modtype mty
  | Implementation_is_required intf_name ->
      fprintf ppf
        "@[L'interface %a@ déclare des valeurs, et non juste des types.@ \
           Un implémentation doit être fournie.@]"
        Location.print_filename intf_name
  | Interface_not_compiled intf_name ->
      fprintf ppf
        "@[Impossible de trouver le fichier .cmi pour l'interface@ %a.@]"
        Location.print_filename intf_name
  | Not_allowed_in_functor_body ->
      fprintf ppf
        "@[Cette expression crée des types frais.@ %s@]"
        "Cela n'est pas autorisé dans les foncteurs applicatifs."
  | With_need_typeconstr ->
      fprintf ppf
        "Seuls les constructeurs de type avec des paramètres identiques peuvent être substitués."
  | Not_a_packed_module ty ->
      fprintf ppf
        "Cette expression n'est pas un module empaqueté. Elle a le type@ %a"
        type_expr ty
  | Incomplete_packed_module ty ->
      fprintf ppf
        "Le type de ce module empaqueté contient des variables :@ %a"
        type_expr ty
  | Scoping_pack (lid, ty) ->
      fprintf ppf
        "Le type %a dans ce module ne peut pas être exporté.@ " longident lid;
      fprintf ppf
        "Son type contient des dépendances locales :@ %a" type_expr ty
  | Extension s ->
      fprintf ppf "Extension non interprétée '%s'." s
  | Recursive_module_require_explicit_type ->
      fprintf ppf "Les modules récursifs requièrent un type de module explicite."
  | Apply_generative ->
      fprintf ppf "Ceci est un foncteur génératif. Il ne peut être appliqué qu'à ()"

soit report_error env ppf err =
  Printtyp.wrap_printing_env env (fonc () -> report_error ppf err)

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, env, err) ->
        Some (Location.error_of_printer loc (report_error env) err)
      | _ ->
        None
    )
