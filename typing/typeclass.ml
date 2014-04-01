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

ouvre Parsetree
ouvre Asttypes
ouvre Path
ouvre Types
ouvre Typecore
ouvre Typetexp
ouvre Format

type error =
    Unconsistent_constraint de (type_expr * type_expr) list
  | Field_type_mismatch de string * string * (type_expr * type_expr) list
  | Structure_expected de class_type
  | Cannot_apply de class_type
  | Apply_wrong_label de label
  | Pattern_type_clash de type_expr
  | Repeated_parameter
  | Unbound_class_2 de Longident.t
  | Unbound_class_type_2 de Longident.t
  | Abbrev_type_clash de type_expr * type_expr * type_expr
  | Constructor_type_mismatch de string * (type_expr * type_expr) list
  | Virtual_class de bool * bool * string list * string list
  | Parameter_arity_mismatch de Longident.t * int * int
  | Parameter_mismatch de (type_expr * type_expr) list
  | Bad_parameters de Ident.t * type_expr * type_expr
  | Class_match_failure de Ctype.class_match_failure list
  | Unbound_val de string
  | Unbound_type_var de (formatter -> unit) * Ctype.closed_class_failure
  | Make_nongen_seltype de type_expr
  | Non_generalizable_class de Ident.t * Types.class_declaration
  | Cannot_coerce_self de type_expr
  | Non_collapsable_conjunction de
      Ident.t * Types.class_declaration * (type_expr * type_expr) list
  | Final_self_clash de (type_expr * type_expr) list
  | Mutability_mismatch de string * mutable_flag
  | No_overriding de string * string
  | Duplicate de string * string
  | Extension de string

exception Error de Location.t * Env.t * error

ouvre Typedtree

soit ctyp desc typ env loc =
  { ctyp_desc = desc; ctyp_type = typ; ctyp_loc = loc; ctyp_env = env; ctyp_attributes = [] }

                       (**********************)
                       (*  Useful constants  *)
                       (**********************)


(*
   Self type have a dummy private method, thus preventing it to become
   closed.
*)
soit dummy_method = Btype.dummy_method

(*
   Path associated to the temporary class type of a class being typed
   (its constructor is not available).
*)
soit unbound_class = Path.Pident (Ident.create "")


                (************************************)
                (*  Some operations on class types  *)
                (************************************)


(* Fully expand the head of a class type *)
soit rec scrape_class_type =
  fonction
    Cty_constr (_, _, cty) -> scrape_class_type cty
  | cty                     -> cty

(* Generalize a class type *)
soit rec generalize_class_type gen =
  fonction
    Cty_constr (_, params, cty) ->
      List.iter gen params;
      generalize_class_type gen cty
  | Cty_signature {csig_self = sty; csig_vars = vars; csig_inher = inher} ->
      gen sty;
      Vars.iter (fonc _ (_, _, ty) -> gen ty) vars;
      List.iter (fonc (_,tl) -> List.iter gen tl) inher
  | Cty_arrow (_, ty, cty) ->
      gen ty;
      generalize_class_type gen cty

soit generalize_class_type vars =
  soit gen = si vars alors Ctype.generalize sinon Ctype.generalize_structure dans
  generalize_class_type gen

(* Return the virtual methods of a class type *)
soit virtual_methods sign =
  soit (fields, _) =
    Ctype.flatten_fields (Ctype.object_fields sign.Types.csig_self)
  dans
  List.fold_left
    (fonc virt (lab, _, _) ->
       si lab = dummy_method alors virt sinon
       si Concr.mem lab sign.csig_concr alors virt sinon
       lab::virt)
    [] fields

(* Return the constructor type associated to a class type *)
soit rec constructor_type constr cty =
  filtre cty avec
    Cty_constr (_, _, cty) ->
      constructor_type constr cty
  | Cty_signature sign ->
      constr
  | Cty_arrow (l, ty, cty) ->
      Ctype.newty (Tarrow (l, ty, constructor_type constr cty, Cok))

soit rec class_body cty =
  filtre cty avec
    Cty_constr (_, _, cty') ->
      cty (* Only class bodies can be abbreviated *)
  | Cty_signature sign ->
      cty
  | Cty_arrow (_, ty, cty) ->
      class_body cty

soit extract_constraints cty =
  soit sign = Ctype.signature_of_class_type cty dans
  (Vars.fold (fonc lab _ vars -> lab :: vars) sign.csig_vars [],
   début soit (fields, _) =
     Ctype.flatten_fields (Ctype.object_fields sign.csig_self)
   dans
   List.fold_left
     (fonc meths (lab, _, _) ->
        si lab = dummy_method alors meths sinon lab::meths)
     [] fields
   fin,
   sign.csig_concr)

soit rec abbreviate_class_type path params cty =
  filtre cty avec
    Cty_constr (_, _, _) | Cty_signature _ ->
      Cty_constr (path, params, cty)
  | Cty_arrow (l, ty, cty) ->
      Cty_arrow (l, ty, abbreviate_class_type path params cty)

soit rec closed_class_type =
  fonction
    Cty_constr (_, params, _) ->
      List.for_all Ctype.closed_schema params
  | Cty_signature sign ->
      Ctype.closed_schema sign.csig_self
        &&
      Vars.fold (fonc _ (_, _, ty) cc -> Ctype.closed_schema ty && cc)
        sign.csig_vars
        vrai
  | Cty_arrow (_, ty, cty) ->
      Ctype.closed_schema ty
        &&
      closed_class_type cty

soit closed_class cty =
  List.for_all Ctype.closed_schema cty.cty_params
    &&
  closed_class_type cty.cty_type

soit rec limited_generalize rv =
  fonction
    Cty_constr (path, params, cty) ->
      List.iter (Ctype.limited_generalize rv) params;
      limited_generalize rv cty
  | Cty_signature sign ->
      Ctype.limited_generalize rv sign.csig_self;
      Vars.iter (fonc _ (_, _, ty) -> Ctype.limited_generalize rv ty)
        sign.csig_vars;
      List.iter (fonc (_, tl) -> List.iter (Ctype.limited_generalize rv) tl)
        sign.csig_inher
  | Cty_arrow (_, ty, cty) ->
      Ctype.limited_generalize rv ty;
      limited_generalize rv cty

(* Record a class type *)
soit rc node =
  Cmt_format.add_saved_type (Cmt_format.Partial_class_expr node);
  Stypes.record (Stypes.Ti_class node); (* moved to genannot *)
  node


                (***********************************)
                (*  Primitives for typing classes  *)
                (***********************************)


(* Enter a value in the method environment only *)
soit enter_met_env ?check loc lab kind ty val_env met_env par_env =
  soit (id, val_env) =
    Env.enter_value lab {val_type = ty; val_kind = Val_unbound;
                         val_attributes = [];
                         Types.val_loc = loc} val_env
  dans
  (id, val_env,
   Env.add_value ?check id {val_type = ty; val_kind = kind;
                            val_attributes = [];
                            Types.val_loc = loc} met_env,
   Env.add_value id {val_type = ty; val_kind = Val_unbound;
                     val_attributes = [];
                     Types.val_loc = loc} par_env)

(* Enter an instance variable in the environment *)
soit enter_val cl_num vars inh lab mut virt ty val_env met_env par_env loc =
  soit instance = Ctype.instance val_env dans
  soit (id, virt) =
    essaie
      soit (id, mut', virt', ty') = Vars.find lab !vars dans
      si mut' <> mut alors
        raise (Error(loc, val_env, Mutability_mismatch(lab, mut)));
      Ctype.unify val_env (instance ty) (instance ty');
      (si not inh alors Some id sinon None),
      (si virt' = Concrete alors virt' sinon virt)
    avec
      Ctype.Unify tr ->
        raise (Error(loc, val_env,
                     Field_type_mismatch("variable d'instance", lab, tr)))
    | Not_found -> None, virt
  dans
  soit (id, _, _, _) tel result =
    filtre id avec Some id -> (id, val_env, met_env, par_env)
    | None ->
        enter_met_env Location.none lab (Val_ivar (mut, cl_num))
          ty val_env met_env par_env
  dans
  vars := Vars.add lab (id, mut, virt, ty) !vars;
  result

soit concr_vals vars =
  Vars.fold
    (fonc id (_, vf, _) s -> si vf = Virtual alors s sinon Concr.add id s)
    vars Concr.empty

soit inheritance self_type env ovf concr_meths warn_vals loc parent =
  filtre scrape_class_type parent avec
    Cty_signature cl_sig ->

      (* Methods *)
      début essaie
        Ctype.unify env self_type cl_sig.csig_self
      avec Ctype.Unify trace ->
        filtre trace avec
          _::_::_::({desc = Tfield(n, _, _, _)}, _)::rem ->
            raise(Error(loc, env, Field_type_mismatch ("méthode", n, rem)))
        | _ ->
            affirme faux
      fin;

      (* Overriding *)
      soit over_meths = Concr.inter cl_sig.csig_concr concr_meths dans
      soit concr_vals = concr_vals cl_sig.csig_vars dans
      soit over_vals = Concr.inter concr_vals warn_vals dans
      début filtre ovf avec
        Some Fresh ->
          soit cname =
            filtre parent avec
              Cty_constr (p, _, _) -> Path.name p
            | _ -> "hérité"
          dans
          si not (Concr.is_empty over_meths) alors
            Location.prerr_warning loc
              (Warnings.Method_override (cname :: Concr.elements over_meths));
          si not (Concr.is_empty over_vals) alors
            Location.prerr_warning loc
              (Warnings.Instance_variable_override
                 (cname :: Concr.elements over_vals));
      | Some Override
        quand Concr.is_empty over_meths && Concr.is_empty over_vals ->
        raise (Error(loc, env, No_overriding ("","")))
      | _ -> ()
      fin;

      soit concr_meths = Concr.union cl_sig.csig_concr concr_meths
      et warn_vals = Concr.union concr_vals warn_vals dans

      (cl_sig, concr_meths, warn_vals)

  | _ ->
      raise(Error(loc, env, Structure_expected parent))

soit virtual_method val_env meths self_type lab priv sty loc =
  soit (_, ty') =
     Ctype.filter_self_method val_env lab priv meths self_type
  dans
  soit sty = Ast_helper.Typ.force_poly sty dans
  soit cty = transl_simple_type val_env faux sty dans
  soit ty = cty.ctyp_type dans
  début
    essaie Ctype.unify val_env ty ty' avec Ctype.Unify trace ->
        raise(Error(loc, val_env, Field_type_mismatch ("méthode", lab, trace)));
  fin;
  cty

soit delayed_meth_specs = ref []

soit declare_method val_env meths self_type lab priv sty loc =
  soit (_, ty') =
     Ctype.filter_self_method val_env lab priv meths self_type
  dans
  soit unif ty =
    essaie Ctype.unify val_env ty ty' avec Ctype.Unify trace ->
      raise(Error(loc, val_env, Field_type_mismatch ("méthode", lab, trace)))
  dans
  soit sty = Ast_helper.Typ.force_poly sty dans
  filtre sty.ptyp_desc, priv avec
    Ptyp_poly ([],sty'), Public ->
(* TODO: we moved the [transl_simple_type_univars] outside of the lazy,
so that we can get an immediate value. Is that correct ? Ask Jacques. *)
      soit returned_cty = ctyp Ttyp_any (Ctype.newty Tnil) val_env loc dans
      delayed_meth_specs :=
      paresseux (
        soit cty = transl_simple_type_univars val_env sty' dans
        soit ty = cty.ctyp_type dans
        unif ty;
        returned_cty.ctyp_desc <- Ttyp_poly ([], cty);
        returned_cty.ctyp_type <- ty;
        ) ::
      !delayed_meth_specs;
      returned_cty
  | _ ->
      soit cty = transl_simple_type val_env faux sty dans
      soit ty = cty.ctyp_type dans
      unif ty;
      cty

soit type_constraint val_env sty sty' loc =
  soit cty  = transl_simple_type val_env faux sty dans
  soit ty = cty.ctyp_type dans
  soit cty' = transl_simple_type val_env faux sty' dans
  soit ty' = cty'.ctyp_type dans
  début
    essaie Ctype.unify val_env ty ty' avec Ctype.Unify trace ->
        raise(Error(loc, val_env, Unconsistent_constraint trace));
  fin;
  (cty, cty')

soit make_method loc cl_num expr =
  soit ouvre Ast_helper dans
  soit mkid s = mkloc s loc dans
  Exp.fun_ ~loc:expr.pexp_loc "" None
    (Pat.alias ~loc (Pat.var ~loc (mkid "self-*")) (mkid ("self-" ^ cl_num)))
    expr

(*******************************)

soit add_val env loc lab (mut, virt, ty) val_sig =
  soit virt =
    essaie
      soit (mut', virt', ty') = Vars.find lab val_sig dans
      si virt' = Concrete alors virt' sinon virt
    avec Not_found -> virt
  dans
  Vars.add lab (mut, virt, ty) val_sig

soit rec class_type_field env self_type meths
    (fields, val_sig, concr_meths, inher) ctf =
  soit loc = ctf.pctf_loc dans
  soit mkctf desc = { ctf_desc = desc; ctf_loc = loc; ctf_attributes = ctf.pctf_attributes } dans
  filtre ctf.pctf_desc avec
    Pctf_inherit sparent ->
      soit parent = class_type env sparent dans
      soit inher =
        filtre parent.cltyp_type avec
          Cty_constr (p, tl, _) -> (p, tl) :: inher
        | _ -> inher
      dans
      soit (cl_sig, concr_meths, _) =
        inheritance self_type env None concr_meths Concr.empty sparent.pcty_loc
          parent.cltyp_type
      dans
      soit val_sig =
        Vars.fold (add_val env sparent.pcty_loc) cl_sig.csig_vars val_sig dans
      (mkctf (Tctf_inherit parent) :: fields,
       val_sig, concr_meths, inher)

  | Pctf_val (lab, mut, virt, sty) ->
      soit cty = transl_simple_type env faux sty dans
      soit ty = cty.ctyp_type dans
      (mkctf (Tctf_val (lab, mut, virt, cty)) :: fields,
      add_val env ctf.pctf_loc lab (mut, virt, ty) val_sig, concr_meths, inher)

  | Pctf_method (lab, priv, virt, sty)  ->
      soit cty =
        declare_method env meths self_type lab priv sty  ctf.pctf_loc dans
      soit concr_meths =
        filtre virt avec
        | Concrete -> Concr.add lab concr_meths
        | Virtual -> concr_meths
      dans
      (mkctf (Tctf_method (lab, priv, virt, cty)) :: fields,
        val_sig, concr_meths, inher)

  | Pctf_constraint (sty, sty') ->
      soit (cty, cty') = type_constraint env sty sty'  ctf.pctf_loc dans
      (mkctf (Tctf_constraint (cty, cty')) :: fields,
        val_sig, concr_meths, inher)

  | Pctf_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))

et class_signature env {pcsig_self=sty; pcsig_fields=sign} =
  soit meths = ref Meths.empty dans
  soit self_cty = transl_simple_type env faux sty dans
  soit self_cty = { self_cty avec
    ctyp_type = Ctype.expand_head env self_cty.ctyp_type } dans
  soit self_type =  self_cty.ctyp_type dans

  (* Check that the binder is a correct type, and introduce a dummy
     method preventing self type from being closed. *)
  soit dummy_obj = Ctype.newvar () dans
  Ctype.unify env (Ctype.filter_method env dummy_method Private dummy_obj)
    (Ctype.newty (Ttuple []));
  début essaie
    Ctype.unify env self_type dummy_obj
  avec Ctype.Unify _ ->
    raise(Error(sty.ptyp_loc, env, Pattern_type_clash self_type))
  fin;

  (* Class type fields *)
  soit (fields, val_sig, concr_meths, inher) =
    List.fold_left (class_type_field env self_type meths)
      ([], Vars.empty, Concr.empty, [])
      sign
  dans
  soit cty =   {csig_self = self_type;
   csig_vars = val_sig;
   csig_concr = concr_meths;
   csig_inher = inher}
  dans
  { csig_self = self_cty;
    csig_fields = fields;
    csig_type = cty;
    }

et class_type env scty =
  soit cltyp desc typ =
    {
     cltyp_desc = desc;
     cltyp_type = typ;
     cltyp_loc = scty.pcty_loc;
     cltyp_env = env;
     cltyp_attributes = scty.pcty_attributes;
    }
  dans
  filtre scty.pcty_desc avec
    Pcty_constr (lid, styl) ->
      soit (path, decl) = Typetexp.find_class_type env scty.pcty_loc lid.txt dans
      si Path.same decl.clty_path unbound_class alors
        raise(Error(scty.pcty_loc, env, Unbound_class_type_2 lid.txt));
      soit (params, clty) =
        Ctype.instance_class decl.clty_params decl.clty_type
      dans
      si List.length params <> List.length styl alors
        raise(Error(scty.pcty_loc, env,
                    Parameter_arity_mismatch (lid.txt, List.length params,
                                                   List.length styl)));
      soit ctys = List.map2
        (fonc sty ty ->
          soit cty' = transl_simple_type env faux sty dans
          soit ty' = cty'.ctyp_type dans
          début
           essaie Ctype.unify env ty' ty avec Ctype.Unify trace ->
                  raise(Error(sty.ptyp_loc, env, Parameter_mismatch trace))
            fin;
            cty'
        )       styl params
      dans
      soit typ = Cty_constr (path, params, clty) dans
      cltyp (Tcty_constr ( path, lid , ctys)) typ

  | Pcty_signature pcsig ->
      soit clsig = class_signature env pcsig dans
      soit typ = Cty_signature clsig.csig_type dans
      cltyp (Tcty_signature clsig) typ

  | Pcty_arrow (l, sty, scty) ->
      soit cty = transl_simple_type env faux sty dans
      soit ty = cty.ctyp_type dans
      soit clty = class_type env scty dans
      soit typ = Cty_arrow (l, ty, clty.cltyp_type) dans
      cltyp (Tcty_arrow (l, cty, clty)) typ
  | Pcty_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))

soit class_type env scty =
  delayed_meth_specs := [];
  soit cty = class_type env scty dans
  List.iter Lazy.force (List.rev !delayed_meth_specs);
  delayed_meth_specs := [];
  cty

(*******************************)

soit rec class_field self_loc cl_num self_type meths vars
    (val_env, met_env, par_env, fields, concr_meths, warn_vals, inher,
     local_meths, local_vals)
  cf =
  soit loc = cf.pcf_loc dans
  soit mkcf desc = { cf_desc = desc; cf_loc = loc; cf_attributes = cf.pcf_attributes } dans
  filtre cf.pcf_desc avec
    Pcf_inherit (ovf, sparent, super) ->
      soit parent = class_expr cl_num val_env par_env sparent dans
      soit inher =
        filtre parent.cl_type avec
          Cty_constr (p, tl, _) -> (p, tl) :: inher
        | _ -> inher
      dans
      soit (cl_sig, concr_meths, warn_vals) =
        inheritance self_type val_env (Some ovf) concr_meths warn_vals
          sparent.pcl_loc parent.cl_type
      dans
      (* Variables *)
      soit (val_env, met_env, par_env, inh_vars) =
        Vars.fold
          (fonc lab info (val_env, met_env, par_env, inh_vars) ->
             soit mut, vr, ty = info dans
             soit (id, val_env, met_env, par_env) =
               enter_val cl_num vars vrai lab mut vr ty val_env met_env par_env
                 sparent.pcl_loc
             dans
             (val_env, met_env, par_env, (lab, id) :: inh_vars))
          cl_sig.csig_vars (val_env, met_env, par_env, [])
      dans
      (* Inherited concrete methods *)
      soit inh_meths =
        Concr.fold (fonc lab rem -> (lab, Ident.create lab)::rem)
          cl_sig.csig_concr []
      dans
      (* Super *)
      soit (val_env, met_env, par_env) =
        filtre super avec
          None ->
            (val_env, met_env, par_env)
        | Some name ->
            soit (id, val_env, met_env, par_env) =
              enter_met_env ~check:(fonc s -> Warnings.Unused_ancestor s)
                sparent.pcl_loc name (Val_anc (inh_meths, cl_num)) self_type
                val_env met_env par_env
            dans
            (val_env, met_env, par_env)
      dans
      (val_env, met_env, par_env,
       paresseux (mkcf (Tcf_inherit (ovf, parent, super, inh_vars, inh_meths)))
       :: fields,
       concr_meths, warn_vals, inher, local_meths, local_vals)

  | Pcf_val (lab, mut, Cfk_virtual styp) ->
      si !Clflags.principal alors Ctype.begin_def ();
      soit cty = Typetexp.transl_simple_type val_env faux styp dans
      soit ty = cty.ctyp_type dans
      si !Clflags.principal alors début
        Ctype.end_def ();
        Ctype.generalize_structure ty
      fin;
      soit (id, val_env, met_env', par_env) =
        enter_val cl_num vars faux lab.txt mut Virtual ty
          val_env met_env par_env loc
      dans
      (val_env, met_env', par_env,
       paresseux (mkcf (Tcf_val (lab, mut, id, Tcfk_virtual cty,
                            met_env == met_env')))
             :: fields,
             concr_meths, warn_vals, inher, local_meths, local_vals)

  | Pcf_val (lab, mut, Cfk_concrete (ovf, sexp)) ->
      si Concr.mem lab.txt local_vals alors
        raise(Error(loc, val_env, Duplicate ("variable d'instance", lab.txt)));
      si Concr.mem lab.txt warn_vals alors début
        si ovf = Fresh alors
          Location.prerr_warning lab.loc
            (Warnings.Instance_variable_override[lab.txt])
      fin sinon début
        si ovf = Override alors
          raise(Error(loc, val_env,
                      No_overriding ("variable d'instance", lab.txt)))
      fin;
      si !Clflags.principal alors Ctype.begin_def ();
      soit exp =
        essaie type_exp val_env sexp avec Ctype.Unify [(ty, _)] ->
          raise(Error(loc, val_env, Make_nongen_seltype ty))
      dans
      si !Clflags.principal alors début
        Ctype.end_def ();
        Ctype.generalize_structure exp.exp_type
       fin;
      soit (id, val_env, met_env', par_env) =
        enter_val cl_num vars faux lab.txt mut Concrete exp.exp_type
          val_env met_env par_env loc
      dans
      (val_env, met_env', par_env,
       paresseux (mkcf (Tcf_val (lab, mut, id,
                            Tcfk_concrete (ovf, exp), met_env == met_env')))
       :: fields,
       concr_meths, Concr.add lab.txt warn_vals, inher, local_meths,
       Concr.add lab.txt local_vals)

  | Pcf_method (lab, priv, Cfk_virtual sty) ->
      soit cty = virtual_method val_env meths self_type lab.txt priv sty loc dans
      (val_env, met_env, par_env,
        paresseux (mkcf(Tcf_method (lab, priv, Tcfk_virtual cty)))
       ::fields,
        concr_meths, warn_vals, inher, local_meths, local_vals)

  | Pcf_method (lab, priv, Cfk_concrete (ovf, expr))  ->
      soit expr =
        filtre expr.pexp_desc avec
        | Pexp_poly _ -> expr
        | _ -> Ast_helper.Exp.poly ~loc:expr.pexp_loc expr None
      dans
      si Concr.mem lab.txt local_meths alors
        raise(Error(loc, val_env, Duplicate ("méthode", lab.txt)));
      si Concr.mem lab.txt concr_meths alors début
        si ovf = Fresh alors
          Location.prerr_warning loc (Warnings.Method_override [lab.txt])
      fin sinon début
        si ovf = Override alors
          raise(Error(loc, val_env, No_overriding("méthode", lab.txt)))
      fin;
      soit (_, ty) =
        Ctype.filter_self_method val_env lab.txt priv meths self_type
      dans
      début essaie filtre expr.pexp_desc avec
        Pexp_poly (sbody, sty) ->
          début filtre sty avec None -> ()
                | Some sty ->
                    soit sty = Ast_helper.Typ.force_poly sty dans
                    soit cty' = Typetexp.transl_simple_type val_env faux sty dans
                    soit ty' = cty'.ctyp_type dans
              Ctype.unify val_env ty' ty
          fin;
          début filtre (Ctype.repr ty).desc avec
            Tvar _ ->
              soit ty' = Ctype.newvar () dans
              Ctype.unify val_env (Ctype.newty (Tpoly (ty', []))) ty;
              Ctype.unify val_env (type_approx val_env sbody) ty'
          | Tpoly (ty1, tl) ->
              soit _, ty1' = Ctype.instance_poly faux tl ty1 dans
              soit ty2 = type_approx val_env sbody dans
              Ctype.unify val_env ty2 ty1'
          | _ -> affirme faux
          fin
      | _ -> affirme faux
      avec Ctype.Unify trace ->
        raise(Error(loc, val_env,
                    Field_type_mismatch ("méthode", lab.txt, trace)))
      fin;
      soit meth_expr = make_method self_loc cl_num expr dans
      (* backup variables for Pexp_override *)
      soit vars_local = !vars dans

      soit field =
        paresseux début
          soit meth_type =
            Btype.newgenty (Tarrow("", self_type, ty, Cok)) dans
          Ctype.raise_nongen_level ();
          vars := vars_local;
          soit texp = type_expect met_env meth_expr meth_type dans
          Ctype.end_def ();
          mkcf (Tcf_method (lab, priv, Tcfk_concrete (ovf, texp)))
        fin dans
      (val_env, met_env, par_env, field::fields,
       Concr.add lab.txt concr_meths, warn_vals, inher,
       Concr.add lab.txt local_meths, local_vals)

  | Pcf_constraint (sty, sty') ->
      soit (cty, cty') = type_constraint val_env sty sty' loc dans
      (val_env, met_env, par_env,
        paresseux (mkcf (Tcf_constraint (cty, cty'))) :: fields,
        concr_meths, warn_vals, inher, local_meths, local_vals)

  | Pcf_initializer expr ->
      soit expr = make_method self_loc cl_num expr dans
      soit vars_local = !vars dans
      soit field =
        paresseux début
          Ctype.raise_nongen_level ();
          soit meth_type =
            Ctype.newty
              (Tarrow ("", self_type,
                       Ctype.instance_def Predef.type_unit, Cok)) dans
          vars := vars_local;
          soit texp = type_expect met_env expr meth_type dans
          Ctype.end_def ();
          mkcf (Tcf_initializer texp)
        fin dans
      (val_env, met_env, par_env, field::fields, concr_meths, warn_vals,
       inher, local_meths, local_vals)

  | Pcf_extension (s, _arg) ->
      raise (Error (s.loc, val_env, Extension s.txt))

et class_structure cl_num final val_env met_env loc
  { pcstr_self = spat; pcstr_fields = str } =
  (* Environment for substructures *)
  soit par_env = met_env dans

  (* Location of self. Used for locations of self arguments *)
  soit self_loc = {spat.ppat_loc avec Location.loc_ghost = vrai} dans

  (* Self type, with a dummy method preventing it from being closed/escaped. *)
  soit self_type = Ctype.newvar () dans
  Ctype.unify val_env
    (Ctype.filter_method val_env dummy_method Private self_type)
    (Ctype.newty (Ttuple []));

  (* Private self is used for private method calls *)
  soit private_self = si final alors Ctype.newvar () sinon self_type dans

  (* Self binder *)
  soit (pat, meths, vars, val_env, meth_env, par_env) =
    type_self_pattern cl_num private_self val_env met_env par_env spat
  dans
  soit public_self = pat.pat_type dans

  (* Check that the binder has a correct type *)
  soit ty =
    si final alors Ctype.newty (Tobject (Ctype.newvar(), ref None))
    sinon self_type dans
  début essaie Ctype.unify val_env public_self ty avec
    Ctype.Unify _ ->
      raise(Error(spat.ppat_loc, val_env, Pattern_type_clash public_self))
  fin;
  soit get_methods ty =
    (fst (Ctype.flatten_fields
            (Ctype.object_fields (Ctype.expand_head val_env ty)))) dans
  si final alors début
    (* Copy known information to still empty self_type *)
    List.iter
      (fonc (lab,kind,ty) ->
        soit k =
          si Btype.field_kind_repr kind = Fpresent alors Public sinon Private dans
        essaie Ctype.unify val_env ty
            (Ctype.filter_method val_env lab k self_type)
        avec _ -> affirme faux)
      (get_methods public_self)
  fin;

  (* Typing of class fields *)
  soit (_, _, _, fields, concr_meths, _, inher, _local_meths, _local_vals) =
    List.fold_left (class_field self_loc cl_num self_type meths vars)
      (val_env, meth_env, par_env, [], Concr.empty, Concr.empty, [],
       Concr.empty, Concr.empty)
      str
  dans
  Ctype.unify val_env self_type (Ctype.newvar ());
  soit sign =
    {csig_self = public_self;
     csig_vars = Vars.map (fonc (id, mut, vr, ty) -> (mut, vr, ty)) !vars;
     csig_concr = concr_meths;
      csig_inher = inher} dans
  soit methods = get_methods self_type dans
  soit priv_meths =
    List.filter (fonc (_,kind,_) -> Btype.field_kind_repr kind <> Fpresent)
      methods dans
  si final alors début
    (* Unify private_self and a copy of self_type. self_type will not
       be modified after this point *)
    Ctype.close_object self_type;
    soit mets = virtual_methods {sign avec csig_self = self_type} dans
    soit vals =
      Vars.fold
        (fonc name (mut, vr, ty) l -> si vr = Virtual alors name :: l sinon l)
        sign.csig_vars [] dans
    si mets <> [] || vals <> [] alors
      raise(Error(loc, val_env, Virtual_class(vrai, final, mets, vals)));
    soit self_methods =
      List.fold_right
        (fonc (lab,kind,ty) rem ->
          si lab = dummy_method alors
            (* allow public self and private self to be unified *)
            filtre Btype.field_kind_repr kind avec
              Fvar r -> Btype.set_kind r Fabsent; rem
            | _ -> rem
          sinon
            Ctype.newty(Tfield(lab, Btype.copy_kind kind, ty, rem)))
        methods (Ctype.newty Tnil) dans
    début essaie
      Ctype.unify val_env private_self
        (Ctype.newty (Tobject(self_methods, ref None)));
      Ctype.unify val_env public_self self_type
    avec Ctype.Unify trace -> raise(Error(loc, val_env, Final_self_clash trace))
    fin;
  fin;

  (* Typing of method bodies *)
  si !Clflags.principal alors
    List.iter (fonc (_,_,ty) -> Ctype.generalize_spine ty) methods;
  soit fields = List.map Lazy.force (List.rev fields) dans
  si !Clflags.principal alors
    List.iter (fonc (_,_,ty) -> Ctype.unify val_env ty (Ctype.newvar ()))
      methods;
  soit meths = Meths.map (fonction (id, ty) -> id) !meths dans

  (* Check for private methods made public *)
  soit pub_meths' =
    List.filter (fonc (_,kind,_) -> Btype.field_kind_repr kind = Fpresent)
      (get_methods public_self) dans
  soit names = List.map (fonc (x,_,_) -> x) dans
  soit l1 = names priv_meths et l2 = names pub_meths' dans
  soit added = List.filter (fonc x -> List.mem x l1) l2 dans
  si added <> [] alors
    Location.prerr_warning loc (Warnings.Implicit_public_methods added);
  soit sign = si final alors sign sinon
      {sign avec csig_self = Ctype.expand_head val_env public_self} dans
  {
    cstr_self = pat;
    cstr_fields = fields;
    cstr_type = sign;
    cstr_meths = meths}, sign (* redondant, since already in cstr_type *)

et class_expr cl_num val_env met_env scl =
  filtre scl.pcl_desc avec
    Pcl_constr (lid, styl) ->
      soit (path, decl) = Typetexp.find_class val_env scl.pcl_loc lid.txt dans
      si Path.same decl.cty_path unbound_class alors
        raise(Error(scl.pcl_loc, val_env, Unbound_class_2 lid.txt));
      soit tyl = List.map
          (fonc sty -> transl_simple_type val_env faux sty)
          styl
      dans
      soit (params, clty) =
        Ctype.instance_class decl.cty_params decl.cty_type
      dans
      soit clty' = abbreviate_class_type path params clty dans
      si List.length params <> List.length tyl alors
        raise(Error(scl.pcl_loc, val_env,
                    Parameter_arity_mismatch (lid.txt, List.length params,
                                                   List.length tyl)));
      List.iter2
        (fonc cty' ty ->
          soit ty' = cty'.ctyp_type dans
           essaie Ctype.unify val_env ty' ty avec Ctype.Unify trace ->
             raise(Error(cty'.ctyp_loc, val_env, Parameter_mismatch trace)))
        tyl params;
      soit cl =
        rc {cl_desc = Tcl_ident (path, lid, tyl);
            cl_loc = scl.pcl_loc;
            cl_type = clty';
            cl_env = val_env;
            cl_attributes = scl.pcl_attributes;
           }
      dans
      soit (vals, meths, concrs) = extract_constraints clty dans
      rc {cl_desc = Tcl_constraint (cl, None, vals, meths, concrs);
          cl_loc = scl.pcl_loc;
          cl_type = clty';
          cl_env = val_env;
          cl_attributes = []; (* attributes are kept on the inner cl node *)
         }
  | Pcl_structure cl_str ->
      soit (desc, ty) =
        class_structure cl_num faux val_env met_env scl.pcl_loc cl_str dans
      rc {cl_desc = Tcl_structure desc;
          cl_loc = scl.pcl_loc;
          cl_type = Cty_signature ty;
          cl_env = val_env;
          cl_attributes = scl.pcl_attributes;
         }
  | Pcl_fun (l, Some default, spat, sbody) ->
      soit loc = default.pexp_loc dans
      soit ouvre Ast_helper dans
      soit scases = [
        Exp.case
          (Pat.construct ~loc
             (mknoloc (Longident.(Ldot (Lident "*predef*", "Some"))))
             (Some (Pat.var ~loc (mknoloc "*sth*"))))
          (Exp.ident ~loc (mknoloc (Longident.Lident "*sth*")));

        Exp.case
          (Pat.construct ~loc
             (mknoloc (Longident.(Ldot (Lident "*predef*", "None"))))
             None)
          default;
       ]
      dans
      soit smatch =
        Exp.match_ ~loc (Exp.ident ~loc (mknoloc (Longident.Lident "*opt*")))
          scases
      dans
      soit sfun =
        Cl.fun_ ~loc:scl.pcl_loc
          l None
          (Pat.var ~loc (mknoloc "*opt*"))
          (Cl.let_ ~loc:scl.pcl_loc Nonrecursive [Vb.mk spat smatch] sbody)
          (* Note: we don't put the '#default' attribute, as it
             is not detected for class-level let bindings.  See #5975.*)
      dans
      class_expr cl_num val_env met_env sfun
  | Pcl_fun (l, None, spat, scl') ->
      si !Clflags.principal alors Ctype.begin_def ();
      soit (pat, pv, val_env', met_env) =
        Typecore.type_class_arg_pattern cl_num val_env met_env l spat
      dans
      si !Clflags.principal alors début
        Ctype.end_def ();
        iter_pattern (fonc {pat_type=ty} -> Ctype.generalize_structure ty) pat
      fin;
      soit pv =
        List.map
          début fonc (id, id_loc, id', ty) ->
            soit path = Pident id' dans
            (* do not mark the value as being used *)
            soit vd = Env.find_value path val_env' dans
            (id, id_loc,
             {exp_desc =
              Texp_ident(path, mknoloc (Longident.Lident (Ident.name id)), vd);
              exp_loc = Location.none; exp_extra = [];
              exp_type = Ctype.instance val_env' vd.val_type;
              exp_attributes = []; (* check *)
              exp_env = val_env'})
          fin
          pv
      dans
      soit not_function = fonction
          Cty_arrow _ -> faux
        | _ -> vrai
      dans
      soit partial =
        Parmatch.check_partial pat.pat_loc
          [{c_lhs=pat;
            c_guard=None;
            c_rhs = (* Dummy expression *)
            {exp_desc = Texp_constant (Asttypes.Const_int 1);
             exp_loc = Location.none; exp_extra = [];
             exp_type = Ctype.none;
             exp_attributes = [];
             exp_env = Env.empty }}]
      dans
      Ctype.raise_nongen_level ();
      soit cl = class_expr cl_num val_env' met_env scl' dans
      Ctype.end_def ();
      si Btype.is_optional l && not_function cl.cl_type alors
        Location.prerr_warning pat.pat_loc
          Warnings.Unerasable_optional_argument;
      rc {cl_desc = Tcl_fun (l, pat, pv, cl, partial);
          cl_loc = scl.pcl_loc;
          cl_type = Cty_arrow
            (l, Ctype.instance_def pat.pat_type, cl.cl_type);
          cl_env = val_env;
          cl_attributes = scl.pcl_attributes;
         }
  | Pcl_apply (scl', sargs) ->
      si !Clflags.principal alors Ctype.begin_def ();
      soit cl = class_expr cl_num val_env met_env scl' dans
      si !Clflags.principal alors début
        Ctype.end_def ();
        generalize_class_type faux cl.cl_type;
      fin;
      soit rec nonopt_labels ls ty_fun =
        filtre ty_fun avec
        | Cty_arrow (l, _, ty_res) ->
            si Btype.is_optional l alors nonopt_labels ls ty_res
            sinon nonopt_labels (l::ls) ty_res
        | _    -> ls
      dans
      soit ignore_labels =
        !Clflags.classic ||
        soit labels = nonopt_labels [] cl.cl_type dans
        List.length labels = List.length sargs &&
        List.for_all (fonc (l,_) -> l = "") sargs &&
        List.exists (fonc l -> l <> "") labels &&
        début
          Location.prerr_warning cl.cl_loc Warnings.Labels_omitted;
          vrai
        fin
      dans
      soit rec type_args args omitted ty_fun ty_fun0 sargs more_sargs =
        filtre ty_fun, ty_fun0 avec
        | Cty_arrow (l, ty, ty_fun), Cty_arrow (_, ty0, ty_fun0)
          quand sargs <> [] || more_sargs <> [] ->
            soit name = Btype.label_name l
            et optional =
              si Btype.is_optional l alors Optional sinon Required dans
            soit sargs, more_sargs, arg =
              si ignore_labels && not (Btype.is_optional l) alors début
                filtre sargs, more_sargs avec
                  (l', sarg0)::_, _ ->
                    raise(Error(sarg0.pexp_loc, val_env, Apply_wrong_label l'))
                | _, (l', sarg0)::more_sargs ->
                    si l <> l' && l' <> "" alors
                      raise(Error(sarg0.pexp_loc, val_env,
                                  Apply_wrong_label l'))
                    sinon ([], more_sargs,
                          Some (type_argument val_env sarg0 ty ty0))
                | _ ->
                    affirme faux
              fin sinon essaie
                soit (l', sarg0, sargs, more_sargs) =
                  essaie
                    soit (l', sarg0, sargs1, sargs2) =
                      Btype.extract_label name sargs
                    dans (l', sarg0, sargs1 @ sargs2, more_sargs)
                  avec Not_found ->
                    soit (l', sarg0, sargs1, sargs2) =
                      Btype.extract_label name more_sargs
                    dans (l', sarg0, sargs @ sargs1, sargs2)
                dans
                si optional = Required && Btype.is_optional l' alors
                  Location.prerr_warning sarg0.pexp_loc
                    (Warnings.Nonoptional_label l);
                sargs, more_sargs,
                si optional = Required || Btype.is_optional l' alors
                  Some (type_argument val_env sarg0 ty ty0)
                sinon
                  soit ty' = extract_option_type val_env ty
                  et ty0' = extract_option_type val_env ty0 dans
                  soit arg = type_argument val_env sarg0 ty' ty0' dans
                  Some (option_some arg)
              avec Not_found ->
                sargs, more_sargs,
                si Btype.is_optional l &&
                  (List.mem_assoc "" sargs || List.mem_assoc "" more_sargs)
                alors
                  Some (option_none ty0 Location.none)
                sinon None
            dans
            soit omitted = si arg = None alors (l,ty0) :: omitted sinon omitted dans
            type_args ((l,arg,optional)::args) omitted ty_fun ty_fun0
              sargs more_sargs
        | _ ->
            filtre sargs @ more_sargs avec
              (l, sarg0)::_ ->
                si omitted <> [] alors
                  raise(Error(sarg0.pexp_loc, val_env, Apply_wrong_label l))
                sinon
                  raise(Error(cl.cl_loc, val_env, Cannot_apply cl.cl_type))
            | [] ->
                (List.rev args,
                 List.fold_left
                   (fonc ty_fun (l,ty) -> Cty_arrow(l,ty,ty_fun))
                   ty_fun0 omitted)
      dans
      soit (args, cty) =
        soit (_, ty_fun0) = Ctype.instance_class [] cl.cl_type dans
        si ignore_labels alors
          type_args [] [] cl.cl_type ty_fun0 [] sargs
        sinon
          type_args [] [] cl.cl_type ty_fun0 sargs []
      dans
      rc {cl_desc = Tcl_apply (cl, args);
          cl_loc = scl.pcl_loc;
          cl_type = cty;
          cl_env = val_env;
          cl_attributes = scl.pcl_attributes;
         }
  | Pcl_let (rec_flag, sdefs, scl') ->
      soit (defs, val_env) =
        essaie
          Typecore.type_let val_env rec_flag sdefs None
        avec Ctype.Unify [(ty, _)] ->
          raise(Error(scl.pcl_loc, val_env, Make_nongen_seltype ty))
      dans
      soit (vals, met_env) =
        List.fold_right
          (fonc (id, id_loc) (vals, met_env) ->
             soit path = Pident id dans
             (* do not mark the value as used *)
             soit vd = Env.find_value path val_env dans
             Ctype.begin_def ();
             soit expr =
               {exp_desc =
                Texp_ident(path, mknoloc(Longident.Lident (Ident.name id)),vd);
                exp_loc = Location.none; exp_extra = [];
                exp_type = Ctype.instance val_env vd.val_type;
                exp_attributes = [];
                exp_env = val_env;
               }
             dans
             Ctype.end_def ();
             Ctype.generalize expr.exp_type;
             soit desc =
               {val_type = expr.exp_type; val_kind = Val_ivar (Immutable,
                                                               cl_num);
                val_attributes = [];
                Types.val_loc = vd.Types.val_loc;
               }
             dans
             soit id' = Ident.create (Ident.name id) dans
             ((id', id_loc, expr)
              :: vals,
              Env.add_value id' desc met_env))
          (let_bound_idents_with_loc defs)
          ([], met_env)
      dans
      soit cl = class_expr cl_num val_env met_env scl' dans
      rc {cl_desc = Tcl_let (rec_flag, defs, vals, cl);
          cl_loc = scl.pcl_loc;
          cl_type = cl.cl_type;
          cl_env = val_env;
          cl_attributes = scl.pcl_attributes;
         }
  | Pcl_constraint (scl', scty) ->
      Ctype.begin_class_def ();
      soit context = Typetexp.narrow () dans
      soit cl = class_expr cl_num val_env met_env scl' dans
      Typetexp.widen context;
      soit context = Typetexp.narrow () dans
      soit clty = class_type val_env scty dans
      Typetexp.widen context;
      Ctype.end_def ();

      limited_generalize (Ctype.row_variable (Ctype.self_type cl.cl_type))
          cl.cl_type;
      limited_generalize (Ctype.row_variable (Ctype.self_type clty.cltyp_type))
        clty.cltyp_type;

      début filtre
        Includeclass.class_types val_env cl.cl_type clty.cltyp_type
      avec
        []    -> ()
      | error -> raise(Error(cl.cl_loc, val_env, Class_match_failure error))
      fin;
      soit (vals, meths, concrs) = extract_constraints clty.cltyp_type dans
      rc {cl_desc = Tcl_constraint (cl, Some clty, vals, meths, concrs);
          cl_loc = scl.pcl_loc;
          cl_type = snd (Ctype.instance_class [] clty.cltyp_type);
          cl_env = val_env;
          cl_attributes = scl.pcl_attributes;
         }
  | Pcl_extension (s, _arg) ->
      raise (Error (s.loc, val_env, Extension s.txt))

(*******************************)

(* Approximate the type of the constructor to allow recursive use *)
(* of optional parameters                                         *)

soit var_option = Predef.type_option (Btype.newgenvar ())

soit rec approx_declaration cl =
  filtre cl.pcl_desc avec
    Pcl_fun (l, _, _, cl) ->
      soit arg =
        si Btype.is_optional l alors Ctype.instance_def var_option
        sinon Ctype.newvar () dans
      Ctype.newty (Tarrow (l, arg, approx_declaration cl, Cok))
  | Pcl_let (_, _, cl) ->
      approx_declaration cl
  | Pcl_constraint (cl, _) ->
      approx_declaration cl
  | _ -> Ctype.newvar ()

soit rec approx_description ct =
  filtre ct.pcty_desc avec
    Pcty_arrow (l, _, ct) ->
      soit arg =
        si Btype.is_optional l alors Ctype.instance_def var_option
        sinon Ctype.newvar () dans
      Ctype.newty (Tarrow (l, arg, approx_description ct, Cok))
  | _ -> Ctype.newvar ()

(*******************************)

soit temp_abbrev loc env id arity =
  soit params = ref [] dans
  pour _i = 1 à arity faire
    params := Ctype.newvar () :: !params
  fait;
  soit ty = Ctype.newobj (Ctype.newvar ()) dans
  soit env =
    Env.add_type ~check:vrai id
      {type_params = !params;
       type_arity = arity;
       type_kind = Type_abstract;
       type_private = Public;
       type_manifest = Some ty;
       type_variance = Misc.replicate_list Variance.full arity;
       type_newtype_level = None;
       type_loc = loc;
       type_attributes = []; (* or keep attrs from the class decl? *)
      }
      env
  dans
  (!params, ty, env)

soit initial_env define_class approx
    (res, env) (cl, id, ty_id, obj_id, cl_id) =
  (* Temporary abbreviations *)
  soit arity = List.length cl.pci_params dans
  soit (obj_params, obj_ty, env) = temp_abbrev cl.pci_loc env obj_id arity dans
  soit (cl_params, cl_ty, env) = temp_abbrev cl.pci_loc env cl_id arity dans

  (* Temporary type for the class constructor *)
  soit constr_type = approx cl.pci_expr dans
  si !Clflags.principal alors Ctype.generalize_spine constr_type;
  soit dummy_cty =
    Cty_signature
      { csig_self = Ctype.newvar ();
        csig_vars = Vars.empty;
        csig_concr = Concr.empty;
        csig_inher = [] }
  dans
  soit dummy_class =
    {Types.cty_params = [];             (* Dummy value *)
     cty_variance = [];
     cty_type = dummy_cty;        (* Dummy value *)
     cty_path = unbound_class;
     cty_new =
       début filtre cl.pci_virt avec
       | Virtual  -> None
       | Concrete -> Some constr_type
       fin;
     cty_loc = Location.none;
     cty_attributes = [];
    }
  dans
  soit env =
    Env.add_cltype ty_id
      {clty_params = [];            (* Dummy value *)
       clty_variance = [];
       clty_type = dummy_cty;       (* Dummy value *)
       clty_path = unbound_class;
       clty_loc = Location.none;
       clty_attributes = [];
      }
      (
        si define_class alors
          Env.add_class id dummy_class env
        sinon
          env
      )
  dans
  ((cl, id, ty_id,
    obj_id, obj_params, obj_ty,
    cl_id, cl_params, cl_ty,
    constr_type, dummy_class)::res,
   env)

soit class_infos define_class kind
    (cl, id, ty_id,
     obj_id, obj_params, obj_ty,
     cl_id, cl_params, cl_ty,
     constr_type, dummy_class)
    (res, env) =

  reset_type_variables ();
  Ctype.begin_class_def ();

  (* Introduce class parameters *)
  soit params =
    essaie
      List.map (fonc (x, _v) -> enter_type_variable x) cl.pci_params
    avec Already_bound loc ->
      raise(Error(loc, env, Repeated_parameter))
  dans

  (* Allow self coercions (only for class declarations) *)
  soit coercion_locs = ref [] dans

  (* Type the class expression *)
  soit (expr, typ) =
    essaie
      Typecore.self_coercion :=
        (Path.Pident obj_id, coercion_locs) :: !Typecore.self_coercion;
      soit res = kind env cl.pci_expr dans
      Typecore.self_coercion := List.tl !Typecore.self_coercion;
      res
    avec exn ->
      Typecore.self_coercion := []; raise exn
  dans

  Ctype.end_def ();

  soit sty = Ctype.self_type typ dans

  (* First generalize the type of the dummy method (cf PR#6123) *)
  soit (fields, _) = Ctype.flatten_fields (Ctype.object_fields sty) dans
  List.iter (fonc (met, _, ty) -> si met = dummy_method alors Ctype.generalize ty)
    fields;
  (* Generalize the row variable *)
  soit rv = Ctype.row_variable sty dans
  List.iter (Ctype.limited_generalize rv) params;
  limited_generalize rv typ;

  (* Check the abbreviation for the object type *)
  soit (obj_params', obj_type) = Ctype.instance_class params typ dans
  soit constr = Ctype.newconstr (Path.Pident obj_id) obj_params dans
  début
    soit ty = Ctype.self_type obj_type dans
    Ctype.hide_private_methods ty;
    Ctype.close_object ty;
    début essaie
      List.iter2 (Ctype.unify env) obj_params obj_params'
    avec Ctype.Unify _ ->
      raise(Error(cl.pci_loc, env,
            Bad_parameters (obj_id, constr,
                            Ctype.newconstr (Path.Pident obj_id)
                                            obj_params')))
    fin;
    début essaie
      Ctype.unify env ty constr
    avec Ctype.Unify _ ->
      raise(Error(cl.pci_loc, env,
        Abbrev_type_clash (constr, ty, Ctype.expand_head env constr)))
    fin
  fin;

  (* Check the other temporary abbreviation (#-type) *)
  début
    soit (cl_params', cl_type) = Ctype.instance_class params typ dans
    soit ty = Ctype.self_type cl_type dans
    Ctype.hide_private_methods ty;
    Ctype.set_object_name obj_id (Ctype.row_variable ty) cl_params ty;
    début essaie
      List.iter2 (Ctype.unify env) cl_params cl_params'
    avec Ctype.Unify _ ->
      raise(Error(cl.pci_loc, env,
            Bad_parameters (cl_id,
                            Ctype.newconstr (Path.Pident cl_id)
                                            cl_params,
                            Ctype.newconstr (Path.Pident cl_id)
                                            cl_params')))
    fin;
    début essaie
      Ctype.unify env ty cl_ty
    avec Ctype.Unify _ ->
      soit constr = Ctype.newconstr (Path.Pident cl_id) params dans
      raise(Error(cl.pci_loc, env, Abbrev_type_clash (constr, ty, cl_ty)))
    fin
  fin;

  (* Type of the class constructor *)
  début essaie
    Ctype.unify env
      (constructor_type constr obj_type)
      (Ctype.instance env constr_type)
  avec Ctype.Unify trace ->
    raise(Error(cl.pci_loc, env,
                Constructor_type_mismatch (cl.pci_name.txt, trace)))
  fin;

  (* Class and class type temporary definitions *)
  soit cty_variance = List.map (fonc _ -> Variance.full) params dans
  soit cltydef =
    {clty_params = params; clty_type = class_body typ;
     clty_variance = cty_variance;
     clty_path = Path.Pident obj_id;
     clty_loc = cl.pci_loc;
     clty_attributes = cl.pci_attributes;
    }
  et clty =
    {cty_params = params; cty_type = typ;
     cty_variance = cty_variance;
     cty_path = Path.Pident obj_id;
     cty_new =
       début filtre cl.pci_virt avec
       | Virtual  -> None
       | Concrete -> Some constr_type
       fin;
     cty_loc = cl.pci_loc;
     cty_attributes = cl.pci_attributes;
    }
  dans
  dummy_class.cty_type <- typ;
  soit env =
    Env.add_cltype ty_id cltydef (
    si define_class alors Env.add_class id clty env sinon env)
  dans

  si cl.pci_virt = Concrete alors début
    soit sign = Ctype.signature_of_class_type typ dans
    soit mets = virtual_methods sign dans
    soit vals =
      Vars.fold
        (fonc name (mut, vr, ty) l -> si vr = Virtual alors name :: l sinon l)
        sign.csig_vars [] dans
    si mets <> []  || vals <> [] alors
      raise(Error(cl.pci_loc, env, Virtual_class(define_class, faux, mets, vals)));
  fin;

  (* Misc. *)
  soit arity = Ctype.class_type_arity typ dans
  soit pub_meths =
    soit (fields, _) =
      Ctype.flatten_fields (Ctype.object_fields (Ctype.expand_head env obj_ty))
    dans
    List.map (fonction (lab, _, _) -> lab) fields
  dans

  (* Final definitions *)
  soit (params', typ') = Ctype.instance_class params typ dans
  soit cltydef =
    {clty_params = params'; clty_type = class_body typ';
     clty_variance = cty_variance;
     clty_path = Path.Pident obj_id;
     clty_loc = cl.pci_loc;
     clty_attributes = cl.pci_attributes;
    }
  et clty =
    {cty_params = params'; cty_type = typ';
     cty_variance = cty_variance;
     cty_path = Path.Pident obj_id;
     cty_new =
       début filtre cl.pci_virt avec
       | Virtual  -> None
       | Concrete -> Some (Ctype.instance env constr_type)
       fin;
     cty_loc = cl.pci_loc;
     cty_attributes = cl.pci_attributes;
    }
  dans
  soit obj_abbr =
    {type_params = obj_params;
     type_arity = List.length obj_params;
     type_kind = Type_abstract;
     type_private = Public;
     type_manifest = Some obj_ty;
     type_variance = List.map (fonc _ -> Variance.full) obj_params;
     type_newtype_level = None;
     type_loc = cl.pci_loc;
     type_attributes = []; (* or keep attrs from cl? *)
    }
  dans
  soit (cl_params, cl_ty) =
    Ctype.instance_parameterized_type params (Ctype.self_type typ)
  dans
  Ctype.hide_private_methods cl_ty;
  Ctype.set_object_name obj_id (Ctype.row_variable cl_ty) cl_params cl_ty;
  soit cl_abbr =
    {type_params = cl_params;
     type_arity = List.length cl_params;
     type_kind = Type_abstract;
     type_private = Public;
     type_manifest = Some cl_ty;
     type_variance = List.map (fonc _ -> Variance.full) cl_params;
     type_newtype_level = None;
     type_loc = cl.pci_loc;
     type_attributes = []; (* or keep attrs from cl? *)
    }
  dans
  ((cl, id, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
    arity, pub_meths, List.rev !coercion_locs, expr) :: res,
   env)

soit final_decl env define_class
    (cl, id, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
     arity, pub_meths, coe, expr) =

  début essaie Ctype.collapse_conj_params env clty.cty_params
  avec Ctype.Unify trace ->
    raise(Error(cl.pci_loc, env, Non_collapsable_conjunction (id, clty, trace)))
  fin;

  List.iter Ctype.generalize clty.cty_params;
  generalize_class_type vrai clty.cty_type;
  Misc.may  Ctype.generalize clty.cty_new;
  List.iter Ctype.generalize obj_abbr.type_params;
  Misc.may  Ctype.generalize obj_abbr.type_manifest;
  List.iter Ctype.generalize cl_abbr.type_params;
  Misc.may  Ctype.generalize cl_abbr.type_manifest;

  si not (closed_class clty) alors
    raise(Error(cl.pci_loc, env, Non_generalizable_class (id, clty)));

  début filtre
    Ctype.closed_class clty.cty_params
      (Ctype.signature_of_class_type clty.cty_type)
  avec
    None        -> ()
  | Some reason ->
      soit printer =
        si define_class
        alors fonction ppf -> Printtyp.class_declaration id ppf clty
        sinon fonction ppf -> Printtyp.cltype_declaration id ppf cltydef
      dans
      raise(Error(cl.pci_loc, env, Unbound_type_var(printer, reason)))
  fin;

  (id, cl.pci_name, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
   arity, pub_meths, coe, expr,
   { ci_loc = cl.pci_loc;
     ci_virt = cl.pci_virt;
     ci_params = cl.pci_params;
(* TODO : check that we have the correct use of identifiers *)
     ci_id_name = cl.pci_name;
     ci_id_class = id;
     ci_id_class_type = ty_id;
     ci_id_object = obj_id;
     ci_id_typesharp = cl_id;
     ci_expr = expr;
     ci_decl = clty;
     ci_type_decl = cltydef;
     ci_attributes = cl.pci_attributes;
 })
(*   (cl.pci_variance, cl.pci_loc)) *)

soit extract_type_decls
    (id, id_loc, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
     arity, pub_meths, coe, expr, required) decls =
  (obj_id, obj_abbr, cl_abbr, clty, cltydef, required) :: decls

soit merge_type_decls
    (id, id_loc, _clty, ty_id, _cltydef, obj_id, _obj_abbr, cl_id, _cl_abbr,
     arity, pub_meths, coe, expr, req) (obj_abbr, cl_abbr, clty, cltydef) =
  (id, id_loc, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
   arity, pub_meths, coe, expr, req)

soit final_env define_class env
    (id, id_loc, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
     arity, pub_meths, coe, expr, req) =
  (* Add definitions after cleaning them *)
  Env.add_type ~check:vrai obj_id
    (Subst.type_declaration Subst.identity obj_abbr) (
  Env.add_type ~check:vrai cl_id
    (Subst.type_declaration Subst.identity cl_abbr) (
  Env.add_cltype ty_id (Subst.cltype_declaration Subst.identity cltydef) (
  si define_class alors
    Env.add_class id (Subst.class_declaration Subst.identity clty) env
  sinon env)))

(* Check that #c is coercible to c if there is a self-coercion *)
soit check_coercions env
    (id, id_loc, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
     arity, pub_meths, coercion_locs, expr, req) =
  début filtre coercion_locs avec [] -> ()
  | loc :: _ ->
      soit cl_ty, obj_ty =
        filtre cl_abbr.type_manifest, obj_abbr.type_manifest avec
          Some cl_ab, Some obj_ab ->
            soit cl_params, cl_ty =
              Ctype.instance_parameterized_type cl_abbr.type_params cl_ab
            et obj_params, obj_ty =
              Ctype.instance_parameterized_type obj_abbr.type_params obj_ab
            dans
            List.iter2 (Ctype.unify env) cl_params obj_params;
            cl_ty, obj_ty
        | _ -> affirme faux
      dans
      début essaie Ctype.subtype env cl_ty obj_ty ()
      avec Ctype.Subtype (tr1, tr2) ->
        raise(Typecore.Error(loc, env, Typecore.Not_subtype(tr1, tr2)))
      fin;
      si not (Ctype.opened_object cl_ty) alors
        raise(Error(loc, env, Cannot_coerce_self obj_ty))
  fin;
  (id, id_loc, clty, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
   arity, pub_meths, req)

(*******************************)

soit type_classes define_class approx kind env cls =
  soit cls =
    List.map
      (fonction cl ->
         (cl,
          Ident.create cl.pci_name.txt, Ident.create cl.pci_name.txt,
          Ident.create cl.pci_name.txt, Ident.create ("#" ^ cl.pci_name.txt)))
      cls
  dans
  Ctype.init_def (Ident.current_time ());
  Ctype.begin_class_def ();
  soit (res, env) =
    List.fold_left (initial_env define_class approx) ([], env) cls
  dans
  soit (res, env) =
    List.fold_right (class_infos define_class kind) res ([], env)
  dans
  Ctype.end_def ();
  soit res = List.rev_map (final_decl env define_class) res dans
  soit decls = List.fold_right extract_type_decls res [] dans
  soit decls = Typedecl.compute_variance_decls env decls dans
  soit res = List.map2 merge_type_decls res decls dans
  soit env = List.fold_left (final_env define_class) env res dans
  soit res = List.map (check_coercions env) res dans
  (res, env)

soit class_num = ref 0
soit class_declaration env sexpr =
  incr class_num;
  soit expr = class_expr (string_of_int !class_num) env env sexpr dans
  (expr, expr.cl_type)

soit class_description env sexpr =
  soit expr = class_type env sexpr dans
  (expr, expr.cltyp_type)

soit class_declarations env cls =
  type_classes vrai approx_declaration class_declaration env cls

soit class_descriptions env cls =
  type_classes vrai approx_description class_description env cls

soit class_type_declarations env cls =
  soit (decl, env) =
    type_classes faux approx_description class_description env cls
  dans
  (List.map
     (fonction
       (_, id_loc, _, ty_id, cltydef, obj_id, obj_abbr, cl_id, cl_abbr,
        _, _, ci) ->
       (ty_id, id_loc, cltydef, obj_id, obj_abbr, cl_id, cl_abbr, ci))
     decl,
   env)

soit rec unify_parents env ty cl =
  filtre cl.cl_desc avec
    Tcl_ident (p, _, _) ->
      début essaie
        soit decl = Env.find_class p env dans
        soit _, body = Ctype.find_cltype_for_path env decl.cty_path dans
        Ctype.unify env ty (Ctype.instance env body)
      avec
        Not_found -> ()
      | exn -> affirme faux
      fin
  | Tcl_structure st -> unify_parents_struct env ty st
  | Tcl_fun (_, _, _, cl, _)
  | Tcl_apply (cl, _)
  | Tcl_let (_, _, _, cl)
  | Tcl_constraint (cl, _, _, _, _) -> unify_parents env ty cl
et unify_parents_struct env ty st =
  List.iter
    (fonction {cf_desc = Tcf_inherit (_, cl, _, _, _)} -> unify_parents env ty cl
      | _ -> ())
    st.cstr_fields

soit type_object env loc s =
  incr class_num;
  soit (desc, sign) =
    class_structure (string_of_int !class_num) vrai env env loc s dans
  soit sty = Ctype.expand_head env sign.csig_self dans
  Ctype.hide_private_methods sty;
  soit (fields, _) = Ctype.flatten_fields (Ctype.object_fields sty) dans
  soit meths = List.map (fonc (s,_,_) -> s) fields dans
  unify_parents_struct env sign.csig_self desc;
  (desc, sign, meths)

soit () =
  Typecore.type_object := type_object

(*******************************)

(* Approximate the class declaration as class ['params] id = object end *)
soit approx_class sdecl =
  soit ouvre Ast_helper dans
  soit self' = Typ.any () dans
  soit clty' = Cty.signature ~loc:sdecl.pci_expr.pcty_loc (Csig.mk self' []) dans
  { sdecl avec pci_expr = clty' }

soit approx_class_declarations env sdecls =
  fst (class_type_declarations env (List.map approx_class sdecls))

(*******************************)

(* Error report *)

ouvre Format

soit report_error env ppf = fonction
  | Repeated_parameter ->
      fprintf ppf "Un paramtre de type apparaît plusieurs fois"
  | Unconsistent_constraint trace ->
      fprintf ppf "Les contraintes de classe ne sont pas consistantes.@.";
      Printtyp.report_unification_error ppf env trace
        (fonc ppf -> fprintf ppf "Type")
        (fonc ppf -> fprintf ppf "n'est pas compatible avec le type")
  | Field_type_mismatch (k, m, trace) ->
      Printtyp.report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "La %s %s@ a le type" k m)
        (fonction ppf ->
           fprintf ppf "mais son type attendu est")
  | Structure_expected clty ->
      fprintf ppf
        "@[Cette expression de classe n'est pas une structure de classe ; elle a le type@ %a@]"
        Printtyp.class_type clty
  | Cannot_apply clty ->
      fprintf ppf
        "Cette expression de classe n'est pas une fonction de classe, elle ne peut pas être appliquée"
  | Apply_wrong_label l ->
      soit mark_label = fonction
        | "" -> "le label de sortie"
        |  l -> sprintf "le label ~%s" l dans
      fprintf ppf "Cet argument ne peut pas être appliqué avec %s" (mark_label l)
  | Pattern_type_clash ty ->
      (* XXX Trace *)
      (* XXX Revoir message d'erreur *)
      Printtyp.reset_and_mark_loops ty;
      fprintf ppf "@[%s@ %a@]"
        "Ce motif ne peut pas se filtrer lui-même : il ne filtre que les valeurs de type"
        Printtyp.type_expr ty
  | Unbound_class_2 cl ->
      fprintf ppf "@[La classe@ %a@ in'est pas encore complètement définie@]"
      Printtyp.longident cl
  | Unbound_class_type_2 cl ->
      fprintf ppf "@[Le type de classe@ %a@ n'est pas encore complètement défini@]"
      Printtyp.longident cl
  | Abbrev_type_clash (abbrev, actual, expected) ->
      (* XXX Afficher une trace ? *)
      Printtyp.reset_and_mark_loops_list [abbrev; actual; expected];
      fprintf ppf "@[L'abréviation@ %a@ s'expend au type@ %a@ \
       mais est utilisé avec le type@ %a@]"
       Printtyp.type_expr abbrev
       Printtyp.type_expr actual
       Printtyp.type_expr expected
  | Constructor_type_mismatch (c, trace) ->
      Printtyp.report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "L'expression \"nouveau %s\" a le type" c)
        (fonction ppf ->
           fprintf ppf "mais est utilisé avec le type")
  | Virtual_class (cl, imm, mets, vals) ->
      soit print_mets ppf mets =
        List.iter (fonction met -> fprintf ppf "@ %s" met) mets dans
      soit missings =
        filtre mets, vals avec
          [], _ -> "des variables"
        | _, [] -> "des méthodes"
        | _ -> "des méthodes et des variables"
      dans
      soit print_msg ppf =
        si imm alors fprintf ppf "Cet objet a %s virtuelles" missings
        sinon si cl alors fprintf ppf "Cette classe devrait être virtuelle"
        sinon fprintf ppf "Ce type de classe devrait être virtuel"
      dans
      soit missings =
        filtre mets, vals avec
          [], _ -> "Les variables"
        | _, [] -> "Les méthodes"
        | _ -> "Les méthodes et les variables"
      dans
      fprintf ppf
        "@[%t.@ @[<2>%s ne sont pas définies :%a@]@]"
        print_msg missings print_mets (mets @ vals)
  | Parameter_arity_mismatch(lid, expected, provided) ->
      fprintf ppf
        "@[Le constructeut de classe %a@ attend %i argument(s) de type,@ \
           mais est appliqué ici à %i argument(s)@]"
        Printtyp.longident lid expected provided
  | Parameter_mismatch trace ->
      Printtyp.report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "Le paramètre de type")
        (fonction ppf ->
           fprintf ppf "ne satisfait pas sa contrainte : il devrait être")
  | Bad_parameters (id, params, cstrs) ->
      Printtyp.reset_and_mark_loops_list [params; cstrs];
      fprintf ppf
        "@[L'abréviation %a@ est utilisée avec les paramètres@ %a@ \
           qui sont incompatibles avec les contraintes@ %a@]"
        Printtyp.ident id Printtyp.type_expr params Printtyp.type_expr cstrs
  | Class_match_failure error ->
      Includeclass.report_error ppf error
  | Unbound_val lab ->
      fprintf ppf "Variable d'instance non liée %s" lab
  | Unbound_type_var (printer, reason) ->
      soit print_common ppf kind ty0 real lab ty =
        soit ty1 =
          si real alors ty0 sinon Btype.newgenty(Tobject(ty0, ref None)) dans
        Printtyp.mark_loops ty1;
        fprintf ppf
          "La %s %s@ a le type@;<1 2>%a@ où@ %a@ n'est pas lié"
            kind lab Printtyp.type_expr ty Printtyp.type_expr ty0
      dans
      soit print_reason ppf = fonction
      | Ctype.CC_Method (ty0, real, lab, ty) ->
          print_common ppf "méthode" ty0 real lab ty
      | Ctype.CC_Value (ty0, real, lab, ty) ->
          print_common ppf "variable d'instance" ty0 real lab ty
      dans
      Printtyp.reset ();
      fprintf ppf
        "@[<v>@[Des variables d'instance ne sont pas liées dans ce type :@;<1 2>%t@]@ \
              @[%a@]@]"
       printer print_reason reason
  | Make_nongen_seltype ty ->
      fprintf ppf
        "@[<v>@[Le type self ne devrait pas apparaître dans le type non générique@;<1 2>\
                %a@]@,\
           Il s'échapperait de la portée de sa classe@]"
        Printtyp.type_scheme ty
  | Non_generalizable_class (id, clty) ->
      fprintf ppf
        "@[Le type de cette classe,@ %a,@ \
           contient des variables de type qui ne peuvent pas être généralisées@]"
        (Printtyp.class_declaration id) clty
  | Cannot_coerce_self ty ->
      fprintf ppf
        "@[Le type de self ne peut pas être coercé au@ \
           type de la classe courante :@ %a.@.\
           Des occurences sont contravariantes@]"
        Printtyp.type_scheme ty
  | Non_collapsable_conjunction (id, clty, trace) ->
      fprintf ppf
        "@[Le type de cette classe,@ %a,@ \
           contient des types conjonctifs non repliables dans les contraintes@]"
        (Printtyp.class_declaration id) clty;
      Printtyp.report_unification_error ppf env trace
        (fonc ppf -> fprintf ppf "Le type")
        (fonc ppf -> fprintf ppf "n'est pas compatible avec le type")
  | Final_self_clash trace ->
      Printtyp.report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "Cet objet doit avoir le type")
        (fonction ppf ->
           fprintf ppf "mais a le type")
  | Mutability_mismatch (lab, mut) ->
      soit mut1, mut2 =
        si mut = Immutable alors "mutable", "immutable"
        sinon "immutable", "mutable" dans
      fprintf ppf
        "@[La variable d'instance est %s;@ elle ne peut pas être redéfinie comme %s@]"
        mut1 mut2
  | No_overriding (_, "") ->
      fprintf ppf "@[Cet héritage ne redéfinit aucune méthode de @ %s@]"
        "la variable d'instance"
  | No_overriding (kind, name) ->
      fprintf ppf "@[La %s `%s'@ n'a pas de définition antérieure@]" kind name
  | Duplicate (kind, name) ->
      fprintf ppf "@[La %s `%s'@ a plusieurs définitions dans cet objet@]"
                    kind name
  | Extension s ->
      fprintf ppf "Extension non interprétée '%s'." s

soit report_error env ppf err =
  Printtyp.wrap_printing_env env (fonc () -> report_error env ppf err)

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, env, err) ->
        Some (Location.error_of_printer loc (report_error env) err)
      | _ ->
        None
    )
