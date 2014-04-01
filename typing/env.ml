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

(* Environment handling *)

ouvre Cmi_format
ouvre Config
ouvre Misc
ouvre Asttypes
ouvre Longident
ouvre Path
ouvre Types
ouvre Btype

soit add_delayed_check_forward = ref (fonc _ -> affirme faux)

soit value_declarations : ((string * Location.t), (unit -> unit)) Hashtbl.t =
  Hashtbl.create 16
    (* This table is used to usage of value declarations.  A declaration is
       identified with its name and location.  The callback attached to a
       declaration is called whenever the value is used explicitly
       (lookup_value) or implicitly (inclusion test between signatures,
       cf Includemod.value_descriptions). *)

soit type_declarations = Hashtbl.create 16

type constructor_usage = Positive | Pattern | Privatize
type constructor_usages =
    {
     modifiable cu_positive: bool;
     modifiable cu_pattern: bool;
     modifiable cu_privatize: bool;
    }
soit add_constructor_usage cu = fonction
  | Positive -> cu.cu_positive <- vrai
  | Pattern -> cu.cu_pattern <- vrai
  | Privatize -> cu.cu_privatize <- vrai
soit constructor_usages () =
  {cu_positive = faux; cu_pattern = faux; cu_privatize = faux}

soit used_constructors :
    (string * Location.t * string, (constructor_usage -> unit)) Hashtbl.t
  = Hashtbl.create 16

soit prefixed_sg = Hashtbl.create 113

type error =
  | Illegal_renaming de string * string * string
  | Inconsistent_import de string * string * string
  | Need_recursive_types de string * string
  | Missing_module de Location.t * Path.t * Path.t

exception Error de error

soit error err = raise (Error err)

module EnvLazy : sig
  type ('a,'b) t

  val force : ('a -> 'b) -> ('a,'b) t -> 'b
  val create : 'a -> ('a,'b) t
  val is_val : ('a,'b) t -> bool

fin  = struct

  type ('a,'b) t = ('a,'b) eval ref

  et ('a,'b) eval =
      Done de 'b
    | Raise de exn
    | Thunk de 'a

  soit force f x =
    filtre !x avec
        Done x -> x
      | Raise e -> raise e
      | Thunk e ->
          essaie
            soit y = f e dans
            x := Done y;
            y
          avec e ->
            x := Raise e;
            raise e

  soit is_val x =
    filtre !x avec Done _ -> vrai | _ -> faux

  soit create x =
    soit x = ref (Thunk x) dans
    x

fin


type summary =
    Env_empty
  | Env_value de summary * Ident.t * value_description
  | Env_type de summary * Ident.t * type_declaration
  | Env_exception de summary * Ident.t * exception_declaration
  | Env_module de summary * Ident.t * module_declaration
  | Env_modtype de summary * Ident.t * modtype_declaration
  | Env_class de summary * Ident.t * class_declaration
  | Env_cltype de summary * Ident.t * class_type_declaration
  | Env_open de summary * Path.t
  | Env_functor_arg de summary * Ident.t

module EnvTbl =
  struct
    (* A table indexed by identifier, with an extra slot to record usage. *)
    type 'a t = ('a * (unit -> unit)) Ident.tbl

    soit empty = Ident.empty
    soit nothing = fonc () -> ()

    soit already_defined s tbl =
      essaie ignore (Ident.find_name s tbl); vrai
      avec Not_found -> faux

    soit add kind slot id x tbl ref_tbl =
      soit slot =
        filtre slot avec
        | None -> nothing
        | Some f ->
          (fonc () ->
             soit s = Ident.name id dans
             f kind s (already_defined s ref_tbl)
          )
      dans
      Ident.add id (x, slot) tbl

    soit add_dont_track id x tbl =
      Ident.add id (x, nothing) tbl

    soit find_same_not_using id tbl =
      fst (Ident.find_same id tbl)

    soit find_same id tbl =
      soit (x, slot) = Ident.find_same id tbl dans
      slot ();
      x

    soit find_name s tbl =
      soit (x, slot) = Ident.find_name s tbl dans
      slot ();
      x

    soit find_all s tbl =
      Ident.find_all s tbl

    soit fold_name f = Ident.fold_name (fonc k (d,_) -> f k d)
    soit keys tbl = Ident.fold_all (fonc k _ accu -> k::accu) tbl []
  fin

type type_descriptions =
    constructor_description list * label_description list

type t = {
  values: (Path.t * value_description) EnvTbl.t;
  constrs: constructor_description EnvTbl.t;
  labels: label_description EnvTbl.t;
  types: (Path.t * (type_declaration * type_descriptions)) EnvTbl.t;
  modules: (Path.t * module_declaration) EnvTbl.t;
  modtypes: (Path.t * modtype_declaration) EnvTbl.t;
  components: (Path.t * module_components) EnvTbl.t;
  classes: (Path.t * class_declaration) EnvTbl.t;
  cltypes: (Path.t * class_type_declaration) EnvTbl.t;
  functor_args: unit Ident.tbl;
  summary: summary;
  local_constraints: bool;
  gadt_instances: (int * TypeSet.t ref) list;
  in_signature: bool;
}

et module_components =
  (t * Subst.t * Path.t * Types.module_type, module_components_repr) EnvLazy.t

et module_components_repr =
    Structure_comps de structure_components
  | Functor_comps de functor_components

et structure_components = {
  modifiable comp_values: (string, (value_description * int)) Tbl.t;
  modifiable comp_constrs: (string, (constructor_description * int) list) Tbl.t;
  modifiable comp_labels: (string, (label_description * int) list) Tbl.t;
  modifiable comp_types:
   (string, ((type_declaration * type_descriptions) * int)) Tbl.t;
  modifiable comp_modules:
   (string, ((Subst.t * Types.module_type,module_type) EnvLazy.t * int)) Tbl.t;
  modifiable comp_modtypes: (string, (modtype_declaration * int)) Tbl.t;
  modifiable comp_components: (string, (module_components * int)) Tbl.t;
  modifiable comp_classes: (string, (class_declaration * int)) Tbl.t;
  modifiable comp_cltypes: (string, (class_type_declaration * int)) Tbl.t
}

et functor_components = {
  fcomp_param: Ident.t;                 (* Formal parameter *)
  fcomp_arg: module_type option;        (* Argument signature *)
  fcomp_res: module_type;               (* Result signature *)
  fcomp_env: t;     (* Environment in which the result signature makes sense *)
  fcomp_subst: Subst.t;  (* Prefixing substitution for the result signature *)
  fcomp_cache: (Path.t, module_components) Hashtbl.t;  (* For memoization *)
  fcomp_subst_cache: (Path.t, module_type) Hashtbl.t
}

soit subst_modtype_maker (subst, mty) = Subst.modtype subst mty

soit empty = {
  values = EnvTbl.empty; constrs = EnvTbl.empty;
  labels = EnvTbl.empty; types = EnvTbl.empty;
  modules = EnvTbl.empty; modtypes = EnvTbl.empty;
  components = EnvTbl.empty; classes = EnvTbl.empty;
  cltypes = EnvTbl.empty;
  summary = Env_empty; local_constraints = faux; gadt_instances = [];
  in_signature = faux;
  functor_args = Ident.empty;
 }

soit in_signature env = {env avec in_signature = vrai}

soit diff_keys is_local tbl1 tbl2 =
  soit keys2 = EnvTbl.keys tbl2 dans
  List.filter
    (fonc id ->
      is_local (EnvTbl.find_same_not_using id tbl2) &&
      essaie ignore (EnvTbl.find_same_not_using id tbl1); faux
      avec Not_found -> vrai)
    keys2

soit is_ident = fonction
    Pident _ -> vrai
  | Pdot _ | Papply _ -> faux

soit is_local (p, _) = is_ident p

soit is_local_exn = fonction
  | {cstr_tag = Cstr_exception (p, _)} -> is_ident p
  | _ -> faux

soit diff env1 env2 =
  diff_keys is_local env1.values env2.values @
  diff_keys is_local_exn env1.constrs env2.constrs @
  diff_keys is_local env1.modules env2.modules @
  diff_keys is_local env1.classes env2.classes

(* Forward declarations *)

soit components_of_module' =
  ref ((fonc env sub path mty -> affirme faux) :
          t -> Subst.t -> Path.t -> module_type -> module_components)
soit components_of_module_maker' =
  ref ((fonc (env, sub, path, mty) -> affirme faux) :
          t * Subst.t * Path.t * module_type -> module_components_repr)
soit components_of_functor_appl' =
  ref ((fonc f p1 p2 -> affirme faux) :
          functor_components -> Path.t -> Path.t -> module_components)
soit check_modtype_inclusion =
  (* to be filled with Includemod.check_modtype_inclusion *)
  ref ((fonc env mty1 path1 mty2 -> affirme faux) :
          t -> module_type -> Path.t -> module_type -> unit)
soit strengthen =
  (* to be filled with Mtype.strengthen *)
  ref ((fonc env mty path -> affirme faux) :
         t -> module_type -> Path.t -> module_type)

soit md md_type =
  {md_type; md_attributes=[]; md_loc=Location.none}

(* The name of the compilation unit currently compiled.
   "" if outside a compilation unit. *)

soit current_unit = ref ""

(* Persistent structure descriptions *)

type pers_struct =
  { ps_name: string;
    ps_sig: signature;
    ps_comps: module_components;
    ps_crcs: (string * Digest.t) list;
    ps_filename: string;
    ps_flags: pers_flags list;
    modifiable ps_crcs_checked: bool }

soit persistent_structures =
  (Hashtbl.create 17 : (string, pers_struct option) Hashtbl.t)

(* Consistency between persistent structures *)

soit crc_units = Consistbl.create()

soit check_consistency ps =
  si ps.ps_crcs_checked alors () sinon
  essaie
    List.iter
      (fonc (name, crc) -> Consistbl.check crc_units name crc ps.ps_filename)
      ps.ps_crcs;
    ps.ps_crcs_checked <- vrai
  avec Consistbl.Inconsistency(name, source, auth) ->
    error (Inconsistent_import(name, auth, source))

(* Reading persistent structures from .cmi files *)

soit read_pers_struct modname filename =
  soit cmi = read_cmi filename dans
  soit name = cmi.cmi_name dans
  soit sign = cmi.cmi_sign dans
  soit crcs = cmi.cmi_crcs dans
  soit flags = cmi.cmi_flags dans
  soit comps =
      !components_of_module' empty Subst.identity
                             (Pident(Ident.create_persistent name))
                             (Mty_signature sign)
  dans
  soit ps = { ps_name = name;
             ps_sig = sign;
             ps_comps = comps;
             ps_crcs = crcs;
             ps_crcs_checked = faux;
             ps_filename = filename;
             ps_flags = flags } dans
  si ps.ps_name <> modname alors
    error (Illegal_renaming(modname, ps.ps_name, filename));
  si not !Clflags.transparent_modules alors check_consistency ps;
  List.iter
    (fonction Rectypes ->
      si not !Clflags.recursive_types alors
        error (Need_recursive_types(ps.ps_name, !current_unit)))
    ps.ps_flags;
  Hashtbl.add persistent_structures modname (Some ps);
  ps

soit find_pers_struct ?(check=vrai) name =
  si name = "*predef*" alors raise Not_found;
  soit r =
    essaie Some (Hashtbl.find persistent_structures name)
    avec Not_found -> None
  dans
  soit ps =
    filtre r avec
    | Some None -> raise Not_found
    | Some (Some sg) -> sg
    | None ->
      soit filename =
        essaie find_in_path_uncap !load_path (name ^ ".cmi")
        avec Not_found ->
          Hashtbl.add persistent_structures name None;
          raise Not_found
      dans
      read_pers_struct name filename
  dans
  si check alors check_consistency ps;
  ps

soit reset_cache () =
  current_unit := "";
  Hashtbl.clear persistent_structures;
  Consistbl.clear crc_units;
  Hashtbl.clear value_declarations;
  Hashtbl.clear type_declarations;
  Hashtbl.clear used_constructors;
  Hashtbl.clear prefixed_sg

soit reset_cache_toplevel () =
  (* Delete 'missing cmi' entries from the cache. *)
  soit l =
    Hashtbl.fold
      (fonc name r acc -> si r = None alors name :: acc sinon acc)
      persistent_structures []
  dans
  List.iter (Hashtbl.remove persistent_structures) l;
  Hashtbl.clear value_declarations;
  Hashtbl.clear type_declarations;
  Hashtbl.clear used_constructors;
  Hashtbl.clear prefixed_sg


soit set_unit_name name =
  current_unit := name

(* Lookup by identifier *)

soit rec find_module_descr path env =
  filtre path avec
    Pident id ->
      début essaie
        soit (p, desc) = EnvTbl.find_same id env.components
        dans desc
      avec Not_found ->
        si Ident.persistent id
        alors (find_pers_struct (Ident.name id)).ps_comps
        sinon raise Not_found
      fin
  | Pdot(p, s, pos) ->
      début filtre
        EnvLazy.force !components_of_module_maker' (find_module_descr p env)
      avec
        Structure_comps c ->
          soit (descr, pos) = Tbl.find s c.comp_components dans
          descr
      | Functor_comps f ->
         raise Not_found
      fin
  | Papply(p1, p2) ->
      début filtre
        EnvLazy.force !components_of_module_maker' (find_module_descr p1 env)
      avec
        Functor_comps f ->
          !components_of_functor_appl' f p1 p2
      | Structure_comps c ->
          raise Not_found
      fin

soit find proj1 proj2 path env =
  filtre path avec
    Pident id ->
      soit (p, data) = EnvTbl.find_same id (proj1 env)
      dans data
  | Pdot(p, s, pos) ->
      début filtre
        EnvLazy.force !components_of_module_maker' (find_module_descr p env)
      avec
        Structure_comps c ->
          soit (data, pos) = Tbl.find s (proj2 c) dans data
      | Functor_comps f ->
          raise Not_found
      fin
  | Papply(p1, p2) ->
      raise Not_found

soit find_value =
  find (fonc env -> env.values) (fonc sc -> sc.comp_values)
et find_type_full =
  find (fonc env -> env.types) (fonc sc -> sc.comp_types)
et find_modtype =
  find (fonc env -> env.modtypes) (fonc sc -> sc.comp_modtypes)
et find_class =
  find (fonc env -> env.classes) (fonc sc -> sc.comp_classes)
et find_cltype =
  find (fonc env -> env.cltypes) (fonc sc -> sc.comp_cltypes)

soit find_type p env =
  fst (find_type_full p env)
soit find_type_descrs p env =
  snd (find_type_full p env)

soit find_module ~alias path env =
  filtre path avec
    Pident id ->
      début essaie
        soit (p, data) = EnvTbl.find_same id env.modules
        dans data
      avec Not_found ->
        si Ident.persistent id alors
          soit ps = find_pers_struct (Ident.name id) dans
          md (Mty_signature(ps.ps_sig))
        sinon raise Not_found
      fin
  | Pdot(p, s, pos) ->
      début filtre
        EnvLazy.force !components_of_module_maker' (find_module_descr p env)
      avec
        Structure_comps c ->
          soit (data, pos) = Tbl.find s c.comp_modules dans
          md (EnvLazy.force subst_modtype_maker data)
      | Functor_comps f ->
          raise Not_found
      fin
  | Papply(p1, p2) ->
      soit desc1 = find_module_descr p1 env dans
      début filtre EnvLazy.force !components_of_module_maker' desc1 avec
        Functor_comps f ->
          md début filtre f.fcomp_res avec
          | Mty_alias p ->
              Mty_alias (Subst.module_path f.fcomp_subst p)
          | mty ->
              si alias alors mty sinon
              essaie
                Hashtbl.find f.fcomp_subst_cache p2
              avec Not_found ->
                soit mty =
                  Subst.modtype
                    (Subst.add_module f.fcomp_param p2 f.fcomp_subst)
                    f.fcomp_res dans
                Hashtbl.add f.fcomp_subst_cache p2 mty;
                mty
          fin
      | Structure_comps c ->
          raise Not_found
      fin

soit required_globals = ref []
soit reset_required_globals () = required_globals := []
soit get_required_globals () = !required_globals
soit add_required_global id =
  si Ident.global id && not !Clflags.transparent_modules
  && not (List.exists (Ident.same id) !required_globals)
  alors required_globals := id :: !required_globals

soit rec normalize_path lax env path =
  soit path =
    filtre path avec
      Pdot(p, s, pos) ->
        Pdot(normalize_path lax env p, s, pos)
    | Papply(p1, p2) ->
        Papply(normalize_path lax env p1, normalize_path vrai env p2)
    | _ -> path
  dans
  essaie filtre find_module ~alias:vrai path env avec
    {md_type=Mty_alias path1} ->
      soit path' = normalize_path lax env path1 dans
      si lax || !Clflags.transparent_modules alors path' sinon
      soit id = Path.head path dans
      si Ident.global id && not (Ident.same id (Path.head path'))
      alors add_required_global id;
      path'
  | _ -> path
  avec Not_found quand lax
  || (filtre path avec Pident id -> not (Ident.persistent id) | _ -> vrai) ->
      path

soit normalize_path oloc env path =
  essaie normalize_path (oloc = None) env path
  avec Not_found ->
    filtre oloc avec None -> affirme faux
    | Some loc ->
        raise (Error(Missing_module(loc, path, normalize_path vrai env path)))

soit find_module = find_module ~alias:faux

(* Find the manifest type associated to a type when appropriate:
   - the type should be public or should have a private row,
   - the type should have an associated manifest type. *)
soit find_type_expansion path env =
  soit decl = find_type path env dans
  filtre decl.type_manifest avec
  | Some body quand decl.type_private = Public
              || decl.type_kind <> Type_abstract
              || Btype.has_constr_row body ->
                  (decl.type_params, body, may_map snd decl.type_newtype_level)
  (* The manifest type of Private abstract data types without
     private row are still considered unknown to the type system.
     Hence, this case is caught by the following clause that also handles
     purely abstract data types without manifest type definition. *)
  | _ ->
      (* another way to expand is to normalize the path itself *)
      soit path' = normalize_path None env path dans
      si Path.same path path' alors raise Not_found sinon
      (decl.type_params,
       newgenty (Tconstr (path', decl.type_params, ref Mnil)),
       may_map snd decl.type_newtype_level)

(* Find the manifest type information associated to a type, i.e.
   the necessary information for the compiler's type-based optimisations.
   In particular, the manifest type associated to a private abstract type
   is revealed for the sake of compiler's type-based optimisations. *)
soit find_type_expansion_opt path env =
  soit decl = find_type path env dans
  filtre decl.type_manifest avec
  (* The manifest type of Private abstract data types can still get
     an approximation using their manifest type. *)
  | Some body -> (decl.type_params, body, may_map snd decl.type_newtype_level)
  | _ ->
      soit path' = normalize_path None env path dans
      si Path.same path path' alors raise Not_found sinon
      (decl.type_params,
       newgenty (Tconstr (path', decl.type_params, ref Mnil)),
       may_map snd decl.type_newtype_level)

soit find_modtype_expansion path env =
  filtre (find_modtype path env).mtd_type avec
  | None -> raise Not_found
  | Some mty -> mty

soit rec is_functor_arg path env =
  filtre path avec
    Pident id ->
      début essaie Ident.find_same id env.functor_args; vrai
      avec Not_found -> faux
      fin
  | Pdot (p, s, _) -> is_functor_arg p env
  | Papply _ -> vrai

(* Lookup by name *)

exception Recmodule

soit rec lookup_module_descr lid env =
  filtre lid avec
    Lident s ->
      début essaie
        EnvTbl.find_name s env.components
      avec Not_found ->
        si s = !current_unit alors raise Not_found;
        soit ps = find_pers_struct s dans
        (Pident(Ident.create_persistent s), ps.ps_comps)
      fin
  | Ldot(l, s) ->
      soit (p, descr) = lookup_module_descr l env dans
      début filtre EnvLazy.force !components_of_module_maker' descr avec
        Structure_comps c ->
          soit (descr, pos) = Tbl.find s c.comp_components dans
          (Pdot(p, s, pos), descr)
      | Functor_comps f ->
          raise Not_found
      fin
  | Lapply(l1, l2) ->
      soit (p1, desc1) = lookup_module_descr l1 env dans
      soit p2 = lookup_module l2 env dans
      soit {md_type=mty2} = find_module p2 env dans
      début filtre EnvLazy.force !components_of_module_maker' desc1 avec
        Functor_comps f ->
          Misc.may (!check_modtype_inclusion env mty2 p2) f.fcomp_arg;
          (Papply(p1, p2), !components_of_functor_appl' f p1 p2)
      | Structure_comps c ->
          raise Not_found
      fin

et lookup_module lid env : Path.t =
  filtre lid avec
    Lident s ->
      début essaie
        soit (p, {md_type}) tel r = EnvTbl.find_name s env.modules dans
        début filtre md_type avec
        | Mty_ident (Path.Pident id) quand Ident.name id = "#recmod#" ->
          (* see #5965 *)
          raise Recmodule
        | _ -> ()
        fin;
        p
      avec Not_found ->
        si s = !current_unit alors raise Not_found;
        ignore (find_pers_struct ~check:faux s);
        Pident(Ident.create_persistent s)
      fin
  | Ldot(l, s) ->
      soit (p, descr) = lookup_module_descr l env dans
      début filtre EnvLazy.force !components_of_module_maker' descr avec
        Structure_comps c ->
          soit (data, pos) = Tbl.find s c.comp_modules dans
          Pdot(p, s, pos)
      | Functor_comps f ->
          raise Not_found
      fin
  | Lapply(l1, l2) ->
      soit (p1, desc1) = lookup_module_descr l1 env dans
      soit p2 = lookup_module l2 env dans
      soit {md_type=mty2} = find_module p2 env dans
      soit p = Papply(p1, p2) dans
      début filtre EnvLazy.force !components_of_module_maker' desc1 avec
        Functor_comps f ->
          Misc.may (!check_modtype_inclusion env mty2 p2) f.fcomp_arg;
          p
      | Structure_comps c ->
          raise Not_found
      fin

soit lookup proj1 proj2 lid env =
  filtre lid avec
    Lident s ->
      EnvTbl.find_name s (proj1 env)
  | Ldot(l, s) ->
      soit (p, desc) = lookup_module_descr l env dans
      début filtre EnvLazy.force !components_of_module_maker' desc avec
        Structure_comps c ->
          soit (data, pos) = Tbl.find s (proj2 c) dans
          (Pdot(p, s, pos), data)
      | Functor_comps f ->
          raise Not_found
      fin
  | Lapply(l1, l2) ->
      raise Not_found

soit lookup_simple proj1 proj2 lid env =
  filtre lid avec
    Lident s ->
      EnvTbl.find_name s (proj1 env)
  | Ldot(l, s) ->
      soit (p, desc) = lookup_module_descr l env dans
      début filtre EnvLazy.force !components_of_module_maker' desc avec
        Structure_comps c ->
          soit (data, pos) = Tbl.find s (proj2 c) dans
          data
      | Functor_comps f ->
          raise Not_found
      fin
  | Lapply(l1, l2) ->
      raise Not_found

soit lookup_all_simple proj1 proj2 shadow lid env =
  filtre lid avec
    Lident s ->
      soit xl = EnvTbl.find_all s (proj1 env) dans
      soit rec do_shadow =
        fonction
        | [] -> []
        | ((x, f) :: xs) ->
            (x, f) ::
              (do_shadow (List.filter (fonc (y, g) -> not (shadow x y)) xs))
      dans
        do_shadow xl
  | Ldot(l, s) ->
      soit (p, desc) = lookup_module_descr l env dans
      début filtre EnvLazy.force !components_of_module_maker' desc avec
        Structure_comps c ->
          soit comps =
            essaie Tbl.find s (proj2 c) avec Not_found -> []
          dans
          List.map
            (fonc (data, pos) -> (data, (fonc () -> ())))
            comps
      | Functor_comps f ->
          raise Not_found
      fin
  | Lapply(l1, l2) ->
      raise Not_found

soit has_local_constraints env = env.local_constraints

soit cstr_shadow cstr1 cstr2 =
  filtre cstr1.cstr_tag, cstr2.cstr_tag avec
    Cstr_exception _, Cstr_exception _ -> vrai
  | _ -> faux

soit lbl_shadow lbl1 lbl2 = faux

soit lookup_value =
  lookup (fonc env -> env.values) (fonc sc -> sc.comp_values)
et lookup_all_constructors =
  lookup_all_simple (fonc env -> env.constrs) (fonc sc -> sc.comp_constrs)
    cstr_shadow
et lookup_all_labels =
  lookup_all_simple (fonc env -> env.labels) (fonc sc -> sc.comp_labels)
    lbl_shadow
et lookup_type =
  lookup (fonc env -> env.types) (fonc sc -> sc.comp_types)
et lookup_modtype =
  lookup (fonc env -> env.modtypes) (fonc sc -> sc.comp_modtypes)
et lookup_class =
  lookup (fonc env -> env.classes) (fonc sc -> sc.comp_classes)
et lookup_cltype =
  lookup (fonc env -> env.cltypes) (fonc sc -> sc.comp_cltypes)

soit mark_value_used name vd =
  essaie Hashtbl.find value_declarations (name, vd.val_loc) ()
  avec Not_found -> ()

soit mark_type_used name vd =
  essaie Hashtbl.find type_declarations (name, vd.type_loc) ()
  avec Not_found -> ()

soit mark_constructor_used usage name vd constr =
  essaie Hashtbl.find used_constructors (name, vd.type_loc, constr) usage
  avec Not_found -> ()

soit mark_exception_used usage ed constr =
  essaie Hashtbl.find used_constructors ("exn", ed.exn_loc, constr) usage
  avec Not_found -> ()

soit set_value_used_callback name vd callback =
  soit key = (name, vd.val_loc) dans
  essaie
    soit old = Hashtbl.find value_declarations key dans
    Hashtbl.replace value_declarations key (fonc () -> old (); callback ())
      (* this is to support cases like:
               let x = let x = 1 in x in x
         where the two declarations have the same location
         (e.g. resulting from Camlp4 expansion of grammar entries) *)
  avec Not_found ->
    Hashtbl.add value_declarations key callback

soit set_type_used_callback name td callback =
  soit loc = td.type_loc dans
  si loc.Location.loc_ghost alors ()
  sinon soit key = (name, loc) dans
  soit old =
    essaie Hashtbl.find type_declarations key
    avec Not_found -> affirme faux
  dans
  Hashtbl.replace type_declarations key (fonc () -> callback old)

soit lookup_value lid env =
  soit (_, desc) tel r = lookup_value lid env dans
  mark_value_used (Longident.last lid) desc;
  r

soit lookup_type lid env =
  soit (path, (decl, _)) = lookup_type lid env dans
  mark_type_used (Longident.last lid) decl;
  (path, decl)

(* [path] must be the path to a type, not to a module ! *)
soit path_subst_last path id =
  filtre path avec
    Pident _ -> Pident id
  | Pdot (p, name, pos) -> Pdot(p, Ident.name id, pos)
  | Papply (p1, p2) -> affirme faux

soit mark_type_path env path =
  essaie
    soit decl = find_type path env dans
    mark_type_used (Path.last path) decl
  avec Not_found -> ()

soit ty_path t =
  filtre repr t avec
  | {desc=Tconstr(path, _, _)} -> path
  | _ -> affirme faux

soit lookup_constructor lid env =
  filtre lookup_all_constructors lid env avec
    [] -> raise Not_found
  | (desc, use) :: _ ->
      mark_type_path env (ty_path desc.cstr_res);
      use ();
      desc

soit is_lident = fonction
    Lident _ -> vrai
  | _ -> faux

soit lookup_all_constructors lid env =
  essaie
    soit cstrs = lookup_all_constructors lid env dans
    soit wrap_use desc use () =
      mark_type_path env (ty_path desc.cstr_res);
      use ()
    dans
    List.map (fonc (cstr, use) -> (cstr, wrap_use cstr use)) cstrs
  avec
    Not_found quand is_lident lid -> []

soit mark_constructor usage env name desc =
  filtre desc.cstr_tag avec
  | Cstr_exception (_, loc) ->
      début
        essaie Hashtbl.find used_constructors ("exn", loc, name) usage
        avec Not_found -> ()
      fin
  | _ ->
      soit ty_path = ty_path desc.cstr_res dans
      soit ty_decl = essaie find_type ty_path env avec Not_found -> affirme faux dans
      soit ty_name = Path.last ty_path dans
      mark_constructor_used usage ty_name ty_decl name

soit lookup_label lid env =
  filtre lookup_all_labels lid env avec
    [] -> raise Not_found
  | (desc, use) :: _ ->
      mark_type_path env (ty_path desc.lbl_res);
      use ();
      desc

soit lookup_all_labels lid env =
  essaie
    soit lbls = lookup_all_labels lid env dans
    soit wrap_use desc use () =
      mark_type_path env (ty_path desc.lbl_res);
      use ()
    dans
    List.map (fonc (lbl, use) -> (lbl, wrap_use lbl use)) lbls
  avec
    Not_found quand is_lident lid -> []

soit lookup_class lid env =
  soit (_, desc) tel r = lookup_class lid env dans
  (* special support for Typeclass.unbound_class *)
  si Path.name desc.cty_path = "" alors ignore (lookup_type lid env)
  sinon mark_type_path env desc.cty_path;
  r

soit lookup_cltype lid env =
  soit (_, desc) tel r = lookup_cltype lid env dans
  si Path.name desc.clty_path = "" alors ignore (lookup_type lid env)
  sinon mark_type_path env desc.clty_path;
  mark_type_path env desc.clty_path;
  r

(* Iter on an environment (ignoring the body of functors and
   not yet evaluated structures) *)

soit iter_env proj1 proj2 f env =
  Ident.iter (fonc id (x,_) -> f (Pident id) x) (proj1 env);
  soit rec iter_components path path' mcomps =
    (* if EnvLazy.is_val mcomps then *)
    filtre EnvLazy.force !components_of_module_maker' mcomps avec
      Structure_comps comps ->
        Tbl.iter
          (fonc s (d, n) -> f (Pdot (path, s, n)) (Pdot (path', s, n), d))
          (proj2 comps);
        Tbl.iter
          (fonc s (c, n) ->
            iter_components (Pdot (path, s, n)) (Pdot (path', s, n)) c)
          comps.comp_components
    | Functor_comps _ -> ()
  dans
  Hashtbl.iter
    (fonc s pso ->
      filtre pso avec None -> ()
      | Some ps ->
          soit id = Pident (Ident.create_persistent s) dans
          iter_components id id ps.ps_comps)
    persistent_structures;
  Ident.iter
    (fonc id ((path, comps), _) -> iter_components (Pident id) path comps)
    env.components

soit iter_types f = iter_env (fonc env -> env.types) (fonc sc -> sc.comp_types) f

soit same_types env1 env2 =
  env1.types == env2.types && env1.components == env2.components

soit used_persistent () =
  soit r = ref Concr.empty dans
  Hashtbl.iter (fonc s pso -> si pso != None alors r := Concr.add s !r)
    persistent_structures;
  !r

soit find_all_comps proj s (p,mcomps) =
  filtre EnvLazy.force !components_of_module_maker' mcomps avec
    Functor_comps _ -> []
  | Structure_comps comps ->
      essaie soit (c,n) = Tbl.find s (proj comps) dans [Pdot(p,s,n), c]
      avec Not_found -> []

soit rec find_shadowed_comps path env =
  filtre path avec
    Pident id ->
      List.map fst (Ident.find_all (Ident.name id) env.components)
  | Pdot (p, s, _) ->
      soit l = find_shadowed_comps p env dans
      soit l' =
        List.map (find_all_comps (fonc comps -> comps.comp_components) s) l dans
      List.flatten l'
  | Papply _ -> []

soit find_shadowed proj1 proj2 path env =
  filtre path avec
    Pident id ->
      List.map fst (Ident.find_all (Ident.name id) (proj1 env))
  | Pdot (p, s, _) ->
      soit l = find_shadowed_comps p env dans
      soit l' = List.map (find_all_comps proj2 s) l dans
      List.flatten l'
  | Papply _ -> []

soit find_shadowed_types path env =
  soit l =
    find_shadowed
      (fonc env -> env.types) (fonc comps -> comps.comp_types) path env
  dans
  List.map fst l


(* GADT instance tracking *)

soit add_gadt_instance_level lv env =
  {env avec
   gadt_instances = (lv, ref TypeSet.empty) :: env.gadt_instances}

soit is_Tlink = fonction {desc = Tlink _} -> vrai | _ -> faux

soit gadt_instance_level env t =
  soit rec find_instance = fonction
      [] -> None
    | (lv, r) :: rem ->
        si TypeSet.exists is_Tlink !r alors
          (* Should we use set_typeset ? *)
          r := TypeSet.fold (fonc ty -> TypeSet.add (repr ty)) !r TypeSet.empty;
        si TypeSet.mem t !r alors Some lv sinon find_instance rem
  dans find_instance env.gadt_instances

soit add_gadt_instances env lv tl =
  soit r =
    essaie List.assoc lv env.gadt_instances avec Not_found -> affirme faux dans
  (* Format.eprintf "Added";
  List.iter (fun ty -> Format.eprintf "@ %a" !Btype.print_raw ty) tl;
  Format.eprintf "@."; *)
  set_typeset r (List.fold_right TypeSet.add tl !r)

(* Only use this after expand_head! *)
soit add_gadt_instance_chain env lv t =
  soit r =
    essaie List.assoc lv env.gadt_instances avec Not_found -> affirme faux dans
  soit rec add_instance t =
    soit t = repr t dans
    si not (TypeSet.mem t !r) alors début
      (* Format.eprintf "@ %a" !Btype.print_raw t; *)
      set_typeset r (TypeSet.add t !r);
      filtre t.desc avec
        Tconstr (p, _, memo) ->
          may add_instance (find_expans Private p !memo)
      | _ -> ()
    fin
  dans
  (* Format.eprintf "Added chain"; *)
  add_instance t
  (* Format.eprintf "@." *)

(* Expand manifest module type names at the top of the given module type *)

soit rec scrape_alias env ?path mty =
  filtre mty, path avec
    Mty_ident p, _ ->
      début essaie
        scrape_alias env (find_modtype_expansion p env) ?path
      avec Not_found ->
        mty
      fin
  | Mty_alias path, _ ->
      début essaie
        scrape_alias env (find_module path env).md_type ~path
      avec Not_found ->
        Location.prerr_warning Location.none 
          (Warnings.Deprecated
             ("le module " ^ Path.name path ^ " est inaccessible"));
        mty
      fin      
  | mty, Some path ->
      !strengthen env mty path
  | _ -> mty

soit scrape_alias env mty = scrape_alias env mty

(* Compute constructor descriptions *)

soit constructors_of_type ty_path decl =
  soit handle_variants cstrs =
    Datarepr.constructor_descrs
      (newgenty (Tconstr(ty_path, decl.type_params, ref Mnil)))
      cstrs decl.type_private
  dans
  filtre decl.type_kind avec
  | Type_variant cstrs -> handle_variants cstrs
  | Type_record _ | Type_abstract -> []

(* Compute label descriptions *)

soit labels_of_type ty_path decl =
  filtre decl.type_kind avec
    Type_record(labels, rep) ->
      Datarepr.label_descrs
        (newgenty (Tconstr(ty_path, decl.type_params, ref Mnil)))
        labels rep decl.type_private
  | Type_variant _ | Type_abstract -> []

(* Given a signature and a root path, prefix all idents in the signature
   by the root path and build the corresponding substitution. *)

soit rec prefix_idents root pos sub = fonction
    [] -> ([], sub)
  | Sig_value(id, decl) :: rem ->
      soit p = Pdot(root, Ident.name id, pos) dans
      soit nextpos = filtre decl.val_kind avec Val_prim _ -> pos | _ -> pos+1 dans
      soit (pl, final_sub) = prefix_idents root nextpos sub rem dans
      (p::pl, final_sub)
  | Sig_type(id, decl, _) :: rem ->
      soit p = Pdot(root, Ident.name id, nopos) dans
      soit (pl, final_sub) =
        prefix_idents root pos (Subst.add_type id p sub) rem dans
      (p::pl, final_sub)
  | Sig_exception(id, decl) :: rem ->
      soit p = Pdot(root, Ident.name id, pos) dans
      soit (pl, final_sub) = prefix_idents root (pos+1) sub rem dans
      (p::pl, final_sub)
  | Sig_module(id, mty, _) :: rem ->
      soit p = Pdot(root, Ident.name id, pos) dans
      soit (pl, final_sub) =
        prefix_idents root (pos+1) (Subst.add_module id p sub) rem dans
      (p::pl, final_sub)
  | Sig_modtype(id, decl) :: rem ->
      soit p = Pdot(root, Ident.name id, nopos) dans
      soit (pl, final_sub) =
        prefix_idents root pos
                      (Subst.add_modtype id (Mty_ident p) sub) rem dans
      (p::pl, final_sub)
  | Sig_class(id, decl, _) :: rem ->
      soit p = Pdot(root, Ident.name id, pos) dans
      soit (pl, final_sub) = prefix_idents root (pos + 1) sub rem dans
      (p::pl, final_sub)
  | Sig_class_type(id, decl, _) :: rem ->
      soit p = Pdot(root, Ident.name id, nopos) dans
      soit (pl, final_sub) = prefix_idents root pos sub rem dans
      (p::pl, final_sub)

soit subst_signature sub sg =
  List.map
    (fonc item ->
      filtre item avec
      | Sig_value(id, decl) ->
          Sig_value (id, Subst.value_description sub decl)
      | Sig_type(id, decl, x) ->
          Sig_type(id, Subst.type_declaration sub decl, x)
      | Sig_exception(id, decl) ->
          Sig_exception (id, Subst.exception_declaration sub decl)
      | Sig_module(id, mty, x) ->
          Sig_module(id, Subst.module_declaration sub mty,x)
      | Sig_modtype(id, decl) ->
          Sig_modtype(id, Subst.modtype_declaration sub decl)
      | Sig_class(id, decl, x) ->
          Sig_class(id, Subst.class_declaration sub decl, x)
      | Sig_class_type(id, decl, x) ->
          Sig_class_type(id, Subst.cltype_declaration sub decl, x)
    )
    sg


soit prefix_idents_and_subst root sub sg =
  soit (pl, sub) = prefix_idents root 0 sub sg dans
  pl, sub, paresseux (subst_signature sub sg)

soit prefix_idents_and_subst root sub sg =
  si sub = Subst.identity alors
    soit sgs =
      essaie
        Hashtbl.find prefixed_sg root
      avec Not_found ->
        soit sgs = ref [] dans
        Hashtbl.add prefixed_sg root sgs;
        sgs
    dans
    essaie
      List.assq sg !sgs
    avec Not_found ->
      soit r = prefix_idents_and_subst root sub sg dans
      sgs := (sg, r) :: !sgs;
      r
  sinon
    prefix_idents_and_subst root sub sg

(* Compute structure descriptions *)

soit add_to_tbl id decl tbl =
  soit decls =
    essaie Tbl.find id tbl avec Not_found -> [] dans
  Tbl.add id (decl :: decls) tbl

soit rec components_of_module env sub path mty =
  EnvLazy.create (env, sub, path, mty)

et components_of_module_maker (env, sub, path, mty) =
  (filtre scrape_alias env mty avec
    Mty_signature sg ->
      soit c =
        { comp_values = Tbl.empty;
          comp_constrs = Tbl.empty;
          comp_labels = Tbl.empty; comp_types = Tbl.empty;
          comp_modules = Tbl.empty; comp_modtypes = Tbl.empty;
          comp_components = Tbl.empty; comp_classes = Tbl.empty;
          comp_cltypes = Tbl.empty } dans
      soit pl, sub, _ = prefix_idents_and_subst path sub sg dans
      soit env = ref env dans
      soit pos = ref 0 dans
      List.iter2 (fonc item path ->
        filtre item avec
          Sig_value(id, decl) ->
            soit decl' = Subst.value_description sub decl dans
            c.comp_values <-
              Tbl.add (Ident.name id) (decl', !pos) c.comp_values;
            début filtre decl.val_kind avec
              Val_prim _ -> () | _ -> incr pos
            fin
        | Sig_type(id, decl, _) ->
            soit decl' = Subst.type_declaration sub decl dans
            soit constructors = List.map snd (constructors_of_type path decl') dans
            soit labels = List.map snd (labels_of_type path decl') dans
            c.comp_types <-
              Tbl.add (Ident.name id)
                ((decl', (constructors, labels)), nopos)
                  c.comp_types;
            List.iter
              (fonc descr ->
                c.comp_constrs <-
                  add_to_tbl descr.cstr_name (descr, nopos) c.comp_constrs)
              constructors;
            List.iter
              (fonc descr ->
                c.comp_labels <-
                  add_to_tbl descr.lbl_name (descr, nopos) c.comp_labels)
              labels;
            env := store_type_infos None id path decl !env !env
        | Sig_exception(id, decl) ->
            soit decl' = Subst.exception_declaration sub decl dans
            soit cstr = Datarepr.exception_descr path decl' dans
            soit s = Ident.name id dans
            c.comp_constrs <-
              add_to_tbl s (cstr, !pos) c.comp_constrs;
            incr pos
        | Sig_module(id, md, _) ->
            soit mty = md.md_type dans
            soit mty' = EnvLazy.create (sub, mty) dans
            c.comp_modules <-
              Tbl.add (Ident.name id) (mty', !pos) c.comp_modules;
            soit comps = components_of_module !env sub path mty dans
            c.comp_components <-
              Tbl.add (Ident.name id) (comps, !pos) c.comp_components;
            env := store_module None id path md !env !env;
            incr pos
        | Sig_modtype(id, decl) ->
            soit decl' = Subst.modtype_declaration sub decl dans
            c.comp_modtypes <-
              Tbl.add (Ident.name id) (decl', nopos) c.comp_modtypes;
            env := store_modtype None id path decl !env !env
        | Sig_class(id, decl, _) ->
            soit decl' = Subst.class_declaration sub decl dans
            c.comp_classes <-
              Tbl.add (Ident.name id) (decl', !pos) c.comp_classes;
            incr pos
        | Sig_class_type(id, decl, _) ->
            soit decl' = Subst.cltype_declaration sub decl dans
            c.comp_cltypes <-
              Tbl.add (Ident.name id) (decl', !pos) c.comp_cltypes)
        sg pl;
        Structure_comps c
  | Mty_functor(param, ty_arg, ty_res) ->
        Functor_comps {
          fcomp_param = param;
          (* fcomp_arg must be prefixed eagerly, because it is interpreted
             in the outer environment, not in env *)
          fcomp_arg = may_map (Subst.modtype sub) ty_arg;
          (* fcomp_res is prefixed lazily, because it is interpreted in env *)
          fcomp_res = ty_res;
          fcomp_env = env;
          fcomp_subst = sub;
          fcomp_cache = Hashtbl.create 17;
          fcomp_subst_cache = Hashtbl.create 17 }
  | Mty_ident _
  | Mty_alias _ ->
        Structure_comps {
          comp_values = Tbl.empty;
          comp_constrs = Tbl.empty;
          comp_labels = Tbl.empty;
          comp_types = Tbl.empty;
          comp_modules = Tbl.empty; comp_modtypes = Tbl.empty;
          comp_components = Tbl.empty; comp_classes = Tbl.empty;
          comp_cltypes = Tbl.empty })

(* Insertion of bindings by identifier + path *)

et check_usage loc id warn tbl =
  si not loc.Location.loc_ghost && Warnings.is_active (warn "") alors début
    soit name = Ident.name id dans
    soit key = (name, loc) dans
    si Hashtbl.mem tbl key alors ()
    sinon soit used = ref faux dans
    Hashtbl.add tbl key (fonc () -> used := vrai);
    si not (name = "" || name.[0] = '_' || name.[0] = '#')
    alors
      !add_delayed_check_forward
        (fonc () -> si not !used alors Location.prerr_warning loc (warn name))
  fin;

et store_value ?check slot id path decl env renv =
  may (fonc f -> check_usage decl.val_loc id f value_declarations) check;
  { env avec
    values = EnvTbl.add "valeur" slot id (path, decl) env.values renv.values;
    summary = Env_value(env.summary, id, decl) }

et store_type ~check slot id path info env renv =
  soit loc = info.type_loc dans
  si check alors
    check_usage loc id (fonc s -> Warnings.Unused_type_declaration s)
      type_declarations;
  soit constructors = constructors_of_type path info dans
  soit labels = labels_of_type path info dans
  soit descrs = (List.map snd constructors, List.map snd labels) dans

  si check && not loc.Location.loc_ghost &&
    Warnings.is_active (Warnings.Unused_constructor ("", faux, faux))
  alors début
    soit ty = Ident.name id dans
    List.iter
      début fonc (_, {cstr_name = c; _}) ->
        soit k = (ty, loc, c) dans
        si not (Hashtbl.mem used_constructors k) alors
          soit used = constructor_usages () dans
          Hashtbl.add used_constructors k (add_constructor_usage used);
          si not (ty = "" || ty.[0] = '_')
          alors !add_delayed_check_forward
              (fonc () ->
                si not env.in_signature && not used.cu_positive alors
                  Location.prerr_warning loc
                    (Warnings.Unused_constructor
                       (c, used.cu_pattern, used.cu_privatize)))
      fin
      constructors
  fin;
  { env avec
    constrs =
      List.fold_right
        (fonc (id, descr) constrs ->
          EnvTbl.add "constructeur" slot id descr constrs renv.constrs)
        constructors
        env.constrs;
    labels =
      List.fold_right
        (fonc (id, descr) labels ->
          EnvTbl.add "label" slot id descr labels renv.labels)
        labels
        env.labels;
    types = EnvTbl.add "type" slot id (path, (info, descrs)) env.types
                       renv.types;
    summary = Env_type(env.summary, id, info) }

et store_type_infos slot id path info env renv =
  (* Simplified version of store_type that doesn't compute and store
     constructor and label infos, but simply record the arity and
     manifest-ness of the type.  Used in components_of_module to
     keep track of type abbreviations (e.g. type t = float) in the
     computation of label representations. *)
  { env avec
    types = EnvTbl.add "type" slot id (path, (info,([],[]))) env.types
                       renv.types;
    summary = Env_type(env.summary, id, info) }

et store_exception ~check slot id path decl env renv =
  soit loc = decl.exn_loc dans
  si check && not loc.Location.loc_ghost &&
    Warnings.is_active (Warnings.Unused_exception ("", faux))
  alors début
    soit ty = "exn" dans
    soit c = Ident.name id dans
    soit k = (ty, loc, c) dans
    si not (Hashtbl.mem used_constructors k) alors début
      soit used = constructor_usages () dans
      Hashtbl.add used_constructors k (add_constructor_usage used);
      !add_delayed_check_forward
        (fonc () ->
          si not env.in_signature && not used.cu_positive alors
            Location.prerr_warning loc
              (Warnings.Unused_exception
                 (c, used.cu_pattern)
              )
        )
    fin;
  fin;
  { env avec
    constrs = EnvTbl.add "constructeur" slot id
                         (Datarepr.exception_descr path decl) env.constrs
                         renv.constrs;
    summary = Env_exception(env.summary, id, decl) }

et store_module slot id path md env renv =
  { env avec
    modules = EnvTbl.add "module" slot id (path, md) env.modules renv.modules;
    components =
      EnvTbl.add "module" slot id
                 (path, components_of_module env Subst.identity path md.md_type)
                   env.components renv.components;
    summary = Env_module(env.summary, id, md) }

et store_modtype slot id path info env renv =
  { env avec
    modtypes = EnvTbl.add "type de module" slot id (path, info) env.modtypes
                          renv.modtypes;
    summary = Env_modtype(env.summary, id, info) }

et store_class slot id path desc env renv =
  { env avec
    classes = EnvTbl.add "classe" slot id (path, desc) env.classes renv.classes;
    summary = Env_class(env.summary, id, desc) }

et store_cltype slot id path desc env renv =
  { env avec
    cltypes = EnvTbl.add "type de classe" slot id (path, desc) env.cltypes
                         renv.cltypes;
    summary = Env_cltype(env.summary, id, desc) }

(* Compute the components of a functor application in a path. *)

soit components_of_functor_appl f p1 p2 =
  essaie
    Hashtbl.find f.fcomp_cache p2
  avec Not_found ->
    soit p = Papply(p1, p2) dans
    soit mty =
      Subst.modtype (Subst.add_module f.fcomp_param p2 Subst.identity)
                    f.fcomp_res dans
    soit comps = components_of_module f.fcomp_env f.fcomp_subst p mty dans
    Hashtbl.add f.fcomp_cache p2 comps;
    comps

(* Define forward functions *)

soit _ =
  components_of_module' := components_of_module;
  components_of_functor_appl' := components_of_functor_appl;
  components_of_module_maker' := components_of_module_maker

(* Insertion of bindings by identifier *)

soit add_functor_arg ?(arg=faux) id env =
  si not arg alors env sinon
  {env avec
   functor_args = Ident.add id () env.functor_args;
   summary = Env_functor_arg (env.summary, id)}

soit add_value ?check id desc env =
  store_value None ?check id (Pident id) desc env env

soit add_type ~check id info env =
  store_type ~check None id (Pident id) info env env

et add_exception ~check id decl env =
  store_exception ~check None id (Pident id) decl env env

et add_module_declaration ?arg id md env =
  soit path =
    (*match md.md_type with
      Mty_alias path -> normalize_path env path
    | _ ->*) Pident id
  dans
  soit env = store_module None id path md env env dans
  add_functor_arg ?arg id env

et add_modtype id info env =
  store_modtype None id (Pident id) info env env

et add_class id ty env =
  store_class None id (Pident id) ty env env

et add_cltype id ty env =
  store_cltype None id (Pident id) ty env env

soit add_module ?arg id mty env =
  add_module_declaration ?arg id (md mty) env

soit add_local_constraint id info elv env =
  filtre info avec
    {type_manifest = Some ty; type_newtype_level = Some (lv, _)} ->
      (* elv is the expansion level, lv is the definition level *)
      soit env =
        add_type ~check:faux
          id {info avec type_newtype_level = Some (lv, elv)} env dans
      { env avec local_constraints = vrai }
  | _ -> affirme faux

(* Insertion of bindings by name *)

soit enter store_fun name data env =
  soit id = Ident.create name dans (id, store_fun None id (Pident id) data env env)

soit enter_value ?check = enter (store_value ?check)
et enter_type = enter (store_type ~check:vrai)
et enter_exception = enter (store_exception ~check:vrai)
et enter_module_declaration ?arg name md env =
  soit id = Ident.create name dans
  (id, add_module_declaration ?arg id md env)
  (* let (id, env) = enter store_module name md env in
  (id, add_functor_arg ?arg id env) *)
et enter_modtype = enter store_modtype
et enter_class = enter store_class
et enter_cltype = enter store_cltype

soit enter_module ?arg s mty env =
  enter_module_declaration ?arg s (md mty) env

(* Insertion of all components of a signature *)

soit add_item comp env =
  filtre comp avec
    Sig_value(id, decl)     -> add_value id decl env
  | Sig_type(id, decl, _)   -> add_type ~check:faux id decl env
  | Sig_exception(id, decl) -> add_exception ~check:faux id decl env
  | Sig_module(id, md, _)  -> add_module_declaration id md env
  | Sig_modtype(id, decl)   -> add_modtype id decl env
  | Sig_class(id, decl, _)  -> add_class id decl env
  | Sig_class_type(id, decl, _) -> add_cltype id decl env

soit rec add_signature sg env =
  filtre sg avec
    [] -> env
  | comp :: rem -> add_signature rem (add_item comp env)

(* Open a signature path *)

soit open_signature slot root sg env0 =
  (* First build the paths and substitution *)
  soit (pl, sub, sg) = prefix_idents_and_subst root Subst.identity sg dans
  soit sg = Lazy.force sg dans

  (* Then enter the components in the environment after substitution *)

  soit newenv =
    List.fold_left2
      (fonc env item p ->
        filtre item avec
          Sig_value(id, decl) ->
            store_value slot (Ident.hide id) p decl env env0
        | Sig_type(id, decl, _) ->
            store_type ~check:faux slot (Ident.hide id) p decl env env0
        | Sig_exception(id, decl) ->
            store_exception ~check:faux slot (Ident.hide id) p decl env env0
        | Sig_module(id, mty, _) ->
            store_module slot (Ident.hide id) p mty env env0
        | Sig_modtype(id, decl) ->
            store_modtype slot (Ident.hide id) p decl env env0
        | Sig_class(id, decl, _) ->
            store_class slot (Ident.hide id) p decl env env0
        | Sig_class_type(id, decl, _) ->
            store_cltype slot (Ident.hide id) p decl env env0
      )
      env0 sg pl dans
  { newenv avec summary = Env_open(env0.summary, root) }

(* Open a signature from a file *)

soit open_pers_signature name env =
  soit ps = find_pers_struct name dans
  open_signature None (Pident(Ident.create_persistent name)) ps.ps_sig env

soit open_signature ?(loc = Location.none) ?(toplevel = faux) ovf root sg env =
  si not toplevel && ovf = Asttypes.Fresh && not loc.Location.loc_ghost
     && (Warnings.is_active (Warnings.Unused_open "")
         || Warnings.is_active (Warnings.Open_shadow_identifier ("", ""))
         || Warnings.is_active (Warnings.Open_shadow_label_constructor ("","")))
  alors début
    soit used = ref faux dans
    !add_delayed_check_forward
      (fonc () ->
        si not !used alors
          Location.prerr_warning loc (Warnings.Unused_open (Path.name root))
      );
    soit shadowed = ref [] dans
    soit slot kind s b =
      si b && not (List.mem (kind, s) !shadowed) alors début
        shadowed := (kind, s) :: !shadowed;
        soit w =
          filtre kind avec
          | "label" | "constructeur" ->
              Warnings.Open_shadow_label_constructor (kind, s)
          | _ -> Warnings.Open_shadow_identifier (kind, s)
        dans
        Location.prerr_warning loc w
      fin;
      used := vrai
    dans
    open_signature (Some slot) root sg env
  fin
  sinon open_signature None root sg env

(* Read a signature from a file *)

soit read_signature modname filename =
  soit ps = read_pers_struct modname filename dans
  check_consistency ps;
  ps.ps_sig

(* Return the CRC of the interface of the given compilation unit *)

soit crc_of_unit name =
  soit ps = find_pers_struct ~check:faux name dans
  essaie
    List.assoc name ps.ps_crcs
  avec Not_found ->
    affirme faux

(* Return the list of imported interfaces with their CRCs *)

soit imported_units() =
  Consistbl.extract crc_units

(* Save a signature to a file *)

soit save_signature_with_imports sg modname filename imports =
  (*prerr_endline filename;
  List.iter (fun (name, crc) -> prerr_endline name) imports;*)
  Btype.cleanup_abbrev ();
  Subst.reset_for_saving ();
  soit sg = Subst.signature (Subst.for_saving Subst.identity) sg dans
  soit oc = open_out_bin filename dans
  essaie
    soit cmi = {
      cmi_name = modname;
      cmi_sign = sg;
      cmi_crcs = imports;
      cmi_flags = si !Clflags.recursive_types alors [Rectypes] sinon [];
    } dans
    soit crc = output_cmi filename oc cmi dans
    close_out oc;
    (* Enter signature in persistent table so that imported_unit()
       will also return its crc *)
    soit comps =
      components_of_module empty Subst.identity
        (Pident(Ident.create_persistent modname)) (Mty_signature sg) dans
    soit ps =
      { ps_name = modname;
        ps_sig = sg;
        ps_comps = comps;
        ps_crcs = (cmi.cmi_name, crc) :: imports;
        ps_filename = filename;
        ps_flags = cmi.cmi_flags;
        ps_crcs_checked = vrai } dans
    Hashtbl.add persistent_structures modname (Some ps);
    Consistbl.set crc_units modname crc filename;
    sg
  avec exn ->
    close_out oc;
    remove_file filename;
    raise exn

soit save_signature sg modname filename =
  save_signature_with_imports sg modname filename (imported_units())

(* Folding on environments *)

soit find_all proj1 proj2 f lid env acc =
  filtre lid avec
    | None ->
      EnvTbl.fold_name
        (fonc id (p, data) acc -> f (Ident.name id) p data acc)
        (proj1 env) acc
    | Some l ->
      soit p, desc = lookup_module_descr l env dans
      début filtre EnvLazy.force components_of_module_maker desc avec
          Structure_comps c ->
            Tbl.fold
              (fonc s (data, pos) acc -> f s (Pdot (p, s, pos)) data acc)
              (proj2 c) acc
        | Functor_comps _ ->
            acc
      fin

soit find_all_simple_list proj1 proj2 f lid env acc =
  filtre lid avec
    | None ->
      EnvTbl.fold_name
        (fonc id data acc -> f data acc)
        (proj1 env) acc
    | Some l ->
      soit p, desc = lookup_module_descr l env dans
      début filtre EnvLazy.force components_of_module_maker desc avec
          Structure_comps c ->
            Tbl.fold
              (fonc s comps acc ->
                filtre comps avec
                  [] -> acc
                | (data, pos) :: _ ->
                  f data acc)
              (proj2 c) acc
        | Functor_comps _ ->
            acc
      fin

soit fold_modules f lid env acc =
  filtre lid avec
    | None ->
      soit acc =
        EnvTbl.fold_name
          (fonc id (p, data) acc -> f (Ident.name id) p data acc)
          env.modules
          acc
      dans
      Hashtbl.fold
        (fonc name ps acc ->
          filtre ps avec
              None -> acc
            | Some ps ->
              f name (Pident(Ident.create_persistent name))
                     (md (Mty_signature ps.ps_sig)) acc)
        persistent_structures
        acc
    | Some l ->
      soit p, desc = lookup_module_descr l env dans
      début filtre EnvLazy.force components_of_module_maker desc avec
          Structure_comps c ->
            Tbl.fold
              (fonc s (data, pos) acc ->
                f s (Pdot (p, s, pos))
                    (md (EnvLazy.force subst_modtype_maker data)) acc)
              c.comp_modules
              acc
        | Functor_comps _ ->
            acc
      fin

soit fold_values f =
  find_all (fonc env -> env.values) (fonc sc -> sc.comp_values) f
et fold_constructors f =
  find_all_simple_list (fonc env -> env.constrs) (fonc sc -> sc.comp_constrs) f
et fold_labels f =
  find_all_simple_list (fonc env -> env.labels) (fonc sc -> sc.comp_labels) f
et fold_types f =
  find_all (fonc env -> env.types) (fonc sc -> sc.comp_types) f
et fold_modtypes f =
  find_all (fonc env -> env.modtypes) (fonc sc -> sc.comp_modtypes) f
et fold_classs f =
  find_all (fonc env -> env.classes) (fonc sc -> sc.comp_classes) f
et fold_cltypes f =
  find_all (fonc env -> env.cltypes) (fonc sc -> sc.comp_cltypes) f


(* Make the initial environment *)

soit initial =
  Predef.build_initial_env
    (add_type ~check:faux)
    (add_exception ~check:faux)
    empty

(* Return the environment summary *)

soit summary env = env.summary

soit last_env = ref empty
soit last_reduced_env = ref empty

soit keep_only_summary env =
  si !last_env == env alors !last_reduced_env
  sinon début
    soit new_env =
      {
       empty avec
       summary = env.summary;
       local_constraints = env.local_constraints;
       in_signature = env.in_signature;
      }
    dans
    last_env := env;
    last_reduced_env := new_env;
    new_env
  fin


soit env_of_only_summary env_from_summary env =
  soit new_env = env_from_summary env.summary Subst.identity dans
  { new_env avec
    local_constraints = env.local_constraints;
    in_signature = env.in_signature;
  }

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Illegal_renaming(name, modname, filename) -> fprintf ppf
      "Mauvais nommage de fichier : %a@ contient une interface compilée pour @ %s alors que %s était attendu"
      Location.print_filename filename name modname
  | Inconsistent_import(name, source1, source2) -> fprintf ppf
      "@[<hov>Les fichiers %a@ et %a@ \
              font des hypothèses inconsistantes@ sur l'interface %s@]"
      Location.print_filename source1 Location.print_filename source2 name
  | Need_recursive_types(import, export) ->
      fprintf ppf
        "@[<hov>L'unité %s importe %s, qui utilise des types récursifs.@ %s@]"
        export import "Le drapeau de compilation -rectypes est requis"
  | Missing_module(_, path1, path2) ->
      fprintf ppf "@[@[<hov>";
      si Path.same path1 path2 alors
        fprintf ppf "Le chemin interne@ %s@ est suspendu" (Path.name path1)
      sinon
        fprintf ppf "Le chemin interne@ %s@ s'étend en@ %s@, qui est suspendu"
          (Path.name path1) (Path.name path2);
      fprintf ppf "@]@ @[%s@ %s@ %s.@]@]"
        "L'interface compilée pour le module" (Ident.name (Path.head path2))
        "n'a pas été trouvée"

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (Missing_module (loc, _, _) tel err) quand loc <> Location.none ->
          Some (Location.error_of_printer loc report_error err)
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )

