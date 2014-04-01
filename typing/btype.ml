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

(* Basic operations on core types *)

ouvre Misc
ouvre Types

(**** Sets, maps and hashtables of types ****)

module TypeSet = Set.Make(TypeOps)
module TypeMap = Map.Make (TypeOps)
module TypeHash = Hashtbl.Make(TypeOps)

(**** Forward declarations ****)

soit print_raw =
  ref (fonc _ -> affirme faux : Format.formatter -> type_expr -> unit)

(**** Type level management ****)

soit generic_level = 100000000

(* Used to mark a type during a traversal. *)
soit lowest_level = 0
soit pivot_level = 2 * lowest_level - 1
    (* pivot_level - lowest_level < lowest_level *)

(**** Some type creators ****)

soit new_id = ref (-1)

soit newty2 level desc  =
  incr new_id; { desc; level; id = !new_id }
soit newgenty desc      = newty2 generic_level desc
soit newgenvar ?name () = newgenty (Tvar name)
(*
let newmarkedvar level =
  incr new_id; { desc = Tvar; level = pivot_level - level; id = !new_id }
let newmarkedgenvar () =
  incr new_id;
  { desc = Tvar; level = pivot_level - generic_level; id = !new_id }
*)

(**** Check some types ****)

soit is_Tvar = fonction {desc=Tvar _} -> vrai | _ -> faux
soit is_Tunivar = fonction {desc=Tunivar _} -> vrai | _ -> faux

soit dummy_method = "*dummy method*"
soit default_mty = fonction
    Some mty -> mty
  | None -> Mty_signature []

(**** Representative of a type ****)

soit rec field_kind_repr =
  fonction
    Fvar {contents = Some kind} -> field_kind_repr kind
  | kind                        -> kind

soit rec repr =
  fonction
    {desc = Tlink t'} ->
      (*
         We do no path compression. Path compression does not seem to
         improve notably efficiency, and it prevents from changing a
         [Tlink] into another type (for instance, for undoing a
         unification).
      *)
      repr t'
  | {desc = Tfield (_, k, _, t')} quand field_kind_repr k = Fabsent ->
      repr t'
  | t -> t

soit rec commu_repr = fonction
    Clink r quand !r <> Cunknown -> commu_repr !r
  | c -> c

soit rec row_field_repr_aux tl = fonction
    Reither(_, tl', _, {contents = Some fi}) ->
      row_field_repr_aux (tl@tl') fi
  | Reither(c, tl', m, r) ->
      Reither(c, tl@tl', m, r)
  | Rpresent (Some _) quand tl <> [] ->
      Rpresent (Some (List.hd tl))
  | fi -> fi

soit row_field_repr fi = row_field_repr_aux [] fi

soit rec rev_concat l ll =
  filtre ll avec
    [] -> l
  | l'::ll -> rev_concat (l'@l) ll

soit rec row_repr_aux ll row =
  filtre (repr row.row_more).desc avec
  | Tvariant row' ->
      soit f = row.row_fields dans
      row_repr_aux (si f = [] alors ll sinon f::ll) row'
  | _ ->
      si ll = [] alors row sinon
      {row avec row_fields = rev_concat row.row_fields ll}

soit row_repr row = row_repr_aux [] row

soit rec row_field tag row =
  soit rec find = fonction
    | (tag',f) :: fields ->
        si tag = tag' alors row_field_repr f sinon find fields
    | [] ->
        filtre repr row.row_more avec
        | {desc=Tvariant row'} -> row_field tag row'
        | _ -> Rabsent
  dans find row.row_fields

soit rec row_more row =
  filtre repr row.row_more avec
  | {desc=Tvariant row'} -> row_more row'
  | ty -> ty

soit row_fixed row =
  soit row = row_repr row dans
  row.row_fixed ||
  filtre (repr row.row_more).desc avec
    Tvar _ | Tnil -> faux
  | Tunivar _ | Tconstr _ -> vrai
  | _ -> affirme faux

soit static_row row =
  soit row = row_repr row dans
  row.row_closed &&
  List.for_all
    (fonc (_,f) -> filtre row_field_repr f avec Reither _ -> faux | _ -> vrai)
    row.row_fields

soit hash_variant s =
  soit accu = ref 0 dans
  pour i = 0 à String.length s - 1 faire
    accu := 223 * !accu + Char.code s.[i]
  fait;
  (* reduce to 31 bits *)
  accu := !accu etl (1 dgl 31 - 1);
  (* make it signed for 64 bits architectures *)
  si !accu > 0x3FFFFFFF alors !accu - (1 dgl 31) sinon !accu

soit proxy ty =
  soit ty0 = repr ty dans
  filtre ty0.desc avec
  | Tvariant row quand not (static_row row) ->
      row_more row
  | Tobject (ty, _) ->
      soit rec proxy_obj ty =
        filtre ty.desc avec
          Tfield (_, _, _, ty) | Tlink ty -> proxy_obj ty
        | Tvar _ | Tunivar _ | Tconstr _ -> ty
        | Tnil -> ty0
        | _ -> affirme faux
      dans proxy_obj ty
  | _ -> ty0

(**** Utilities for fixed row private types ****)

soit has_constr_row t =
  filtre (repr t).desc avec
    Tobject(t,_) ->
      soit rec check_row t =
        filtre (repr t).desc avec
          Tfield(_,_,_,t) -> check_row t
        | Tconstr _ -> vrai
        | _ -> faux
      dans check_row t
  | Tvariant row ->
      (filtre row_more row avec {desc=Tconstr _} -> vrai | _ -> faux)
  | _ ->
      faux

soit is_row_name s =
  soit l = String.length s dans
  si l < 4 alors faux sinon String.sub s (l-4) 4 = "#row"

soit is_constr_row t =
  filtre t.desc avec
    Tconstr (Path.Pident id, _, _) -> is_row_name (Ident.name id)
  | Tconstr (Path.Pdot (_, s, _), _, _) -> is_row_name s
  | _ -> faux


                  (**********************************)
                  (*  Utilities for type traversal  *)
                  (**********************************)

soit rec iter_row f row =
  List.iter
    (fonc (_, fi) ->
      filtre row_field_repr fi avec
      | Rpresent(Some ty) -> f ty
      | Reither(_, tl, _, _) -> List.iter f tl
      | _ -> ())
    row.row_fields;
  filtre (repr row.row_more).desc avec
    Tvariant row -> iter_row f row
  | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
      Misc.may (fonc (_,l) -> List.iter f l) row.row_name
  | _ -> affirme faux

soit iter_type_expr f ty =
  filtre ty.desc avec
    Tvar _              -> ()
  | Tarrow (_, ty1, ty2, _) -> f ty1; f ty2
  | Ttuple l            -> List.iter f l
  | Tconstr (_, l, _)   -> List.iter f l
  | Tobject(ty, {contents = Some (_, p)})
                        -> f ty; List.iter f p
  | Tobject (ty, _)     -> f ty
  | Tvariant row        -> iter_row f row; f (row_more row)
  | Tfield (_, _, ty1, ty2) -> f ty1; f ty2
  | Tnil                -> ()
  | Tlink ty            -> f ty
  | Tsubst ty           -> f ty
  | Tunivar _           -> ()
  | Tpoly (ty, tyl)     -> f ty; List.iter f tyl
  | Tpackage (_, _, l)  -> List.iter f l

soit rec iter_abbrev f = fonction
    Mnil                   -> ()
  | Mcons(_, _, ty, ty', rem) -> f ty; f ty'; iter_abbrev f rem
  | Mlink rem              -> iter_abbrev f !rem

type type_iterators =
  { it_signature: type_iterators -> signature -> unit;
    it_signature_item: type_iterators -> signature_item -> unit;
    it_value_description: type_iterators -> value_description -> unit;
    it_type_declaration: type_iterators -> type_declaration -> unit;
    it_exception_declaration: type_iterators -> exception_declaration -> unit;
    it_module_declaration: type_iterators -> module_declaration -> unit;
    it_modtype_declaration: type_iterators -> modtype_declaration -> unit;
    it_class_declaration: type_iterators -> class_declaration -> unit;
    it_class_type_declaration: type_iterators -> class_type_declaration -> unit;
    it_module_type: type_iterators -> module_type -> unit;
    it_class_type: type_iterators -> class_type -> unit;
    it_type_kind: type_iterators -> type_kind -> unit;
    it_type_expr: type_iterators -> type_expr -> unit;
    it_path: Path.t -> unit; }

soit type_iterators =
  soit it_signature it =
    List.iter (it.it_signature_item it)
  et it_signature_item it = fonction
      Sig_value (_, vd)     -> it.it_value_description it vd
    | Sig_type (_, td, _)   -> it.it_type_declaration it td
    | Sig_exception (_, ed) -> it.it_exception_declaration it ed
    | Sig_module (_, md, _) -> it.it_module_declaration it md
    | Sig_modtype (_, mtd)  -> it.it_modtype_declaration it mtd
    | Sig_class (_, cd, _)  -> it.it_class_declaration it cd
    | Sig_class_type (_, ctd, _) -> it.it_class_type_declaration it ctd
  et it_value_description it vd =
    it.it_type_expr it vd.val_type
  et it_type_declaration it td =
    List.iter (it.it_type_expr it) td.type_params;
    may (it.it_type_expr it) td.type_manifest;
    it.it_type_kind it td.type_kind
  et it_exception_declaration it ed =
    List.iter (it.it_type_expr it) ed.exn_args
  et it_module_declaration it md =
    it.it_module_type it md.md_type
  et it_modtype_declaration it mtd =
    may (it.it_module_type it) mtd.mtd_type
  et it_class_declaration it cd =
    List.iter (it.it_type_expr it) cd.cty_params;
    it.it_class_type it cd.cty_type;
    may (it.it_type_expr it) cd.cty_new;
    it.it_path cd.cty_path
  et it_class_type_declaration it ctd =
    List.iter (it.it_type_expr it) ctd.clty_params;
    it.it_class_type it ctd.clty_type;
    it.it_path ctd.clty_path
  et it_module_type it = fonction
      Mty_ident p
    | Mty_alias p -> it.it_path p
    | Mty_signature sg -> it.it_signature it sg
    | Mty_functor (_, mto, mt) ->
        may (it.it_module_type it) mto;
        it.it_module_type it mt
  et it_class_type it = fonction
      Cty_constr (p, tyl, cty) ->
        it.it_path p;
        List.iter (it.it_type_expr it) tyl;
        it.it_class_type it cty
    | Cty_signature cs ->
        it.it_type_expr it cs.csig_self;
        Vars.iter (fonc _ (_,_,ty) -> it.it_type_expr it ty) cs.csig_vars;
        List.iter
          (fonc (p, tl) -> it.it_path p; List.iter (it.it_type_expr it) tl)
          cs.csig_inher
    | Cty_arrow  (_, ty, cty) ->
        it.it_type_expr it ty;
        it.it_class_type it cty
  et it_type_kind it = fonction
      Type_abstract -> ()
    | Type_record (ll, _) ->
        List.iter (fonc ld -> it.it_type_expr it ld.ld_type) ll
    | Type_variant cl ->
        List.iter (fonc cd ->
          List.iter (it.it_type_expr it) cd.cd_args;
          may (it.it_type_expr it) cd.cd_res)
          cl
  et it_type_expr it ty =
    iter_type_expr (it.it_type_expr it) ty;
    filtre ty.desc avec
      Tconstr (p, _, _)
    | Tobject (_, {contents=Some (p, _)})
    | Tpackage (p, _, _) ->
        it.it_path p
    | Tvariant row ->
        may (fonc (p,_) -> it.it_path p) (row_repr row).row_name
    | _ -> ()
  et it_path p = ()
  dans
  { it_path; it_type_expr; it_type_kind; it_class_type; it_module_type;
    it_signature; it_class_type_declaration; it_class_declaration;
    it_modtype_declaration; it_module_declaration; it_exception_declaration;
    it_type_declaration; it_value_description; it_signature_item; }

soit copy_row f fixed row keep more =
  soit fields = List.map
      (fonc (l, fi) -> l,
        filtre row_field_repr fi avec
        | Rpresent(Some ty) -> Rpresent(Some(f ty))
        | Reither(c, tl, m, e) ->
            soit e = si keep alors e sinon ref None dans
            soit m = si row.row_fixed alors fixed sinon m dans
            soit tl = List.map f tl dans
            Reither(c, tl, m, e)
        | _ -> fi)
      row.row_fields dans
  soit name =
    filtre row.row_name avec None -> None
    | Some (path, tl) -> Some (path, List.map f tl) dans
  { row_fields = fields; row_more = more;
    row_bound = (); row_fixed = row.row_fixed && fixed;
    row_closed = row.row_closed; row_name = name; }

soit rec copy_kind = fonction
    Fvar{contents = Some k} -> copy_kind k
  | Fvar _   -> Fvar (ref None)
  | Fpresent -> Fpresent
  | Fabsent  -> affirme faux

soit copy_commu c =
  si commu_repr c = Cok alors Cok sinon Clink (ref Cunknown)

(* Since univars may be used as row variables, we need to do some
   encoding during substitution *)
soit rec norm_univar ty =
  filtre ty.desc avec
    Tunivar _ | Tsubst _ -> ty
  | Tlink ty           -> norm_univar ty
  | Ttuple (ty :: _)   -> norm_univar ty
  | _                  -> affirme faux

soit rec copy_type_desc ?(keep_names=faux) f = fonction
    Tvar _ tel ty        -> si keep_names alors ty sinon Tvar None
  | Tarrow (p, ty1, ty2, c)-> Tarrow (p, f ty1, f ty2, copy_commu c)
  | Ttuple l            -> Ttuple (List.map f l)
  | Tconstr (p, l, _)   -> Tconstr (p, List.map f l, ref Mnil)
  | Tobject(ty, {contents = Some (p, tl)})
                        -> Tobject (f ty, ref (Some(p, List.map f tl)))
  | Tobject (ty, _)     -> Tobject (f ty, ref None)
  | Tvariant row        -> affirme faux (* too ambiguous *)
  | Tfield (p, k, ty1, ty2) -> (* the kind is kept shared *)
      Tfield (p, field_kind_repr k, f ty1, f ty2)
  | Tnil                -> Tnil
  | Tlink ty            -> copy_type_desc f ty.desc
  | Tsubst ty           -> affirme faux
  | Tunivar _ tel ty     -> ty (* always keep the name *)
  | Tpoly (ty, tyl)     ->
      soit tyl = List.map (fonc x -> norm_univar (f x)) tyl dans
      Tpoly (f ty, tyl)
  | Tpackage (p, n, l)  -> Tpackage (p, n, List.map f l)

(* Utilities for copying *)

soit saved_desc = ref []
  (* Saved association of generic nodes with their description. *)

soit save_desc ty desc =
  saved_desc := (ty, desc)::!saved_desc

soit saved_kinds = ref [] (* duplicated kind variables *)
soit new_kinds = ref []   (* new kind variables *)
soit dup_kind r =
  (filtre !r avec None -> () | Some _ -> affirme faux);
  si not (List.memq r !new_kinds) alors début
    saved_kinds := r :: !saved_kinds;
    soit r' = ref None dans
    new_kinds := r' :: !new_kinds;
    r := Some (Fvar r')
  fin

(* Restored type descriptions. *)
soit cleanup_types () =
  List.iter (fonc (ty, desc) -> ty.desc <- desc) !saved_desc;
  List.iter (fonc r -> r := None) !saved_kinds;
  saved_desc := []; saved_kinds := []; new_kinds := []

(* Mark a type. *)
soit rec mark_type ty =
  soit ty = repr ty dans
  si ty.level >= lowest_level alors début
    ty.level <- pivot_level - ty.level;
    iter_type_expr mark_type ty
  fin

soit mark_type_node ty =
  soit ty = repr ty dans
  si ty.level >= lowest_level alors début
    ty.level <- pivot_level - ty.level;
  fin

soit mark_type_params ty =
  iter_type_expr mark_type ty

(* Remove marks from a type. *)
soit rec unmark_type ty =
  soit ty = repr ty dans
  si ty.level < lowest_level alors début
    ty.level <- pivot_level - ty.level;
    iter_type_expr unmark_type ty
  fin

soit unmark_type_decl decl =
  List.iter unmark_type decl.type_params;
  début filtre decl.type_kind avec
    Type_abstract -> ()
  | Type_variant cstrs ->
      List.iter
        (fonc d ->
          List.iter unmark_type d.cd_args;
          Misc.may unmark_type d.cd_res)
        cstrs
  | Type_record(lbls, rep) ->
      List.iter (fonc d -> unmark_type d.ld_type) lbls
  fin;
  début filtre decl.type_manifest avec
    None    -> ()
  | Some ty -> unmark_type ty
  fin

soit unmark_class_signature sign =
  unmark_type sign.csig_self;
  Vars.iter (fonc l (m, v, t) -> unmark_type t) sign.csig_vars

soit rec unmark_class_type =
  fonction
    Cty_constr (p, tyl, cty) ->
      List.iter unmark_type tyl; unmark_class_type cty
  | Cty_signature sign ->
      unmark_class_signature sign
  | Cty_arrow (_, ty, cty) ->
      unmark_type ty; unmark_class_type cty


                  (*******************************************)
                  (*  Memorization of abbreviation expansion *)
                  (*******************************************)

(* Search whether the expansion has been memorized. *)
soit rec find_expans priv p1 = fonction
    Mnil -> None
  | Mcons (priv', p2, ty0, ty, _)
    quand priv' >= priv && Path.same p1 p2 -> Some ty
  | Mcons (_, _, _, _, rem)   -> find_expans priv p1 rem
  | Mlink {contents = rem} -> find_expans priv p1 rem

(* debug: check for cycles in abbreviation. only works with -principal
let rec check_expans visited ty =
  let ty = repr ty in
  assert (not (List.memq ty visited));
  match ty.desc with
    Tconstr (path, args, abbrev) ->
      begin match find_expans path !abbrev with
        Some ty' -> check_expans (ty :: visited) ty'
      | None -> ()
      end
  | _ -> ()
*)

soit memo = ref []
        (* Contains the list of saved abbreviation expansions. *)

soit cleanup_abbrev () =
        (* Remove all memorized abbreviation expansions. *)
  List.iter (fonc abbr -> abbr := Mnil) !memo;
  memo := []

soit memorize_abbrev mem priv path v v' =
        (* Memorize the expansion of an abbreviation. *)
  mem := Mcons (priv, path, v, v', !mem);
  (* check_expans [] v; *)
  memo := mem :: !memo

soit rec forget_abbrev_rec mem path =
  filtre mem avec
    Mnil ->
      affirme faux
  | Mcons (_, path', _, _, rem) quand Path.same path path' ->
      rem
  | Mcons (priv, path', v, v', rem) ->
      Mcons (priv, path', v, v', forget_abbrev_rec rem path)
  | Mlink mem' ->
      mem' := forget_abbrev_rec !mem' path;
      raise Exit

soit forget_abbrev mem path =
  essaie mem := forget_abbrev_rec !mem path avec Exit -> ()

(* debug: check for invalid abbreviations
let rec check_abbrev_rec = function
    Mnil -> true
  | Mcons (_, ty1, ty2, rem) ->
      repr ty1 != repr ty2
  | Mlink mem' ->
      check_abbrev_rec !mem'

let check_memorized_abbrevs () =
  List.for_all (fun mem -> check_abbrev_rec !mem) !memo
*)

                  (**********************************)
                  (*  Utilities for labels          *)
                  (**********************************)

soit is_optional l =
  String.length l > 0 && l.[0] = '?'

soit label_name l =
  si is_optional l alors String.sub l 1 (String.length l - 1)
                   sinon l

soit rec extract_label_aux hd l = fonction
    [] -> raise Not_found
  | (l',t tel p) :: ls ->
      si label_name l' = l alors (l', t, List.rev hd, ls)
      sinon extract_label_aux (p::hd) l ls

soit extract_label l ls = extract_label_aux [] l ls


                  (**********************************)
                  (*  Utilities for backtracking    *)
                  (**********************************)

type change =
    Ctype de type_expr * type_desc
  | Clevel de type_expr * int
  | Cname de
      (Path.t * type_expr list) option ref * (Path.t * type_expr list) option
  | Crow de row_field option ref * row_field option
  | Ckind de field_kind option ref * field_kind option
  | Ccommu de commutable ref * commutable
  | Cuniv de type_expr option ref * type_expr option
  | Ctypeset de TypeSet.t ref * TypeSet.t

soit undo_change = fonction
    Ctype  (ty, desc) -> ty.desc <- desc
  | Clevel (ty, level) -> ty.level <- level
  | Cname  (r, v) -> r := v
  | Crow   (r, v) -> r := v
  | Ckind  (r, v) -> r := v
  | Ccommu (r, v) -> r := v
  | Cuniv  (r, v) -> r := v
  | Ctypeset (r, v) -> r := v

type changes =
    Change de change * changes ref
  | Unchanged
  | Invalid

type snapshot = changes ref * int

soit trail = Weak.create 1
soit last_snapshot = ref 0

soit log_change ch =
  filtre Weak.get trail 0 avec None -> ()
  | Some r ->
      soit r' = ref Unchanged dans
      r := Change (ch, r');
      Weak.set trail 0 (Some r')

soit log_type ty =
  si ty.id <= !last_snapshot alors log_change (Ctype (ty, ty.desc))
soit link_type ty ty' =
  log_type ty;
  soit desc = ty.desc dans
  ty.desc <- Tlink ty';
  (* Name is a user-supplied name for this unification variable (obtained
   * through a type annotation for instance). *)
  filtre desc, ty'.desc avec
    Tvar name, Tvar name' ->
      début filtre name, name' avec
      | Some _, None ->  log_type ty'; ty'.desc <- Tvar name
      | None, Some _ ->  ()
      | Some _, Some _ ->
          si ty.level < ty'.level alors (log_type ty'; ty'.desc <- Tvar name)
      | None, None   ->  ()
      fin
  | _ -> ()
  (* ; assert (check_memorized_abbrevs ()) *)
  (*  ; check_expans [] ty' *)
soit set_level ty level =
  si ty.id <= !last_snapshot alors log_change (Clevel (ty, ty.level));
  ty.level <- level
soit set_univar rty ty =
  log_change (Cuniv (rty, !rty)); rty := Some ty
soit set_name nm v =
  log_change (Cname (nm, !nm)); nm := v
soit set_row_field e v =
  log_change (Crow (e, !e)); e := Some v
soit set_kind rk k =
  log_change (Ckind (rk, !rk)); rk := Some k
soit set_commu rc c =
  log_change (Ccommu (rc, !rc)); rc := c
soit set_typeset rs s =
  log_change (Ctypeset (rs, !rs)); rs := s

soit snapshot () =
  soit old = !last_snapshot dans
  last_snapshot := !new_id;
  filtre Weak.get trail 0 avec Some r -> (r, old)
  | None ->
      soit r = ref Unchanged dans
      Weak.set trail 0 (Some r);
      (r, old)

soit rec rev_log accu = fonction
    Unchanged -> accu
  | Invalid -> affirme faux
  | Change (ch, next) ->
      soit d = !next dans
      next := Invalid;
      rev_log (ch::accu) d

soit backtrack (changes, old) =
  filtre !changes avec
    Unchanged -> last_snapshot := old
  | Invalid -> failwith "Btype.backtrack"
  | Change _ tel change ->
      cleanup_abbrev ();
      soit backlog = rev_log [] change dans
      List.iter undo_change backlog;
      changes := Unchanged;
      last_snapshot := old;
      Weak.set trail 0 (Some changes)
