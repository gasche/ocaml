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

(* Compute constructor and label descriptions from type declarations,
   determining their representation. *)

ouvre Asttypes
ouvre Types
ouvre Btype

(* Simplified version of Ctype.free_vars *)
soit free_vars ty =
  soit ret = ref TypeSet.empty dans
  soit rec loop ty =
    soit ty = repr ty dans
    si ty.level >= lowest_level alors début
      ty.level <- pivot_level - ty.level;
      filtre ty.desc avec
      | Tvar _ ->
          ret := TypeSet.add ty !ret
      | Tvariant row ->
          soit row = row_repr row dans
          iter_row loop row;
          si not (static_row row) alors loop row.row_more
      | _ ->
          iter_type_expr loop ty
    fin
  dans
  loop ty;
  unmark_type ty;
  !ret

soit constructor_descrs ty_res cstrs priv =
  soit num_consts = ref 0 et num_nonconsts = ref 0  et num_normal = ref 0 dans
  List.iter
    (fonc {cd_args; cd_res; _} ->
      si cd_args = [] alors incr num_consts sinon incr num_nonconsts;
      si cd_res = None alors incr num_normal)
    cstrs;
  soit rec describe_constructors idx_const idx_nonconst = fonction
      [] -> []
    | {cd_id; cd_args; cd_res; cd_loc; cd_attributes} :: rem ->
        soit ty_res =
          filtre cd_res avec
          | Some ty_res' -> ty_res'
          | None -> ty_res
        dans
        soit (tag, descr_rem) =
          filtre cd_args avec
            [] -> (Cstr_constant idx_const,
                   describe_constructors (idx_const+1) idx_nonconst rem)
          | _  -> (Cstr_block idx_nonconst,
                   describe_constructors idx_const (idx_nonconst+1) rem) dans
        soit existentials =
          filtre cd_res avec
          | None -> []
          | Some type_ret ->
              soit res_vars = free_vars type_ret dans
              soit arg_vars = free_vars (newgenty (Ttuple cd_args)) dans
              TypeSet.elements (TypeSet.diff arg_vars res_vars)
        dans
        soit cstr =
          { cstr_name = Ident.name cd_id;
            cstr_res = ty_res;
            cstr_existentials = existentials;
            cstr_args = cd_args;
            cstr_arity = List.length cd_args;
            cstr_tag = tag;
            cstr_consts = !num_consts;
            cstr_nonconsts = !num_nonconsts;
            cstr_normal = !num_normal;
            cstr_private = priv;
            cstr_generalized = cd_res <> None;
            cstr_loc = cd_loc;
            cstr_attributes = cd_attributes;
          } dans
        (cd_id, cstr) :: descr_rem dans
  describe_constructors 0 0 cstrs

soit exception_descr path_exc decl =
  { cstr_name = Path.last path_exc;
    cstr_res = Predef.type_exn;
    cstr_existentials = [];
    cstr_args = decl.exn_args;
    cstr_arity = List.length decl.exn_args;
    cstr_tag = Cstr_exception (path_exc, decl.exn_loc);
    cstr_consts = -1;
    cstr_nonconsts = -1;
    cstr_private = Public;
    cstr_normal = -1;
    cstr_generalized = faux;
    cstr_loc = decl.exn_loc;
    cstr_attributes = decl.exn_attributes;
  }

soit none = {desc = Ttuple []; level = -1; id = -1}
                                        (* Clearly ill-formed type *)
soit dummy_label =
  { lbl_name = ""; lbl_res = none; lbl_arg = none; lbl_mut = Immutable;
    lbl_pos = (-1); lbl_all = [||]; lbl_repres = Record_regular;
    lbl_private = Public;
    lbl_loc = Location.none;
    lbl_attributes = [];
  }

soit label_descrs ty_res lbls repres priv =
  soit all_labels = Array.create (List.length lbls) dummy_label dans
  soit rec describe_labels num = fonction
      [] -> []
    | l :: rest ->
        soit lbl =
          { lbl_name = Ident.name l.ld_id;
            lbl_res = ty_res;
            lbl_arg = l.ld_type;
            lbl_mut = l.ld_mutable;
            lbl_pos = num;
            lbl_all = all_labels;
            lbl_repres = repres;
            lbl_private = priv;
            lbl_loc = l.ld_loc;
            lbl_attributes = l.ld_attributes;
          } dans
        all_labels.(num) <- lbl;
        (l.ld_id, lbl) :: describe_labels (num+1) rest dans
  describe_labels 0 lbls

exception Constr_not_found

soit rec find_constr tag num_const num_nonconst = fonction
    [] ->
      raise Constr_not_found
  | {cd_args = []; _} tel c  :: rem ->
      si tag = Cstr_constant num_const
      alors c
      sinon find_constr tag (num_const + 1) num_nonconst rem
  | c :: rem ->
      si tag = Cstr_block num_nonconst
      alors c
      sinon find_constr tag num_const (num_nonconst + 1) rem

soit find_constr_by_tag tag cstrlist =
  find_constr tag 0 0 cstrlist
