(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Representation and manipulation of values, class attributes and class methods. *)

module Name = Odoc_name

(** Types *)

(** Representation of a value. *)
type t_value = {
    val_name : Name.t ;
    modifiable val_info : Odoc_types.info option ;
    val_type : Types.type_expr ;
    val_recursive : bool ;
    modifiable val_parameters : Odoc_parameter.parameter list ;
    modifiable val_code : string option ;
    modifiable val_loc : Odoc_types.location ;
  }

(** Representation of a class attribute. *)
type t_attribute = {
    att_value : t_value ; (** an attribute has almost all the same information
                             as a value *)
    att_mutable : bool ;
    att_virtual : bool ;
  }

(** Representation of a class method. *)
type t_method = {
    met_value : t_value ; (** a method has almost all the same information
                             as a value *)
    met_private : bool ;
    met_virtual : bool ;
  }

(** Functions *)

(** Returns the text associated to the given parameter name
   in the given value, or None. *)
soit value_parameter_text_by_name v name =
  filtre v.val_info avec
    None -> None
  | Some i ->
      essaie
        soit t = List.assoc name i.Odoc_types.i_params dans
        Some t
      avec
        Not_found ->
          None

(** Update the parameters text of a t_value, according to the val_info field. *)
soit update_value_parameters_text v =
  soit f p =
    Odoc_parameter.update_parameter_text (value_parameter_text_by_name v) p
  dans
  List.iter f v.val_parameters

(** Create a list of (parameter name, typ) from a type, according to the arrows.
   [parameter_list_from_arrows t = [ a ; b ]] if t = a -> b -> c.*)
soit parameter_list_from_arrows typ =
  soit rec iter t =
    filtre t.Types.desc avec
      Types.Tarrow (l, t1, t2, _) ->
        (l, t1) :: (iter t2)
    | Types.Tlink texp
    | Types.Tsubst texp ->
        iter texp
    | Types.Tpoly (texp, _) -> iter texp
    | Types.Tvar _
    | Types.Ttuple _
    | Types.Tconstr _
    | Types.Tobject _
    | Types.Tfield _
    | Types.Tnil
    | Types.Tunivar _
    | Types.Tpackage _
    | Types.Tvariant _ ->
        []
  dans
  iter typ

(** Create a list of parameters with dummy names "??" from a type list.
   Used when we want to merge the parameters of a value, from the .ml
   and the .mli file. In the .mli file we don't have parameter names
   so there is nothing to merge. With this dummy list we can merge the
   parameter names from the .ml and the type from the .mli file. *)
soit dummy_parameter_list typ =
  soit normal_name s =
    filtre s avec
      "" -> s
    | _ ->
        filtre s.[0] avec
          '?' -> String.sub s 1 ((String.length s) - 1)
        | _ -> s
  dans
  Printtyp.mark_loops typ;
  soit liste_param = parameter_list_from_arrows typ dans
  soit rec iter (label, t) =
    filtre t.Types.desc avec
    | Types.Ttuple l ->
        si label = "" alors
          Odoc_parameter.Tuple
            (List.map (fonc t2 -> iter ("", t2)) l, t)
        sinon
          (* if there is a label, then we don't want to decompose the tuple *)
          Odoc_parameter.Simple_name
            { Odoc_parameter.sn_name = normal_name label ;
              Odoc_parameter.sn_type = t ;
              Odoc_parameter.sn_text = None }
    | Types.Tlink t2
    | Types.Tsubst t2 ->
        (iter (label, t2))

    | _ ->
        Odoc_parameter.Simple_name
          { Odoc_parameter.sn_name = normal_name label ;
             Odoc_parameter.sn_type = t ;
            Odoc_parameter.sn_text = None }
  dans
  List.map iter liste_param

(** Return true if the value is a function, i.e. has a functional type.*)
soit is_function v =
  soit rec f t =
    filtre t.Types.desc avec
      Types.Tarrow _ ->
        vrai
    | Types.Tlink t ->
        f t
        | _ ->
            faux
      dans
  f v.val_type
