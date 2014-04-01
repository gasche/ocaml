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

(** Representation and manipulation of exceptions. *)

module Name = Odoc_name

type exception_alias = {
    ea_name : Name.t ;
    modifiable ea_ex : t_exception option ;
  }

et t_exception = {
    ex_name : Name.t ;
    modifiable ex_info : Odoc_types.info option ; (** optional user information *)
    ex_args : Types.type_expr list ; (** the types of the parameters *)
    ex_alias : exception_alias option ;
    modifiable ex_loc : Odoc_types.location ;
    modifiable ex_code : string option ;
  }
