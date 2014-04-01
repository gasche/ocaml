(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Gallium, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2010 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** The types of generators. *)

(** The minimal class type of documentation generators. *)
classe type doc_generator =
  objet méthode generate : Odoc_module.t_module list -> unit fin;;

(** The module type of minimal generators. *)
module type Base = sig
    classe generator : doc_generator
  fin;;

module Base_generator : Base

module type Base_functor = foncteur (P: Base) -> Base
module type Html_functor = foncteur (G: Odoc_html.Html_generator) -> Odoc_html.Html_generator
module type Latex_functor = foncteur (G: Odoc_latex.Latex_generator) -> Odoc_latex.Latex_generator
module type Texi_functor = foncteur (G: Odoc_texi.Texi_generator) -> Odoc_texi.Texi_generator
module type Man_functor = foncteur (G: Odoc_man.Man_generator) -> Odoc_man.Man_generator
module type Dot_functor = foncteur (G: Odoc_dot.Dot_generator) -> Odoc_dot.Dot_generator

(** Various ways to create a generator. *)
type generator =
  | Html de (module Odoc_html.Html_generator)
  | Latex de (module Odoc_latex.Latex_generator)
  | Texi de (module Odoc_texi.Texi_generator)
  | Man de (module Odoc_man.Man_generator)
  | Dot de (module Odoc_dot.Dot_generator)
  | Base de (module Base)
;;

val get_minimal_generator : generator -> doc_generator
