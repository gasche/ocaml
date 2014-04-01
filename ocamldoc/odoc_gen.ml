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

(** *)

classe type doc_generator =
  objet méthode generate : Odoc_module.t_module list -> unit fin;;

module type Base = sig
    classe generator : doc_generator
  fin;;

module Base_generator : Base = struct
  classe generator : doc_generator = objet méthode generate l = () fin
  fin;;

module type Base_functor = foncteur (G: Base) -> Base
module type Html_functor = foncteur (G: Odoc_html.Html_generator) -> Odoc_html.Html_generator
module type Latex_functor = foncteur (G: Odoc_latex.Latex_generator) -> Odoc_latex.Latex_generator
module type Texi_functor = foncteur (G: Odoc_texi.Texi_generator) -> Odoc_texi.Texi_generator
module type Man_functor = foncteur (G: Odoc_man.Man_generator) -> Odoc_man.Man_generator
module type Dot_functor = foncteur (G: Odoc_dot.Dot_generator) -> Odoc_dot.Dot_generator

type generator =
  | Html de (module Odoc_html.Html_generator)
  | Latex de (module Odoc_latex.Latex_generator)
  | Texi de (module Odoc_texi.Texi_generator)
  | Man de (module Odoc_man.Man_generator)
  | Dot de (module Odoc_dot.Dot_generator)
  | Base de (module Base)
;;

soit get_minimal_generator = fonction
  Html m ->
    soit module M = (val m : Odoc_html.Html_generator) dans
    (nouv M.html :> doc_generator)
| Latex m ->
    soit module M = (val m : Odoc_latex.Latex_generator) dans
    (nouv M.latex :> doc_generator)
| Man m ->
    soit module M = (val m : Odoc_man.Man_generator) dans
    (nouv M.man :> doc_generator)
| Texi m ->
    soit module M = (val m : Odoc_texi.Texi_generator) dans
    (nouv M.texi :> doc_generator)
| Dot m ->
    soit module M = (val m : Odoc_dot.Dot_generator) dans
    (nouv M.dot :> doc_generator)
| Base m ->
    soit module M = (val m : Base) dans
    nouv M.generator
    ;;
