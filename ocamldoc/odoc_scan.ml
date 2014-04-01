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

(** Scanning of modules and elements.

   The class scanner defined in this module can be used to
   develop generators which perform controls on the elements
   and their comments.
*)

ouvre Odoc_types

(** Class which defines the scanning of a list of modules and their
   elements. Inherit this class to develop your own scanner, by
   overriding some methods.*)
classe scanner =
  objet (self)
  (** Scan of 'leaf elements'. *)

    méthode scan_value (v : Odoc_value.t_value) = ()

    méthode scan_type_pre (t : Odoc_type.t_type) = vrai

    méthode scan_type_recfield t (f : Odoc_type.record_field) = ()
    méthode scan_type_const t (f : Odoc_type.variant_constructor) = ()
    méthode scan_type (t : Odoc_type.t_type) =
      si self#scan_type_pre t alors
        filtre t.Odoc_type.ty_kind avec
          Odoc_type.Type_abstract -> ()
        | Odoc_type.Type_variant l -> List.iter (self#scan_type_const t) l
        | Odoc_type.Type_record l -> List.iter (self#scan_type_recfield t) l

    méthode scan_exception (e : Odoc_exception.t_exception) = ()
    méthode scan_attribute (a : Odoc_value.t_attribute) = ()
    méthode scan_method (m : Odoc_value.t_method) = ()
    méthode scan_included_module (im : Odoc_module.included_module) = ()

  (** Scan of a class. *)

    (** Scan of a comment inside a class. *)
    méthode scan_class_comment (t : text) = ()

    (** Override this method to perform controls on the class comment
       and params. This method is called before scanning the class elements.
       @return true if the class elements must be scanned.*)
    méthode scan_class_pre (c : Odoc_class.t_class) = vrai

    (** This method scan the elements of the given class.
       A VOIR : scan des classes heritees.*)
    méthode scan_class_elements c =
      List.iter
        (fonc ele ->
          filtre ele avec
            Odoc_class.Class_attribute a -> self#scan_attribute a
          | Odoc_class.Class_method m -> self#scan_method m
          | Odoc_class.Class_comment t -> self#scan_class_comment t
        )
        (Odoc_class.class_elements c)

    (** Scan of a class. Should not be overridden. It calls [scan_class_pre]
      and if [scan_class_pre] returns [true], then it calls scan_class_elements.*)
    méthode scan_class c = si self#scan_class_pre c alors self#scan_class_elements c

  (** Scan of a class type. *)

    (** Scan of a comment inside a class type. *)
    méthode scan_class_type_comment (t : text) = ()

    (** Override this method to perform controls on the class type comment
       and form. This method is called before scanning the class type elements.
       @return true if the class type elements must be scanned.*)
    méthode scan_class_type_pre (ct : Odoc_class.t_class_type) = vrai

    (** This method scan the elements of the given class type.
       A VOIR : scan des classes heritees.*)
    méthode scan_class_type_elements ct =
      List.iter
        (fonc ele ->
          filtre ele avec
            Odoc_class.Class_attribute a -> self#scan_attribute a
          | Odoc_class.Class_method m -> self#scan_method m
          | Odoc_class.Class_comment t -> self#scan_class_type_comment t
        )
        (Odoc_class.class_type_elements ct)

    (** Scan of a class type. Should not be overridden. It calls [scan_class_type_pre]
      and if [scan_class_type_pre] returns [true], then it calls scan_class_type_elements.*)
    méthode scan_class_type ct = si self#scan_class_type_pre ct alors self#scan_class_type_elements ct

  (** Scan of modules. *)

    (** Scan of a comment inside a module. *)
    méthode scan_module_comment (t : text) = ()

    (** Override this method to perform controls on the module comment
       and form. This method is called before scanning the module elements.
       @return true if the module elements must be scanned.*)
    méthode scan_module_pre (m : Odoc_module.t_module) = vrai

    (** This method scan the elements of the given module. *)
    méthode scan_module_elements m =
      List.iter
        (fonc ele ->
          filtre ele avec
            Odoc_module.Element_module m -> self#scan_module m
          | Odoc_module.Element_module_type mt -> self#scan_module_type mt
          | Odoc_module.Element_included_module im -> self#scan_included_module im
          | Odoc_module.Element_class c -> self#scan_class c
          | Odoc_module.Element_class_type ct -> self#scan_class_type ct
          | Odoc_module.Element_value v -> self#scan_value v
          | Odoc_module.Element_exception e -> self#scan_exception e
          | Odoc_module.Element_type t -> self#scan_type t
          | Odoc_module.Element_module_comment t -> self#scan_module_comment t
        )
        (Odoc_module.module_elements m)

    (** Scan of a module. Should not be overridden. It calls [scan_module_pre]
      and if [scan_module_pre] returns [true], then it calls scan_module_elements.*)
    méthode scan_module m = si self#scan_module_pre m alors self#scan_module_elements m

  (** Scan of module types. *)

    (** Scan of a comment inside a module type. *)
    méthode scan_module_type_comment (t : text) = ()

    (** Override this method to perform controls on the module type comment
       and form. This method is called before scanning the module type elements.
       @return true if the module type elements must be scanned. *)
    méthode scan_module_type_pre (mt : Odoc_module.t_module_type) = vrai

    (** This method scan the elements of the given module type. *)
    méthode scan_module_type_elements mt =
      List.iter
        (fonc ele ->
          filtre ele avec
            Odoc_module.Element_module m -> self#scan_module m
          | Odoc_module.Element_module_type mt -> self#scan_module_type mt
          | Odoc_module.Element_included_module im -> self#scan_included_module im
          | Odoc_module.Element_class c -> self#scan_class c
          | Odoc_module.Element_class_type ct -> self#scan_class_type ct
          | Odoc_module.Element_value v -> self#scan_value v
          | Odoc_module.Element_exception e -> self#scan_exception e
          | Odoc_module.Element_type t -> self#scan_type t
          | Odoc_module.Element_module_comment t -> self#scan_module_comment t
        )
        (Odoc_module.module_type_elements mt)

    (** Scan of a module type. Should not be overridden. It calls [scan_module_type_pre]
      and if [scan_module_type_pre] returns [true], then it calls scan_module_type_elements.*)
    méthode scan_module_type mt =
      si self#scan_module_type_pre mt alors self#scan_module_type_elements mt

  (** Main scanning method. *)

    (** Scan a list of modules. *)
    méthode scan_module_list l = List.iter self#scan_module l
  fin
