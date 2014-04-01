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

(** Representation and manipulation of classes and class types.*)

module Name = Odoc_name

(** To keep the order of elements in a class *)
type class_element =
    Class_attribute de Odoc_value.t_attribute
  | Class_method de Odoc_value.t_method
  | Class_comment de Odoc_types.text

(** Used when we can reference t_class or t_class_type. *)
type cct =
    Cl de t_class
  | Cltype de t_class_type * Types.type_expr list (** class type and type parameters *)

et inherited_class = {
    ic_name : Name.t ; (** Complete name of the inherited class *)
    modifiable ic_class : cct option ; (** The associated t_class or t_class_type *)
    ic_text : Odoc_types.text option ; (** The inheritance comment, if any *)
  }

et class_apply = {
    capp_name : Name.t ; (** The complete name of the applied class *)
    modifiable capp_class : t_class option;  (** The associated t_class if we found it *)
    capp_params : Types.type_expr list; (** The type of expressions the class is applied to *)
    capp_params_code : string list ; (** The code of these expressions *)
  }

et class_constr = {
    cco_name : Name.t ; (** The complete name of the applied class *)
    modifiable cco_class : cct option;  (** The associated class ot class type if we found it *)
    cco_type_parameters : Types.type_expr list; (** The type parameters of the class, if needed *)
  }


et class_kind =
    Class_structure de inherited_class list * class_element list
        (** an explicit class structure, used in implementation and interface *)
  | Class_apply de class_apply (** application/alias of a class, used in implementation only *)
  | Class_constr de class_constr (** a class used to give the type of the defined class,
                                    instead of a structure, used in interface only.
                                    For example, it will be used with the name "M1.M2....tutu"
                                    when the class to is defined like this :
                                    class toto : int -> tutu *)
  | Class_constraint de class_kind * class_type_kind
        (** A class definition with a constraint. *)

(** Representation of a class. *)
et t_class = {
    cl_name : Name.t ; (** Name of the class *)
    modifiable cl_info : Odoc_types.info option ; (** The optional associated user information *)
    cl_type : Types.class_type ;
    cl_type_parameters : Types.type_expr list ; (** Type parameters *)
    cl_virtual : bool ; (** true = virtual *)
    modifiable cl_kind : class_kind ;
    modifiable cl_parameters : Odoc_parameter.parameter list ;
    modifiable cl_loc : Odoc_types.location ;
  }

et class_type_alias = {
    cta_name : Name.t ;
    modifiable cta_class : cct option ; (** we can have a t_class or a t_class_type *)
    cta_type_parameters : Types.type_expr list ; (** the type parameters *)
  }

et class_type_kind =
    Class_signature de inherited_class list * class_element list
  | Class_type de class_type_alias (** a class type eventually applied to type args *)

(** Representation of a class type. *)
et t_class_type = {
    clt_name : Name.t ;
    modifiable clt_info : Odoc_types.info option ; (** The optional associated user information *)
    clt_type : Types.class_type ;
    clt_type_parameters : Types.type_expr list ; (** type parameters *)
    clt_virtual : bool ; (** true = virtual *)
    modifiable clt_kind : class_type_kind ;
    modifiable clt_loc : Odoc_types.location ;
  }


(** {2 Functions} *)

(** Returns the text associated to the given parameter label
   in the given class, or None. *)
soit class_parameter_text_by_name cl label =
  filtre cl.cl_info avec
    None -> None
  | Some i ->
      essaie
        soit t = List.assoc label i.Odoc_types.i_params dans
        Some t
      avec
        Not_found ->
          None

(** Returns the list of elements of a t_class. *)
soit rec class_elements ?(trans=vrai) cl =
  soit rec iter_kind k =
    filtre k avec
      Class_structure (_, elements) -> elements
    | Class_constraint (c_kind, ct_kind) ->
        iter_kind c_kind
      (* A VOIR : utiliser le c_kind ou le ct_kind ?
         Pour l'instant, comme le ct_kind n'est pas analyse,
         on cherche dans le c_kind
         class_type_elements ~trans: trans
         { clt_name = "" ; clt_info = None ;
          clt_type_parameters = [] ;
         clt_virtual = false ;
         clt_kind = ct_kind }
      *)
    | Class_apply capp ->
        (
         filtre capp.capp_class avec
           Some c quand trans -> class_elements ~trans: trans c
         | _ -> []
        )
    | Class_constr cco ->
        (
         filtre cco.cco_class avec
           Some (Cl c) quand trans -> class_elements ~trans: trans c
         | Some (Cltype (ct,_)) quand trans -> class_type_elements ~trans: trans ct
         | _ -> []
        )
  dans
  iter_kind cl.cl_kind

(** Returns the list of elements of a t_class_type. *)
et class_type_elements ?(trans=vrai) clt =
  filtre clt.clt_kind avec
    Class_signature (_, elements) -> elements
  | Class_type { cta_class = Some (Cltype (ct, _)) } quand trans ->
      class_type_elements ~trans ct
  | Class_type { cta_class = Some (Cl c) } quand trans ->
      class_elements ~trans c
  | Class_type _ ->
      []

(** Returns the attributes of a t_class. *)
soit class_attributes ?(trans=vrai) cl =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Class_attribute a ->
          acc @ [ a ]
      | _ ->
          acc
    )
    []
    (class_elements ~trans cl)

(** Returns the methods of a t_class. *)
soit class_methods ?(trans=vrai) cl =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Class_method m ->
          acc @ [ m ]
      | _ ->
          acc
    )
    []
    (class_elements ~trans cl)

(** Returns the comments in a t_class. *)
soit class_comments ?(trans=vrai) cl =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Class_comment t ->
          acc @ [ t ]
      | _ ->
          acc
    )
    []
    (class_elements ~trans cl)


(** Update the parameters text of a t_class, according to the cl_info field. *)
soit class_update_parameters_text cl =
  soit f p =
    Odoc_parameter.update_parameter_text (class_parameter_text_by_name cl) p
  dans
  List.iter f cl.cl_parameters

(** Returns the attributes of a t_class_type. *)
soit class_type_attributes ?(trans=vrai) clt =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Class_attribute a ->
          acc @ [ a ]
      | _ ->
          acc
    )
    []
    (class_type_elements ~trans clt)

(** Returns the methods of a t_class_type. *)
soit class_type_methods ?(trans=vrai) clt =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Class_method m ->
          acc @ [ m ]
      | _ ->
          acc
    )
    []
    (class_type_elements ~trans clt)

(** Returns the comments in a t_class_type. *)
soit class_type_comments ?(trans=vrai) clt =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Class_comment m ->
          acc @ [ m ]
      | _ ->
          acc
    )
    []
    (class_type_elements ~trans clt)

(** Returns the text associated to the given parameter label
   in the given class type, or None. *)
soit class_type_parameter_text_by_name clt label =
  filtre clt.clt_info avec
    None -> None
  | Some i ->
      essaie
        soit t = List.assoc label i.Odoc_types.i_params dans
        Some t
      avec
        Not_found ->
          None
