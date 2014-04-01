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

(** Representation and manipulation of modules and module types. *)

soit print_DEBUG s = print_string s ; print_newline ()

module Name = Odoc_name

(** To keep the order of elements in a module. *)
type module_element =
    Element_module de t_module
  | Element_module_type de t_module_type
  | Element_included_module de included_module
  | Element_class de Odoc_class.t_class
  | Element_class_type de Odoc_class.t_class_type
  | Element_value de Odoc_value.t_value
  | Element_exception de Odoc_exception.t_exception
  | Element_type de Odoc_type.t_type
  | Element_module_comment de Odoc_types.text

(** Used where we can reference t_module or t_module_type *)
et mmt =
  | Mod de t_module
  | Modtype de t_module_type

et included_module = {
    im_name : Name.t ; (** the name of the included module *)
    modifiable im_module : mmt option ; (** the included module or module type *)
    modifiable im_info : Odoc_types.info option ; (** comment associated to the includ directive *)
  }

et module_alias = {
    ma_name : Name.t ;
    modifiable ma_module : mmt option ; (** the real module or module type if we could associate it *)
  }

et module_parameter = {
    mp_name : string ; (** the name *)
    mp_type : Types.module_type option ; (** the type *)
    mp_type_code : string ; (** the original code *)
    mp_kind : module_type_kind ; (** the way the parameter was built *)
  }

(** Different kinds of module. *)
et module_kind =
  | Module_struct de module_element list
  | Module_alias de module_alias (** complete name and corresponding module if we found it *)
  | Module_functor de module_parameter * module_kind
  | Module_apply de module_kind * module_kind
  | Module_with de module_type_kind * string
  | Module_constraint de module_kind * module_type_kind
  | Module_typeof de string (** by now only the code of the module expression *)
  | Module_unpack de string * module_type_alias (** code of the expression and module type alias *)

(** Representation of a module. *)
et t_module = {
    m_name : Name.t ;
    modifiable m_type : Types.module_type ;
    modifiable m_info : Odoc_types.info option ;
    m_is_interface : bool ; (** true for modules read from interface files *)
    m_file : string ; (** the file the module is defined in. *)
    modifiable m_kind : module_kind ;
    modifiable m_loc : Odoc_types.location ;
    modifiable m_top_deps : Name.t list ; (** The toplevels module names this module depends on. *)
    modifiable m_code : string option ; (** The whole code of the module *)
    modifiable m_code_intf : string option ; (** The whole code of the interface of the module *)
    m_text_only : bool ; (** [true] if the module comes from a text file *)
  }

et module_type_alias = {
    mta_name : Name.t ;
    modifiable mta_module : t_module_type option ; (** the real module type if we could associate it *)
  }

(** Different kinds of module type. *)
et module_type_kind =
  | Module_type_struct de module_element list
  | Module_type_functor de module_parameter * module_type_kind
  | Module_type_alias de module_type_alias (** complete name and corresponding module type if we found it *)
  | Module_type_with de module_type_kind * string (** the module type kind and the code of the with constraint *)
  | Module_type_typeof de string (** by now only the code of the module expression *)

(** Representation of a module type. *)
et t_module_type = {
    mt_name : Name.t ;
    modifiable mt_info : Odoc_types.info option ;
    modifiable mt_type : Types.module_type option ; (** [None] = abstract module type *)
    mt_is_interface : bool ; (** true for modules read from interface files *)
    mt_file : string ; (** the file the module type is defined in. *)
    modifiable mt_kind : module_type_kind option ; (** [None] = abstract module type if mt_type = None ;
                                           Always [None] when the module type was extracted from the implementation file. *)
    modifiable mt_loc : Odoc_types.location ;
  }


(** {2 Functions} *)

(** Returns the list of values from a list of module_element. *)
soit values l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_value v -> acc @ [v]
      | _ -> acc
    )
    []
    l

(** Returns the list of types from a list of module_element. *)
soit types l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_type t -> acc @ [t]
      | _ -> acc
    )
    []
    l

(** Returns the list of exceptions from a list of module_element. *)
soit exceptions l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_exception e -> acc @ [e]
      | _ -> acc
    )
    []
    l

(** Returns the list of classes from a list of module_element. *)
soit classes l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_class c -> acc @ [c]
      | _ -> acc
    )
    []
    l

(** Returns the list of class types from a list of module_element. *)
soit class_types l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_class_type ct -> acc @ [ct]
      | _ -> acc
    )
    []
    l

(** Returns the list of modules from a list of module_element. *)
soit modules l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_module m -> acc @ [m]
      | _ -> acc
    )
    []
    l

(** Returns the list of module types from a list of module_element. *)
soit mod_types l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_module_type mt -> acc @ [mt]
      | _ -> acc
    )
    []
    l

(** Returns the list of module comment from a list of module_element. *)
soit comments l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_module_comment t -> acc @ [t]
      | _ -> acc
    )
    []
    l

(** Returns the list of included modules from a list of module_element. *)
soit included_modules l =
  List.fold_left
    (fonc acc -> fonc ele ->
      filtre ele avec
        Element_included_module m -> acc @ [m]
      | _ -> acc
    )
    []
    l

(** Returns the list of elements of a module.
   @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit rec module_elements ?(trans=vrai) m =
  soit rec iter_kind = fonction
      Module_struct l ->
        print_DEBUG "Odoc_module.module_element: Module_struct";
        l
    | Module_alias ma ->
        print_DEBUG "Odoc_module.module_element: Module_alias";
        si trans alors
          filtre ma.ma_module avec
            None -> []
          | Some (Mod m) -> module_elements m
          | Some (Modtype mt) -> module_type_elements mt
        sinon
          []
    | Module_functor (_, k)
    | Module_apply (k, _) ->
        print_DEBUG "Odoc_module.module_element: Module_functor ou Module_apply";
        iter_kind k
    | Module_with (tk,_) ->
        print_DEBUG "Odoc_module.module_element: Module_with";
        module_type_elements ~trans: trans
          { mt_name = "" ; mt_info = None ; mt_type = None ;
            mt_is_interface = faux ; mt_file = "" ; mt_kind = Some tk ;
            mt_loc = Odoc_types.dummy_loc ;
          }
    | Module_constraint (k, tk) ->
        print_DEBUG "Odoc_module.module_element: Module_constraint";
      (* A VOIR : utiliser k ou tk ? *)
        module_elements ~trans: trans
          { m_name = "" ;
            m_info = None ;
            m_type = Types.Mty_signature [] ;
            m_is_interface = faux ; m_file = "" ; m_kind = k ;
            m_loc = Odoc_types.dummy_loc ;
            m_top_deps = [] ;
            m_code = None ;
            m_code_intf = None ;
            m_text_only = faux ;
          }
    | Module_typeof _ -> []
    | Module_unpack _ -> []
(*
   module_type_elements ~trans: trans
   { mt_name = "" ; mt_info = None ; mt_type = None ;
   mt_is_interface = false ; mt_file = "" ; mt_kind = Some tk ;
   mt_loc = Odoc_types.dummy_loc }
*)
  dans
  iter_kind m.m_kind

(** Returns the list of elements of a module type.
   @param trans indicates if, for aliased modules, we must perform a transitive search.*)
et module_type_elements ?(trans=vrai) mt =
  soit rec iter_kind = fonction
    | None -> []
    | Some (Module_type_struct l) -> l
    | Some (Module_type_functor (_, k)) -> iter_kind (Some k)
    | Some (Module_type_with (k, _)) ->
        si trans alors
          iter_kind (Some k)
        sinon
          []
    | Some (Module_type_alias mta) ->
        si trans alors
          filtre mta.mta_module avec
            None -> []
          | Some mt -> module_type_elements mt
        sinon
          []
  | Some (Module_type_typeof _) -> []
  dans
  iter_kind mt.mt_kind

(** Returns the list of values of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_values ?(trans=vrai) m = values (module_elements ~trans m)

(** Returns the list of functional values of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_functions ?(trans=vrai) m =
  List.filter
    (fonc v -> Odoc_value.is_function v)
    (values (module_elements ~trans m))

(** Returns the list of non-functional values of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_simple_values ?(trans=vrai) m =
    List.filter
    (fonc v -> not (Odoc_value.is_function v))
    (values (module_elements ~trans m))

(** Returns the list of types of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_types ?(trans=vrai) m = types (module_elements ~trans m)

(** Returns the list of excptions of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_exceptions ?(trans=vrai) m = exceptions (module_elements ~trans m)

(** Returns the list of classes of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_classes ?(trans=vrai) m = classes (module_elements ~trans m)

(** Returns the list of class types of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_class_types ?(trans=vrai) m = class_types (module_elements ~trans m)

(** Returns the list of modules of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_modules ?(trans=vrai) m = modules (module_elements ~trans m)

(** Returns the list of module types of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_module_types ?(trans=vrai) m = mod_types (module_elements ~trans m)

(** Returns the list of included module of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_included_modules ?(trans=vrai) m = included_modules (module_elements ~trans m)

(** Returns the list of comments of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_comments ?(trans=vrai) m = comments (module_elements ~trans m)

(** Access to the parameters, for a functor type.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit rec module_type_parameters ?(trans=vrai) mt =
  soit rec iter k =
    filtre k avec
      Some (Module_type_functor (p, k2)) ->
        soit param =
           (* we create the couple (parameter, description opt), using
              the description of the parameter if we can find it in the comment.*)
          filtre mt.mt_info avec
            None -> (p, None)
          | Some i ->
              essaie
                soit d = List.assoc p.mp_name i.Odoc_types.i_params dans
                (p, Some d)
              avec
                Not_found ->
                  (p, None)
        dans
        param :: (iter (Some k2))
    | Some (Module_type_alias mta) ->
        si trans alors
          filtre mta.mta_module avec
            None -> []
          | Some mt2 -> module_type_parameters ~trans mt2
        sinon
          []
    | Some (Module_type_with (k, _)) ->
        si trans alors
          iter (Some k)
        sinon
          []
    | Some (Module_type_struct _) ->
        []
    | Some (Module_type_typeof _) -> []
      | None ->
        []
  dans
  iter mt.mt_kind

(** Access to the parameters, for a functor.
   @param trans indicates if, for aliased modules, we must perform a transitive search.*)
et module_parameters ?(trans=vrai) m =
  soit rec iter = fonction
      Module_functor (p, k) ->
        soit param =
         (* we create the couple (parameter, description opt), using
            the description of the parameter if we can find it in the comment.*)
          filtre m.m_info avec
            None ->(p, None)
          | Some i ->
              essaie
                soit d = List.assoc p.mp_name i.Odoc_types.i_params dans
                (p, Some d)
              avec
                Not_found ->
                  (p, None)
        dans
        param :: (iter k)

    | Module_alias ma ->
        si trans alors
          filtre ma.ma_module avec
            None -> []
          | Some (Mod m) -> module_parameters ~trans m
          | Some (Modtype mt) -> module_type_parameters ~trans mt
        sinon
          []
    | Module_constraint (k, tk) ->
        module_type_parameters ~trans: trans
          { mt_name = "" ; mt_info = None ; mt_type = None ;
            mt_is_interface = faux ; mt_file = "" ; mt_kind = Some tk ;
            mt_loc = Odoc_types.dummy_loc }
    | Module_struct _
    | Module_apply _
    | Module_with _
    | Module_typeof _
    | Module_unpack _ -> []
  dans
  iter m.m_kind

(** access to all submodules and sudmobules of submodules ... of the given module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit rec module_all_submodules ?(trans=vrai) m =
  soit l = module_modules ~trans m dans
  List.fold_left
    (fonc acc -> fonc m -> acc @ (module_all_submodules ~trans m))
    l
    l

(** The module type is a functor if is defined as a functor or if it is an alias for a functor. *)
soit rec module_type_is_functor mt =
  soit rec iter k =
    filtre k avec
      Some (Module_type_functor _) -> vrai
    | Some (Module_type_alias mta) ->
        (
         filtre mta.mta_module avec
           None -> faux
         | Some mtyp -> module_type_is_functor mtyp
        )
    | Some (Module_type_with (k, _)) ->
        iter (Some k)
    | Some (Module_type_struct _)
    | Some (Module_type_typeof _)
    | None -> faux
  dans
  iter mt.mt_kind

(** The module is a functor if is defined as a functor or if it is an alias for a functor. *)
soit module_is_functor m =
  soit rec iter = fonction
      Module_functor _ -> vrai
    | Module_alias ma ->
        (
         filtre ma.ma_module avec
           None -> faux
         | Some (Mod mo) -> iter mo.m_kind
         | Some (Modtype mt) -> module_type_is_functor mt
        )
    | Module_constraint (k, _) ->
        iter k
    | _ -> faux
  dans
  iter m.m_kind

(** Returns the list of values of a module type.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_values ?(trans=vrai) m = values (module_type_elements ~trans m)

(** Returns the list of types of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_types ?(trans=vrai) m = types (module_type_elements ~trans m)

(** Returns the list of excptions of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_exceptions ?(trans=vrai) m = exceptions (module_type_elements ~trans m)

(** Returns the list of classes of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_classes ?(trans=vrai) m = classes (module_type_elements ~trans m)

(** Returns the list of class types of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_class_types ?(trans=vrai) m = class_types (module_type_elements ~trans m)

(** Returns the list of modules of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_modules ?(trans=vrai)  m = modules (module_type_elements ~trans m)

(** Returns the list of module types of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_module_types ?(trans=vrai) m = mod_types (module_type_elements ~trans m)

(** Returns the list of included module of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_included_modules ?(trans=vrai) m = included_modules (module_type_elements ~trans m)

(** Returns the list of comments of a module.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_comments ?(trans=vrai) m = comments (module_type_elements ~trans m)

(** Returns the list of functional values of a module type.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_functions ?(trans=vrai) mt =
  List.filter
    (fonc v -> Odoc_value.is_function v)
    (values (module_type_elements ~trans mt))

(** Returns the list of non-functional values of a module type.
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit module_type_simple_values ?(trans=vrai) mt =
    List.filter
    (fonc v -> not (Odoc_value.is_function v))
    (values (module_type_elements ~trans mt))

(** {2 Functions for modules and module types} *)

(** The list of classes defined in this module and all its modules, functors, ....
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
soit rec module_all_classes ?(trans=vrai) m =
  List.fold_left
    (fonc acc -> fonc m -> acc @ (module_all_classes ~trans m))
    (
       List.fold_left
       (fonc acc -> fonc mtyp -> acc @ (module_type_all_classes ~trans mtyp))
       (module_classes ~trans m)
       (module_module_types ~trans m)
    )
    (module_modules ~trans m)

(** The list of classes defined in this module type and all its modules, functors, ....
  @param trans indicates if, for aliased modules, we must perform a transitive search.*)
et module_type_all_classes ?(trans=vrai) mt =
  List.fold_left
    (fonc acc -> fonc m -> acc @ (module_all_classes ~trans m))
    (
     List.fold_left
       (fonc acc -> fonc mtyp -> acc @ (module_type_all_classes ~trans mtyp))
       (module_type_classes ~trans mt)
       (module_type_module_types ~trans mt)
    )
    (module_type_modules ~trans mt)
