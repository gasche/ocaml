(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*      Olivier Andrieu, base sur du code de Maxence Guesdon           *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Generation of Texinfo documentation. *)

ouvre Odoc_info
ouvre Parameter
ouvre Value
ouvre Type
ouvre Exception
ouvre Class
ouvre Module

soit esc_8bits = ref faux

soit info_section = ref "OCaml"

soit info_entry = ref []

(** {2 Some small helper functions} *)

soit puts_nl chan s =
  output_string chan s ;
  output_char chan '\n'
soit puts chan s =
  output_string chan s
soit nl chan =
  output_char chan '\n'

soit is = fonction
  | None -> faux
  | Some _ -> vrai

soit pad_to n s =
  soit len = String.length s dans
  si len < n
  alors
    soit s' = String.make n ' ' dans
    String.blit s 0 s' 0 len ; s'
  sinon s

soit indent nb_sp s =
  soit c = ref 0 dans
  soit len = pred (String.length s) dans
  pour i = 0 à len faire si s.[i] = '\n' alors incr c fait ;
  soit s' = String.make (succ len + (succ !c) * nb_sp ) ' ' dans
  c := nb_sp ;
  pour i = 0 à len faire
    s'.[!c] <- s.[i] ;
    si s.[i] = '\n' alors c := !c + nb_sp ;
    incr c
  fait ;
  s'

type subparts = [
  | `Module de Odoc_info.Module.t_module
  | `Module_type de Odoc_info.Module.t_module_type
  | `Class de Odoc_info.Class.t_class
  | `Class_type de Odoc_info.Class.t_class_type
  ]

type menu_data = [
  | subparts
  | `Blank
  | `Comment de string
  | `Texi de string
  | `Index de string
] list

soit nothing = Verbatim ""

soit module_subparts =
  soit rec iter acc = fonction
    | [] -> List.rev acc
    (* skip aliases *)
    | Element_module { m_kind = Module_alias _ } :: n ->
        iter acc n
    | Element_module_type { mt_kind = Some (Module_type_alias _) } :: n ->
        iter acc n
    (* keep modules, module types, classes and class types *)
    | Element_module m :: n ->
        iter (`Module m :: acc) n
    | Element_module_type mt :: n ->
        iter (`Module_type mt :: acc) n
    | Element_class c :: n ->
        iter (`Class c :: acc) n
    | Element_class_type ct :: n ->
        iter (`Class_type ct :: acc) n
    (* forget the rest *)
    | _ :: n -> iter acc n
  dans
  iter []

type indices = [
  | `Type
  | `Exception
  | `Value
  | `Class_att
  | `Method
  | `Class
  | `Class_type
  | `Module
  | `Module_type
]

soit indices = fonction
  | `Type        -> "ty"
  | `Exception   -> "ex"
  | `Value       -> "va"
  | `Class_att   -> "ca"
  | `Method      -> "me"
  | `Class       -> "cl"
  | `Class_type  -> "ct"
  | `Module      -> "mo"
  | `Module_type -> "mt"

soit indices_names = [
  "Types"           , "ty" ;
  "Exceptions"      , "ex" ;
  "Values"          , "va" ;
  "Class attributes", "ca" ;
  "Methods"         , "me" ;
  "Classes"         , "cl" ;
  "Class types"     , "ct" ;
  "Modules"         , "mo" ;
  "Module types"    , "mt" ; ]



(** Module for generating various Texinfo things (menus, xrefs, ...) *)
module Texi =
struct
  (** Associations of strings to subsitute in Texinfo code. *)
  soit subst_strings = [
    (Str.regexp "@", "@@") ;
    (Str.regexp "{", "@{") ;
    (Str.regexp "}", "@}") ;
    (Str.regexp "\\.\\.\\.", "@dots{}") ;
  ] @
    (si !esc_8bits
    alors [
    (Str.regexp "\xE0", "@`a") ;
    (Str.regexp "\xE2", "@^a") ;
    (Str.regexp "\xE9", "@'e") ;
    (Str.regexp "\xE8", "@`e") ;
    (Str.regexp "\xEA", "@^e") ;
    (Str.regexp "\xEB", "@\"e") ;
    (Str.regexp "\xF7", "@,{c}") ;
    (Str.regexp "\xF4", "@^o") ;
    (Str.regexp "\xF6", "@\"o") ;
    (Str.regexp "\xEE", "@^i") ;
    (Str.regexp "\xEF", "@\"i") ;
    (Str.regexp "\xF9", "@`u") ;
    (Str.regexp "\xFB", "@^u") ;
    (Str.regexp "\xE6", "@ae{}" ) ;
    (Str.regexp "\xC6", "@AE{}" ) ;
    (Str.regexp "\xDF", "@ss{}" ) ;
    (Str.regexp "\xA9", "@copyright{}" ) ;
    ]
    sinon [])

  (** Escape the strings which would clash with Texinfo syntax. *)
  soit escape s =
    List.fold_left
      (fonc acc (p, r) -> Str.global_replace p r acc)
      s subst_strings

  (** Removes dots (no good for a node name). *)
  soit fix_nodename s =
    Str.global_replace (Str.regexp "\\.") "/" (escape s)

  (** Generates a Texinfo menu. *)
  soit generate_menu chan subpart_list =
    si subpart_list <> []
    alors début
      soit menu_line part_qual name =
        soit sname = Name.simple name dans
        si sname = name
        alors (
          puts chan (pad_to 35
                       ("* " ^ sname ^ ":: ")) ;
          puts_nl chan part_qual )
        sinon (
          puts chan (pad_to 35
                       ("* " ^ sname ^ ": " ^ (fix_nodename name) ^ ". " )) ;
          puts_nl chan part_qual )
      dans
      puts_nl chan "@menu" ;
      List.iter
        (fonction
        | `Module { m_name = name } ->
            menu_line Odoc_messages.modul name
        | `Module_type { mt_name = name } ->
            menu_line Odoc_messages.module_type name
        | `Class { cl_name = name } ->
            menu_line Odoc_messages.clas name
        | `Class_type { clt_name = name } ->
            menu_line Odoc_messages.class_type name
        | `Blank -> nl chan
        | `Comment c -> puts_nl chan (escape c)
        | `Texi t -> puts_nl chan t
        | `Index ind -> Printf.fprintf chan "* %s::\n" ind)
      subpart_list ;
    puts_nl chan "@end menu"
  fin

  (** cross reference to node [name] *)
  soit xref ?xname name =
    "@xref{" ^ (fix_nodename name) ^
    (filtre xname avec | None -> "" | Some s -> "," ^ s) ^
    "}."

  (** enclose the string between [\@ifinfo] tags *)
  soit ifinfo s =
    String.concat "\n"
      [ "@ifinfo" ; s ; "@end ifinfo" ; "" ]

  (** [install-info] information *)
  soit dirsection sec =
    "@dircategory " ^ (escape sec)

  soit direntry ent =
    [ "@direntry" ] @
      (List.map escape ent) @
    [ "@end direntry" ]
fin





(** {2 Generation of Texinfo code} *)

(** This class generates Texinfo code from text structures *)
classe text =
  objet(self)

  (** Associations between a title number and texinfo code. *)
    val titles = [
      1, "@chapter " ;
      2, "@section " ;
      3, "@subsection " ;
      4, "@subsubsection " ;
    ]

    val fallback_title =
      "@unnumberedsubsubsec "

    val headings = [
      1, "@majorheading " ;
      2, "@heading " ;
      3, "@subheading " ;
      4, "@subsubheading " ;
    ]

    val fallback_heading =
      "@subsubheading "

    méthode escape =
      Texi.escape

    (** this method is not used here but is virtual
        in a class we will inherit later *)
    méthode label ?(no_ : bool option) (_ : string) : string =
      failwith "gni"

    (** Return the Texinfo code corresponding to the [text] parameter.*)
    méthode texi_of_text t =
      String.concat ""
        (List.map self#texi_of_text_element t)


    (** {3 Conversion methods}
       [texi_of_????] converts a [text_element] to a Texinfo string. *)

    (** Return the Texinfo code for the [text_element] in parameter. *)
    méthode texi_of_text_element = fonction
      | Verbatim s | Latex s -> self#texi_of_Verbatim s
      | Raw s -> self#texi_of_Raw s
      | Code s -> self#texi_of_Code s
      | CodePre s -> self#texi_of_CodePre s
      | Bold t -> self#texi_of_Bold t
      | Italic t -> self#texi_of_Italic t
      | Emphasize t -> self#texi_of_Emphasize t
      | Center t -> self#texi_of_Center t
      | Left t -> self#texi_of_Left t
      | Right t -> self#texi_of_Right t
      | List tl -> self#texi_of_List tl
      | Enum tl -> self#texi_of_Enum tl
      | Newline -> self#texi_of_Newline
      | Block t -> self#texi_of_Block t
      | Title (n, _, t) -> self#texi_of_Title n t
      | Link (s, t) -> self#texi_of_Link s t
      | Ref (name, kind, _) ->self#texi_of_Ref name kind
      | Superscript t -> self#texi_of_Superscript t
      | Subscript t -> self#texi_of_Subscript t
      | Odoc_info.Module_list _ -> ""
      | Odoc_info.Index_list -> ""
      | Odoc_info.Custom (s,t) -> self#texi_of_custom_text s t
      | Odoc_info.Target (target, code) -> self#texi_of_Target ~target ~code

    méthode texi_of_custom_text s t = ""

    méthode texi_of_Target ~target ~code =
      si String.lowercase target = "texi" alors code sinon ""

    méthode texi_of_Verbatim s = s
    méthode texi_of_Raw s = self#escape s
    méthode texi_of_Code s = "@code{" ^ (self#escape s) ^ "}"
    méthode texi_of_CodePre s =
      String.concat "\n"
        [ "" ;  "@example" ; self#escape s ; "@end example" ; "" ]
    méthode texi_of_Bold t = "@strong{" ^ (self#texi_of_text t) ^ "}"
    méthode texi_of_Italic t = "@i{" ^ (self#texi_of_text t) ^ "}"
    méthode texi_of_Emphasize t = "@emph{" ^ (self#texi_of_text t) ^ "}"
    méthode texi_of_Center t =
      soit sl = Str.split (Str.regexp "\n") (self#texi_of_text t) dans
      String.concat ""
        ((List.map (fonc s -> "\n@center "^s) sl) @ [ "\n" ])
    méthode texi_of_Left t =
      String.concat "\n"
        [ "" ; "@flushleft" ; self#texi_of_text t ; "@end flushleft" ; "" ]
    méthode texi_of_Right t =
      String.concat "\n"
        [ "" ; "@flushright" ; self#texi_of_text t ; "@end flushright"; "" ]
    méthode texi_of_List tl =
      String.concat "\n"
        ( [ "" ; "@itemize" ] @
          (List.map (fonc t -> "@item\n" ^ (self#texi_of_text t)) tl) @
          [ "@end itemize"; "" ] )
    méthode texi_of_Enum tl =
      String.concat "\n"
        ( [ "" ; "@enumerate" ] @
          (List.map (fonc t -> "@item\n" ^ (self#texi_of_text t)) tl) @
          [ "@end enumerate"; "" ] )
    méthode texi_of_Newline = "\n"
    méthode texi_of_Block t =
      String.concat "\n"
        [ "@format" ; self#texi_of_text t ; "@end format" ; "" ]
    méthode texi_of_Title n t =
      soit t_begin =
        essaie List.assoc n titles
        avec Not_found -> fallback_title dans
      t_begin ^ (self#texi_of_text t) ^ "\n"
    méthode texi_of_Link s t =
      String.concat ""
        [ "@uref{" ; s ;  "," ; self#texi_of_text t ; "}" ]
    méthode texi_of_Ref name kind =
      soit xname =
        filtre kind avec
        | Some RK_module ->
            Odoc_messages.modul ^ " " ^ (Name.simple name)
        | Some RK_module_type ->
            Odoc_messages.module_type ^ " " ^ (Name.simple name)
        | Some RK_class ->
            Odoc_messages.clas ^ " " ^ (Name.simple name)
        | Some RK_class_type ->
            Odoc_messages.class_type ^ " " ^ (Name.simple name)
        | _ -> ""
      dans
      si xname = "" alors self#escape name sinon Texi.xref ~xname name
    méthode texi_of_Superscript t =
      "^@{" ^ (self#texi_of_text t) ^ "@}"
    méthode texi_of_Subscript t =
      "_@{" ^ (self#texi_of_text t) ^ "@}"

    méthode heading n t =
      soit f =
        essaie List.assoc n headings
        avec Not_found -> fallback_heading
      dans
      f ^ (self#texi_of_text t) ^ "\n"

    méthode fixedblock t =
      Block ( ( Verbatim "@t{" :: t ) @ [ Verbatim "}" ] )

  fin

exception Aliased_node

module Generator =
struct

(** This class is used to create objects which can generate a simple
    Texinfo documentation. *)
classe texi =
  objet (self)
    hérite text tel to_texi
    hérite Odoc_to_text.to_text tel to_text

    (** {3 Small helper stuff.} *)

    val maxdepth = 4

    val bullet = Verbatim " @bullet{} "
    val minus  = Verbatim " @minus{} "
    val linebreak =  Verbatim "@*\n"

    val modifiable indices_to_build = [ `Module ]

    (** Keep a set of nodes we create. If we try to create one
        a second time, that means it is some kind of alias, so
        don't do it, just link to the previous one *)
    val node_tbl = Hashtbl.create 37

    méthode node depth name =
      si Hashtbl.mem node_tbl name
      alors raise Aliased_node ;
      Hashtbl.add node_tbl name () ;
      si depth <= maxdepth
      alors Verbatim ("@node " ^ (Texi.fix_nodename name) ^ ",\n")
      sinon nothing

    méthode index (ind : indices) ent =
      Verbatim
        (si !Global.with_index
        alors (affirme(List.mem ind indices_to_build) ;
              String.concat ""
                [ "@" ; indices ind ; "index " ;
                  Texi.escape (Name.simple ent) ; "\n" ])
        sinon "")


    (** Two hacks to fix linebreaks in the descriptions.*)
    méthode privée fix_linebreaks =
      soit re = Str.regexp "\n[ \t]*" dans
      fonc t ->
        List.map
          (fonction
            | Newline -> Raw "\n"
            | Raw s -> Raw (Str.global_replace re "\n" s)
            | List tes -> List (List.map self#fix_linebreaks tes)
            | Enum tes -> Enum (List.map self#fix_linebreaks tes)
            | te -> te) t

    méthode privée soft_fix_linebreaks =
      soit re = Str.regexp "\n[ \t]*" dans
      fonc ind t ->
        soit rep = String.make (succ ind) ' ' dans
        rep.[0] <- '\n' ;
        List.map
          (fonction
            | Raw s -> Raw (Str.global_replace re rep s)
            | te -> te) t

    (** {3 [text] values generation}
       Generates [text] values out of description parts.
       Redefines some of methods of {! Odoc_to_text.to_text}. *)

    méthode text_of_desc = fonction
      | None -> []
      | Some [ Raw "" ] -> []
      | Some t -> (self#fix_linebreaks t) @ [ Newline ]

    méthode text_of_sees_opt see_l =
      List.concat
        (List.map
           (fonction
             | (See_url s, t) ->
                 [ linebreak ; Bold [ Raw Odoc_messages.see_also ] ;
                   Raw " " ; Link (s, t) ; Newline ]
             | (See_file s, t)
             | (See_doc s, t)  ->
                 [ linebreak ; Bold [ Raw Odoc_messages.see_also ] ;
                   Raw " " ; Raw s ] @ t @ [ Newline ])
           see_l)

    méthode text_of_before l =
      List.flatten
      (List.map
        (fonc x -> linebreak :: (to_text#text_of_before [x])) l)

    méthode text_of_params params_list =
        List.concat
          (List.map
             (fonc (s, t) ->
               [ linebreak ;
                 Bold [ Raw Odoc_messages.parameters ] ;
                 Raw " " ; Raw s ; Raw ": " ] @ t @ [ Newline ] )
             params_list)

    méthode! text_of_raised_exceptions = fonction
      | [] -> []
      | (s, t) :: [] ->
          [ linebreak ;
            Bold [ Raw Odoc_messages.raises ] ;
            Raw " " ; Code s ; Raw " " ]
          @ t @ [ Newline ]
      | l ->
          [ linebreak ;
            Bold [ Raw Odoc_messages.raises ] ;
            Raw " :" ;
            List
              (List.map
                 (fonc (ex, desc) ->(Code ex) :: (Raw " ") :: desc ) l ) ;
            Newline ]

    méthode! text_of_return_opt = fonction
      | None -> []
      | Some t ->
          (Bold [Raw Odoc_messages.returns ]) :: Raw " " :: t @ [ Newline ]

    méthode! text_of_custom c_l =
      List.flatten
        (List.rev
           (List.fold_left
              (fonc acc -> fonc (tag, text) ->
                essaie
                  soit f = List.assoc tag tag_functions dans
                  ( linebreak :: (f text) @ [ Newline ] ) :: acc
                avec
               Not_found ->
                 Odoc_info.warning (Odoc_messages.tag_not_handled tag) ;
                 acc
              ) [] c_l))

    méthode! text_of_info ?(block=faux) = fonction
      | None -> []
      | Some info ->
          soit t =
            List.concat
                 [ ( filtre info.i_deprecated avec
                 | None -> []
                 | Some t ->
                     (Raw (Odoc_messages.deprecated ^ " ")) ::
                     (self#fix_linebreaks t)
                     @ [ Newline ; Newline ] ) ;
                   self#text_of_desc info.i_desc ;
                   si info.i_authors <> []
                   alors ( linebreak ::
                          self#text_of_author_list info.i_authors )
                   sinon [] ;
                   si is info.i_version
                   alors ( linebreak ::
                          self#text_of_version_opt info.i_version )
                   sinon [] ;
                   self#text_of_sees_opt info.i_sees ;
                   self#text_of_before info.i_before ;
                   si is info.i_since
                   alors ( linebreak ::
                          self#text_of_since_opt info.i_since )
                   sinon [] ;
                   self#text_of_params info.i_params ;
                   self#text_of_raised_exceptions info.i_raised_exceptions ;
                   si is info.i_return_value
                   alors ( linebreak ::
                          self#text_of_return_opt info.i_return_value )
                   sinon [] ;
                   self#text_of_custom info.i_custom ;
                 ] dans
          si block
          alors [ Block t ]
          sinon (t @ [ Newline ] )

    méthode texi_of_info i =
      self#texi_of_text (self#text_of_info i)

    (** {3 Conversion of [module_elements] into Texinfo strings}
       The following functions convert [module_elements] and their
       description to [text] values then to Texinfo strings using the
       functions above. *)

    méthode text_el_of_type_expr m_name typ =
      Raw (indent 5
             (self#relative_idents m_name
                (Odoc_info.string_of_type_expr typ)))

    méthode! text_of_short_type_expr m_name typ =
      [ Raw (self#normal_type m_name typ) ]

    (** Return Texinfo code for a value. *)
    méthode texi_of_value v =
      Odoc_info.reset_type_names () ;
      soit t = [ self#fixedblock
                  [ Newline ; minus ;
                    Raw ("val " ^ (Name.simple v.val_name) ^ " :\n") ;
                    self#text_el_of_type_expr
                      (Name.father v.val_name) v.val_type ] ;
                self#index `Value v.val_name ; Newline  ] @
                (self#text_of_info v.val_info) dans
      self#texi_of_text t


    (** Return Texinfo code for a class attribute. *)
    méthode texi_of_attribute a =
      Odoc_info.reset_type_names () ;
      soit t = [ self#fixedblock
                  [ Newline ; minus ;
                    Raw "val " ;
                    Raw (si a.att_virtual alors "virtual " sinon "") ;
                    Raw (si a.att_mutable alors "mutable " sinon "") ;
                    Raw (Name.simple a.att_value.val_name) ;
                    Raw " :\n" ;
                    self#text_el_of_type_expr
                      (Name.father a.att_value.val_name)
                      a.att_value.val_type ] ;
                self#index `Class_att a.att_value.val_name  ; Newline ] @
        (self#text_of_info a.att_value.val_info) dans
      self#texi_of_text t


    (** Return Texinfo code for a class method. *)
    méthode texi_of_method m =
      Odoc_info.reset_type_names () ;
      soit t = [ self#fixedblock
                  [ Newline ; minus ; Raw "method " ;
                    Raw (si m.met_private alors "private " sinon "") ;
                    Raw (si m.met_virtual alors "virtual " sinon "") ;
                    Raw (Name.simple m.met_value.val_name) ;
                    Raw " :\n" ;
                    self#text_el_of_type_expr
                      (Name.father m.met_value.val_name)
                      m.met_value.val_type ] ;
                self#index `Method m.met_value.val_name ; Newline ] @
        (self#text_of_info m.met_value.val_info) dans
      self#texi_of_text t


    méthode string_of_type_parameters t =
      soit f (tp, co, cn) =
        Printf.sprintf "%s%s"
          (Odoc_info.string_of_variance t (co, cn))
          (Odoc_info.string_of_type_expr tp)
      dans
      filtre t.ty_parameters avec
      | [] -> ""
      | [ (tp, co, cn) ] ->
          (f (tp, co, cn))^" "
      | l ->
          Printf.sprintf "(%s) "
            (String.concat ", " (List.map f l))

    méthode string_of_type_args (args:Types.type_expr list) (ret:Types.type_expr option) =
      filtre args, ret avec
      | [], None -> ""
      | args, None -> " of " ^ (Odoc_info.string_of_type_list " * " args)
      | [], Some r -> " : " ^ (Odoc_info.string_of_type_expr r)
      | args, Some r -> " : " ^ (Odoc_info.string_of_type_list " * " args) ^
                                " -> " ^ (Odoc_info.string_of_type_expr r)

    (** Return Texinfo code for a type. *)
    méthode texi_of_type ty =
      Odoc_info.reset_type_names () ;
      soit t =
        [ self#fixedblock (
          [ Newline ; minus ; Raw "type " ;
            Raw (self#string_of_type_parameters ty) ;
            Raw (Name.simple ty.ty_name) ] @
          soit priv = ty.ty_private = Asttypes.Private dans
          ( filtre ty.ty_manifest avec
          | None -> []
          | Some typ ->
              (Raw " = ") ::
              (Raw (si priv alors "private " sinon "")) ::
              (self#text_of_short_type_expr (Name.father ty.ty_name) typ) ) @
          (
           filtre ty.ty_kind avec
           | Type_abstract -> [ Newline ]
           | Type_variant l ->
               (Raw (" ="^(si priv alors " private" sinon "")^"\n")) ::
               (List.flatten
                  (List.map
                     (fonc constr ->
                       (Raw ("  | " ^ constr.vc_name)) ::
                       (Raw (self#string_of_type_args
                               constr.vc_args constr.vc_ret)) ::
                       (filtre constr.vc_text avec
                       | None -> [ Newline ]
                       | Some t ->
                           (Raw (indent 5 "\n(*\n ") ::
                            self#soft_fix_linebreaks 8 (self#text_of_info (Some t))) @
                           [ Raw " *)" ; Newline ]
                       ) ) l ) )
           | Type_record l ->
               (Raw (" = "^(si priv alors "private " sinon "")^"{\n")) ::
               (List.flatten
                  (List.map
                     (fonc r ->
                       [ Raw ("  " ^ r.rf_name ^ " : ") ] @
                       (self#text_of_short_type_expr
                          (Name.father r.rf_name)
                          r.rf_type) @
                       [ Raw " ;" ] @
                       (filtre r.rf_text avec
                       | None -> [ Newline ]
                       | Some t ->
                           ((Raw (indent 5 "\n(*\n ")) ::
                           (self#soft_fix_linebreaks 8 (self#text_of_info (Some t)))) @
                           [ Raw " *)" ; Newline ] ) )
                     l ) )
               @  [ Raw " }" ]
          ) ) ;
          self#index `Type ty.ty_name ; Newline ] @
        (self#text_of_info ty.ty_info) dans
      self#texi_of_text t

    (** Return Texinfo code for an exception. *)
    méthode texi_of_exception e =
      Odoc_info.reset_type_names () ;
      soit t =
        [ self#fixedblock
            ( [ Newline ; minus ; Raw "exception " ;
                Raw (Name.simple e.ex_name) ;
                Raw (self#string_of_type_args e.ex_args None) ] @
              (filtre e.ex_alias avec
              | None -> []
              | Some ea -> [ Raw " = " ; Raw
                               ( filtre ea.ea_ex avec
                               | None -> ea.ea_name
                               | Some e -> e.ex_name ) ; ]
              ) ) ;
          self#index `Exception e.ex_name ; Newline ] @
        (self#text_of_info e.ex_info) dans
      self#texi_of_text t


    (** Return the Texinfo code for the given module. *)
    méthode texi_of_module m =
      soit is_alias = fonction
        | { m_kind = Module_alias _ } -> vrai
        | _ -> faux dans
      soit is_alias_there = fonction
        | { m_kind = Module_alias { ma_module = None } } -> faux
        | _ -> vrai dans
      soit resolve_alias_name = fonction
        | { m_kind = Module_alias { ma_name = name } } -> name
        | { m_name = name } -> name dans
      soit t =
        [ [ self#fixedblock
              [ Newline ; minus ; Raw "module " ;
                Raw (Name.simple m.m_name) ;
                Raw (si is_alias m
                alors " = " ^ (resolve_alias_name m)
                sinon "" ) ] ] ;
          ( si is_alias_there m
          alors [ Ref (resolve_alias_name m, Some RK_module, None) ;
                 Newline ; ]
          sinon [] ) ;
          ( si is_alias m
          alors [ self#index `Module m.m_name ; Newline ]
          sinon [ Newline ] ) ;
          self#text_of_info m.m_info ]
      dans
      self#texi_of_text (List.flatten t)

    (** Return the Texinfo code for the given module type. *)
    méthode texi_of_module_type mt =
      soit is_alias = fonction
        | { mt_kind = Some (Module_type_alias _) } -> vrai
        | _ -> faux dans
      soit is_alias_there = fonction
        | { mt_kind = Some (Module_type_alias { mta_module = None }) } -> faux
        | _ -> vrai dans
      soit resolve_alias_name = fonction
        | { mt_kind = Some (Module_type_alias { mta_name = name }) } -> name
        | { mt_name = name } -> name dans
      soit t =
        [ [ self#fixedblock
              [ Newline ; minus ; Raw "module type " ;
                Raw (Name.simple mt.mt_name) ;
                Raw (si is_alias mt
                alors " = " ^ (resolve_alias_name mt)
                sinon "" ) ] ] ;
          ( si is_alias_there mt
          alors [ Ref (resolve_alias_name mt, Some RK_module_type, None) ;
                 Newline ; ]
          sinon [] ) ;
          ( si is_alias mt
          alors [ self#index `Module_type mt.mt_name ; Newline ]
          sinon [ Newline ] ) ;
          self#text_of_info mt.mt_info ]
      dans
      self#texi_of_text (List.flatten t)

    (** Return the Texinfo code for the given included module. *)
    méthode texi_of_included_module im =
      soit t = [ self#fixedblock
                  ( Newline :: minus :: (Raw "include ") ::
                    ( filtre im.im_module avec
                    | None ->
                        [ Raw im.im_name ]
                    | Some (Mod { m_name = name }) ->
                        [ Raw name ; Raw "\n     " ;
                          Ref (name, Some RK_module, None) ]
                    | Some (Modtype { mt_name = name }) ->
                        [ Raw name ; Raw "\n     " ;
                          Ref (name, Some RK_module_type, None) ]
                    ) @
                   [ Newline ] @
                   (self#text_of_info im.im_info)
                  )
              ]
      dans
      self#texi_of_text t

    (** Return the Texinfo code for the given class. *)
    méthode texi_of_class c =
      Odoc_info.reset_type_names () ;
      soit t = [ self#fixedblock
                  [ Newline ; minus ; Raw "class " ;
                    Raw (Name.simple c.cl_name) ] ;
                Ref (c.cl_name, Some RK_class, None) ; Newline ;
                Newline ] @ (self#text_of_info c.cl_info) dans
      self#texi_of_text t

    (** Return the Texinfo code for the given class type. *)
    méthode texi_of_class_type ct =
      Odoc_info.reset_type_names () ;
      soit t = [ self#fixedblock
                  [ Newline ; minus ; Raw "class type " ;
                    Raw (Name.simple ct.clt_name) ] ;
                Ref (ct.clt_name, Some RK_class_type, None) ; Newline ;
                Newline ] @ (self#text_of_info ct.clt_info) dans
      self#texi_of_text t

    (** Return the Texinfo code for the given class element. *)
    méthode texi_of_class_element class_name class_ele =
      filtre class_ele avec
      | Class_attribute att -> self#texi_of_attribute att
      | Class_method met -> self#texi_of_method met
      | Class_comment t -> self#texi_of_text t

    (** Return the Texinfo code for the given module element. *)
    méthode texi_of_module_element module_name module_ele =
      (filtre module_ele avec
      | Element_module m -> self#texi_of_module m
      | Element_module_type mt -> self#texi_of_module_type mt
      | Element_included_module im -> self#texi_of_included_module im
      | Element_class c -> self#texi_of_class c
      | Element_class_type ct -> self#texi_of_class_type ct
      | Element_value v -> self#texi_of_value v
      | Element_exception e -> self#texi_of_exception e
      | Element_type t -> self#texi_of_type t
      | Element_module_comment t ->
          self#texi_of_text (Newline :: t @ [Newline])
      )

    (** {3 Generating methods }
       These methods write Texinfo code to an [out_channel] *)

    (** Generate the Texinfo code for the given list of inherited classes.*)
    méthode generate_inheritance_info chanout inher_l =
      soit f inh =
        filtre inh.ic_class avec
        | None -> (* we can't make the reference *)
            (Code inh.ic_name) ::
            (filtre inh.ic_text avec
            | None -> []
            | Some t -> Newline :: t)
        | Some cct -> (* we can create the reference *)
            soit kind =
              filtre cct avec
              | Cl _ -> Some RK_class
              | Cltype _ -> Some RK_class_type dans
            (Code inh.ic_name) ::
            (Ref (inh.ic_name, kind, None)) ::
            ( filtre inh.ic_text avec
            | None -> []
            | Some t -> Newline :: t)
      dans
      soit text = [
        Bold [ Raw Odoc_messages.inherits ] ;
        List (List.map f inher_l) ; Newline ]
      dans
      puts chanout (self#texi_of_text text)



    (** Generate the Texinfo code for the inherited classes
       of the given class. *)
    méthode generate_class_inheritance_info chanout cl =
      soit rec iter_kind = fonction
        | Class_structure ([], _) -> ()
        | Class_structure (l, _) ->
            self#generate_inheritance_info chanout l
        | Class_constraint (k, _) -> iter_kind k
        | Class_apply _
        | Class_constr _ -> ()
      dans
      iter_kind cl.cl_kind



    (** Generate the Texinfo code for the inherited classes
       of the given class type. *)
    méthode generate_class_type_inheritance_info chanout clt =
      filtre clt.clt_kind avec
      | Class_signature ([], _) ->
          ()
      | Class_signature (l, _) ->
          self#generate_inheritance_info chanout l
      | Class_type _ ->
          ()

    (** Generate the Texinfo code for the given class,
       in the given out channel. *)
    méthode generate_for_class chanout c =
     essaie
      Odoc_info.reset_type_names () ;
      soit depth = Name.depth c.cl_name dans
      soit title = [
        self#node depth c.cl_name ;
        Title (depth, None, [ Raw (Odoc_messages.clas ^ " ") ;
                                    Code c.cl_name ]) ;
        self#index `Class c.cl_name ] dans
      puts chanout (self#texi_of_text title) ;

      si is c.cl_info
      alors début
        soit descr = [ Title (succ depth, None,
                             [ Raw Odoc_messages.description ]) ] dans
        puts chanout (self#texi_of_text descr) ;
        puts chanout (self#texi_of_info c.cl_info)
      fin ;

      soit intf = [ Title (succ depth, None,
                          [ Raw Odoc_messages.interface]) ] dans
      puts chanout (self#texi_of_text intf);
      self#generate_class_inheritance_info chanout c ;
      List.iter
        (fonc ele -> puts chanout
            (self#texi_of_class_element c.cl_name ele))
        (Class.class_elements ~trans:faux c)
     avec Aliased_node -> ()


    (** Generate the Texinfo code for the given class type,
       in the given out channel. *)
    méthode generate_for_class_type chanout ct =
     essaie
      Odoc_info.reset_type_names () ;
      soit depth = Name.depth ct.clt_name dans
      soit title = [
        self#node depth ct.clt_name ;
        Title (depth, None, [ Raw (Odoc_messages.class_type ^ " ") ;
                                    Code ct.clt_name ]) ;
        self#index `Class_type ct.clt_name ] dans
      puts chanout (self#texi_of_text title) ;

      si is ct.clt_info
      alors début
        soit descr = [ Title (succ depth, None,
                             [ Raw Odoc_messages.description ]) ] dans
        puts chanout (self#texi_of_text descr) ;
        puts chanout (self#texi_of_info ct.clt_info)
      fin ;

      soit intf = [ Title (succ depth, None,
                          [ Raw Odoc_messages.interface ]) ] dans
      puts chanout (self#texi_of_text intf) ;
      self#generate_class_type_inheritance_info chanout ct;
      List.iter
        (fonc ele -> puts chanout
            (self#texi_of_class_element ct.clt_name ele))
        (Class.class_type_elements ~trans:faux ct)
     avec Aliased_node -> ()


    (** Generate the Texinfo code for the given module type,
       in the given out channel. *)
    méthode generate_for_module_type chanout mt =
     essaie
      soit depth = Name.depth mt.mt_name dans
      soit title = [
        self#node depth mt.mt_name ;
        Title (depth, None, [ Raw (Odoc_messages.module_type ^ " ") ;
                              Code mt.mt_name ]) ;
        self#index `Module_type mt.mt_name ; Newline ] dans
      puts chanout (self#texi_of_text title) ;

      si is mt.mt_info
      alors début
        soit descr = [ Title (succ depth, None,
                             [ Raw Odoc_messages.description ]) ] dans
        puts chanout (self#texi_of_text descr) ;
        puts chanout (self#texi_of_info mt.mt_info)
      fin ;

      soit mt_ele = Module.module_type_elements ~trans:vrai mt dans
      soit subparts = module_subparts mt_ele dans
      si depth < maxdepth && subparts <> []
      alors début
        soit menu = Texi.ifinfo
            ( self#heading (succ depth) [ Raw "Subparts" ]) dans
        puts chanout menu ;
        Texi.generate_menu chanout (subparts :> menu_data)
      fin ;

      soit intf = [ Title (succ depth, None,
                          [ Raw Odoc_messages.interface ]) ] dans
      puts chanout (self#texi_of_text intf) ;
      List.iter
        (fonc ele -> puts chanout
            (self#texi_of_module_element mt.mt_name ele))
        mt_ele ;

      (* create sub parts for modules, module types, classes and class types *)
      List.iter
        (fonction
          | `Module m -> self#generate_for_module chanout m
          | `Module_type mt -> self#generate_for_module_type chanout mt
          | `Class c -> self#generate_for_class chanout c
          | `Class_type ct -> self#generate_for_class_type chanout ct)
        subparts
     avec Aliased_node -> ()

    (** Generate the Texinfo code for the given module,
       in the given out channel. *)
    méthode generate_for_module chanout m =
     essaie
      Odoc_info.verbose ("Generate for module " ^ m.m_name) ;
      soit depth = Name.depth m.m_name dans
      soit title = [
        self#node depth m.m_name ;
        Title (depth, None,
               si m.m_text_only alors
                 [ Raw m.m_name ]
               sinon
                 [ Raw (Odoc_messages.modul ^ " ") ;
                   Code m.m_name ]
              ) ;
        self#index `Module m.m_name ; Newline ] dans
      puts chanout (self#texi_of_text title) ;

      si is m.m_info
      alors début
        soit descr = [ Title (succ depth, None,
                             [ Raw Odoc_messages.description ]) ] dans
        puts chanout (self#texi_of_text descr) ;
        puts chanout (self#texi_of_info m.m_info)
      fin ;

      soit m_ele = Module.module_elements ~trans:vrai m dans
      soit subparts = module_subparts m_ele dans
      si depth < maxdepth && subparts <> []
      alors début
        soit menu = Texi.ifinfo
            ( self#heading (succ depth) [ Raw "Subparts" ]) dans
        puts chanout menu ;
        Texi.generate_menu chanout (subparts :> menu_data)
      fin ;

      soit intf = [ Title (succ depth, None,
                          [ Raw Odoc_messages.interface]) ] dans
      puts chanout (self#texi_of_text intf) ;

      List.iter
        (fonc ele -> puts chanout
            (self#texi_of_module_element m.m_name ele))
        m_ele ;

      (* create sub nodes for modules, module types, classes and class types *)
      List.iter
        (fonction
          | `Module m -> self#generate_for_module chanout m
          | `Module_type mt -> self#generate_for_module_type chanout mt
          | `Class c -> self#generate_for_class chanout c
          | `Class_type ct -> self#generate_for_class_type chanout ct )
        subparts
     avec Aliased_node -> ()


    (** Writes the header of the TeXinfo document. *)
    méthode generate_texi_header chan texi_filename m_list =
      soit title = filtre !Global.title avec
      | None -> ""
      | Some s -> self#escape s dans
      soit filename =
        si texi_filename <> "ocamldoc.texi"
        alors
          soit fn = Filename.basename texi_filename dans
          (si Filename.check_suffix fn ".texi"
          alors Filename.chop_suffix fn ".texi"
          sinon fn) ^ ".info"
        sinon
          si title <> ""
          alors title ^ ".info"
          sinon "doc.info"
      dans
      (* write a standard Texinfo header *)
      List.iter
        (puts_nl chan)
        (List.flatten
           [ [ "\\input texinfo   @c -*-texinfo-*-" ;
               "@c %**start of header" ;
               "@setfilename " ^ filename ;
               "@settitle " ^ title ;
               "@c %**end of header" ; ] ;

             (si !Global.with_index alors
               List.map
                 (fonc ind ->
                   "@defcodeindex " ^ (indices ind))
                 indices_to_build
             sinon []) ;

             [ Texi.dirsection !info_section ] ;

             Texi.direntry
               (si !info_entry <> []
               alors !info_entry
               sinon [ Printf.sprintf "* %s: (%s)."
                        title
                        (Filename.chop_suffix filename ".info") ]) ;

             [ "@ifinfo" ;
               "This file was generated by Ocamldoc using the Texinfo generator." ;
               "@end ifinfo" ;

               "@c no titlepage." ;

               "@node Top, , , (dir)" ;
               "@top "^ title ; ]
           ] ) ;

      (* insert the intro file *)
      début
        filtre !Odoc_info.Global.intro_file avec
        | None quand title <> "" ->
            puts_nl chan "@ifinfo" ;
            puts_nl chan ("Documentation for " ^ title) ;
            puts_nl chan "@end ifinfo"
        | None ->
            puts_nl chan "@c no title given"
        | Some f ->
            nl chan ;
            puts_nl chan
              (self#texi_of_info
                 (Some (Odoc_info.info_of_comment_file m_list f)))
      fin ;

      (* write a top menu *)
      Texi.generate_menu chan
        ((List.map (fonc m -> `Module m) m_list) @
         (si !Global.with_index alors
           soit indices_names_to_build = List.map indices indices_to_build dans
           List.rev
             (List.fold_left
                (fonc acc ->
                  fonction (longname, shortname)
                      quand List.mem shortname indices_names_to_build ->
                        (`Index (longname ^ " index")) :: acc
                    | _ -> acc)
                [ `Comment "Indices :" ; `Blank ]
                indices_names )
         sinon [] ))


    (** Writes the trailer of the TeXinfo document. *)
    méthode generate_texi_trailer chan =
      nl chan ;
      si !Global.with_index
      alors
        soit indices_names_to_build = List.map indices indices_to_build dans
        List.iter (puts_nl chan)
          (List.flatten
             (List.map
                (fonc (longname, shortname) ->
                  si List.mem shortname indices_names_to_build
                  alors [ "@node " ^ longname ^ " index," ;
                         "@unnumbered " ^ longname ^ " index" ;
                         "@printindex " ^ shortname ; ]
                  sinon [])
                indices_names )) ;
      si !Global.with_toc
      alors puts_nl chan "@contents" ;
      puts_nl chan "@bye"


    méthode do_index it =
      si not (List.mem it indices_to_build)
      alors indices_to_build <- it :: indices_to_build

   (** Scan the whole module information to know which indices need to be build *)
    méthode scan_for_index : subparts -> unit = fonction
      | `Module m ->
          soit m_ele = Module.module_elements ~trans:vrai m dans
          List.iter self#scan_for_index_in_mod m_ele
      | `Module_type mt ->
          soit m_ele = Module.module_type_elements ~trans:vrai mt dans
          List.iter self#scan_for_index_in_mod m_ele
      | `Class c ->
          soit c_ele = Class.class_elements ~trans:vrai c dans
          List.iter self#scan_for_index_in_class c_ele
      | `Class_type ct ->
          soit c_ele = Class.class_type_elements ~trans:vrai ct dans
          List.iter self#scan_for_index_in_class c_ele

    méthode scan_for_index_in_mod = fonction
        (* no recursion *)
      | Element_value _ -> self#do_index `Value
      | Element_exception _ -> self#do_index `Exception
      | Element_type _ -> self#do_index `Type
      | Element_included_module _
      | Element_module_comment _ -> ()
         (* recursion *)
      | Element_module m -> self#do_index `Module ;
          self#scan_for_index (`Module m)
      | Element_module_type mt -> self#do_index `Module_type ;
          self#scan_for_index (`Module_type mt)
      | Element_class c -> self#do_index `Class ;
          self#scan_for_index (`Class c)
      | Element_class_type ct -> self#do_index `Class_type ;
          self#scan_for_index (`Class_type ct)

    méthode scan_for_index_in_class = fonction
      | Class_attribute _ -> self#do_index `Class_att
      | Class_method _ -> self#do_index `Method
      | Class_comment _ -> ()


    (** Generate the Texinfo file from a module list,
       in the {!Odoc_info.Global.out_file} file. *)
    méthode generate module_list =
      Hashtbl.clear node_tbl ;
      soit filename =
        si !Global.out_file = Odoc_messages.default_out_file
        alors "ocamldoc.texi"
        sinon !Global.out_file dans
      si !Global.with_index
      alors List.iter self#scan_for_index
          (List.map (fonc m -> `Module m) module_list) ;
      essaie
        soit chanout = open_out
            (Filename.concat !Global.target_dir filename) dans
        si !Global.with_header
        alors self#generate_texi_header chanout filename module_list ;
        List.iter
          (self#generate_for_module chanout)
          module_list ;
        si !Global.with_trailer
        alors self#generate_texi_trailer chanout ;
        close_out chanout
      avec
      | Failure s
      | Sys_error s ->
          prerr_endline s ;
          incr Odoc_info.errors
  fin
fin

module type Texi_generator = module type de Generator
