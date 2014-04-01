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

(** Definition of a class which outputs a dot file showing
   top modules dependencies.*)

ouvre Odoc_info

module F = Format

soit dot_include_all = ref faux

soit dot_types = ref faux

soit dot_reduce = ref faux

soit dot_colors  = ref (List.flatten Odoc_messages.default_dot_colors)

module Generator =
struct

(** This class generates a dot file showing the top modules dependencies. *)
classe dot =
  objet (self)

    (** To store the colors associated to locations of modules. *)
    val modifiable loc_colors = []

    (** the list of modules we know. *)
    val modifiable modules = []

    (** Colors to use when finding new locations of modules. *)
    val modifiable colors = !dot_colors

    (** Graph header. *)
    méthode header =
      "digraph G {\n"^
      "  size=\"10,7.5\";\n"^
      "  ratio=\"fill\";\n"^
      "  rotate=90;\n"^
      "  fontsize=\"12pt\";\n"^
      "  rankdir = TB ;\n"

    méthode get_one_color =
      filtre colors avec
        [] -> None
      | h :: q ->
          colors <- q ;
          Some h

    méthode node_color s =
      essaie Some (List.assoc s loc_colors)
      avec
        Not_found ->
          filtre self#get_one_color avec
            None -> None
          | Some c ->
              loc_colors <- (s, c) :: loc_colors ;
              Some c

    méthode print_module_atts fmt m =
      filtre self#node_color (Filename.dirname m.Module.m_file) avec
        None -> ()
      | Some col -> F.fprintf fmt "\"%s\" [style=filled, color=%s];\n" m.Module.m_name col

    méthode print_type_atts fmt t =
      filtre self#node_color (Name.father t.Type.ty_name) avec
        None -> ()
      | Some col -> F.fprintf fmt "\"%s\" [style=filled, color=%s];\n" t.Type.ty_name col

    méthode print_one_dep fmt src dest =
      F.fprintf fmt "\"%s\" -> \"%s\";\n" src dest

    méthode generate_for_module fmt m =
      soit l = List.filter
          (fonc n ->
            !dot_include_all ||
            (List.exists (fonc m -> m.Module.m_name = n) modules))
          m.Module.m_top_deps
      dans
      self#print_module_atts fmt m;
      List.iter (self#print_one_dep fmt m.Module.m_name) l

    méthode generate_for_type fmt (t, l) =
      self#print_type_atts fmt t;
      List.iter
        (self#print_one_dep fmt t.Type.ty_name)
        l

    méthode generate_types types =
      essaie
        soit oc = open_out !Global.out_file dans
        soit fmt = F.formatter_of_out_channel oc dans
        F.fprintf fmt "%s" self#header;
        soit graph = Odoc_info.Dep.deps_of_types
            ~kernel: !dot_reduce
            types
        dans
        List.iter (self#generate_for_type fmt) graph;
        F.fprintf fmt "}\n" ;
        F.pp_print_flush fmt ();
        close_out oc
      avec
        Sys_error s ->
          raise (Failure s)

    méthode generate_modules modules_list =
      essaie
        modules <- modules_list ;
        soit oc = open_out !Global.out_file dans
        soit fmt = F.formatter_of_out_channel oc dans
        F.fprintf fmt "%s" self#header;

        si !dot_reduce alors
          Odoc_info.Dep.kernel_deps_of_modules modules_list;

        List.iter (self#generate_for_module fmt) modules_list;
        F.fprintf fmt "}\n" ;
        F.pp_print_flush fmt ();
        close_out oc
      avec
        Sys_error s ->
          raise (Failure s)

    (** Generate the dot code in the file {!Odoc_info.Args.out_file}. *)
    méthode generate (modules_list : Odoc_info.Module.t_module list) =
      colors <- !dot_colors;
      si !dot_types alors
        self#generate_types (Odoc_info.Search.types modules_list)
      sinon
        self#generate_modules modules_list
  fin
fin

module type Dot_generator = module type de Generator
