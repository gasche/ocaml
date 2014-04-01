(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2010 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** An OCamldoc generator to retrieve information in "todo" tags and
   generate an html page with all todo items. *)

ouvre Odoc_info
module Naming = Odoc_html.Naming
ouvre Odoc_info.Value
ouvre Odoc_info.Module
ouvre Odoc_info.Type
ouvre Odoc_info.Exception
ouvre Odoc_info.Class

soit p = Printf.bprintf

module Html =
  (val
   (
   filtre !Odoc_args.current_generator avec
     None -> (module Odoc_html.Generator : Odoc_html.Html_generator)
   | Some (Odoc_gen.Html m) -> m
   | _ ->
       failwith
         "Un générateur non-html est déjà choisi. Impossible d'installer le générateur html Todo-list"
  ) : Odoc_html.Html_generator)
;;

module Generator =
struct
  classe scanner html =
    objet (self)
      hérite Odoc_info.Scan.scanner

    val b = Buffer.create 256
    méthode buffer = b

    méthode privée gen_if_tag name target info_opt =
      filtre info_opt avec
        None -> ()
      | Some i ->
          soit l =
            List.fold_left
              (fonc acc (t, text) ->
                 filtre t avec
                   "todo" ->
                     début
                       filtre text avec
                         (Odoc_info.Code s) :: q ->
                           (
                            essaie
                              soit n = int_of_string s dans
                              soit head =
                                Odoc_info.Code (Printf.sprintf "[%d] " n)
                              dans
                              (Some n, head::q) :: acc
                            avec _ -> (None, text) :: acc
                           )
                       | _ -> (None, text) :: acc

                     fin
                 | _ -> acc
              )
              []
              i.i_custom
          dans
          filtre l avec
            [] -> ()
          | _ ->
              soit l = List.sort
                (fonc a b ->
                   filtre a, b avec
                     (None, _), _ -> -1
                   | _, (None, _) -> 1
                   | (Some n1, _), (Some n2, _) -> compare n1 n2
                )
                l
              dans
              p b "<pre><a href=\"%s\">%s</a></pre><div class=\"info\">"
                target name;
              soit col = fonction
                None -> "#000000"
              | Some 1 -> "#FF0000"
              | Some 2 -> "#AA5555"
              | Some 3 -> "#44BB00"
              | Some n -> Printf.sprintf "#%2x0000" (0xAA - (n * 0x10))
              dans
              List.iter
                (fonc (n, e) ->
                   Printf.bprintf b "<span style=\"color: %s\">" (col n);
                   html#html_of_text b e;
                   p b "</span><br/>\n";
                )
                l;
              p b "</div>"

    méthode scan_value v =
      self#gen_if_tag
        v.val_name
        (Odoc_html.Naming.complete_value_target v)
        v.val_info

    méthode scan_type t =
      self#gen_if_tag
        t.ty_name
        (Odoc_html.Naming.complete_type_target t)
        t.ty_info

    méthode scan_exception e =
      self#gen_if_tag
        e.ex_name
        (Odoc_html.Naming.complete_exception_target e)
        e.ex_info

    méthode scan_attribute a =
      self#gen_if_tag
        a.att_value.val_name
        (Odoc_html.Naming.complete_attribute_target a)
        a.att_value.val_info

    méthode scan_method m =
      self#gen_if_tag
        m.met_value.val_name
        (Odoc_html.Naming.complete_method_target m)
        m.met_value.val_info

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
        (Odoc_module.module_elements ~trans: faux m)

    méthode scan_included_module _ = ()

    méthode scan_class_pre c =
      self#gen_if_tag
        c.cl_name
        (fst (Odoc_html.Naming.html_files c.cl_name))
        c.cl_info;
      vrai

    méthode scan_class_type_pre ct =
      self#gen_if_tag
        ct.clt_name
        (fst (Odoc_html.Naming.html_files ct.clt_name))
        ct.clt_info;
      vrai

    méthode scan_module_pre m =
      self#gen_if_tag
        m.m_name
        (fst (Odoc_html.Naming.html_files m.m_name))
        m.m_info;
      vrai

    méthode scan_module_type_pre mt =
      self#gen_if_tag
        mt.mt_name
        (fst (Odoc_html.Naming.html_files mt.mt_name))
        mt.mt_info;
      vrai
  fin

  classe html : Html.html =
    objet (self)
      hérite Html.html tel html

      (** we have to hack a little because we cannot inherit from
             scanner, since public method cannot be hidden and
             our html class must respect the type of the default
             html generator class *)
      val modifiable scanner = nouv scanner (nouv Html.html )

      méthode generate modules =
      (* prevent having the 'todo' tag signaled as not handled *)
      tag_functions <-  ("todo", (fonc _ -> "")) :: tag_functions;
      (* generate doc as usual *)
      html#generate modules;
      (* then retrieve the todo tags and generate the todo.html page *)
      soit title =
        filtre !Odoc_info.Global.title avec
          None -> ""
        | Some s -> s
      dans
      soit b = Buffer.create 512 dans
      p b "<html>";
      self#print_header b title ;
      p b "<body><h1>%s</h1>" title;
      scanner#scan_module_list modules;
      Buffer.add_buffer b scanner#buffer;
      soit oc = open_out
          (Filename.concat !Odoc_info.Global.target_dir "todo.html")
      dans
      Buffer.output_buffer oc b;
      close_out oc

     initialisateur
       scanner <- nouv scanner self
  fin
fin

soit _ = Odoc_args.set_generator
 (Odoc_gen.Html (module Generator : Odoc_html.Html_generator))
 ;;
