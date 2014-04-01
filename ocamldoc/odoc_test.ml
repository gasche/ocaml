(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2004 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Custom generator to perform test on ocamldoc. *)

ouvre Odoc_info
ouvre Odoc_info.Module
ouvre Odoc_info.Type

type test_kind =
    Types_display

soit p = Format.fprintf

module Generator (G : Odoc_gen.Base) =
struct
  classe string_gen =
  objet(self)
    hérite Odoc_info.Scan.scanner


    val modifiable test_kinds = []
    val modifiable fmt = Format.str_formatter

    méthode must_display_types = List.mem Types_display test_kinds

    méthode set_test_kinds_from_module m =
      test_kinds <- List.fold_left
          (fonc acc (s, _) ->
            filtre s avec
              "test_types_display" -> Types_display :: acc
            | _ -> acc
          )
          []
          (
           filtre m.m_info avec
             None -> []
           | Some i -> i.i_custom
          )
    méthode! scan_type t =
      filtre test_kinds avec
        [] -> ()
      | _ ->
          p fmt "# type %s:\n" t.ty_name;
          si self#must_display_types alors
            (
             p fmt "# manifest (Odoc_info.string_of_type_expr):\n<[%s]>\n"
               (filtre t.ty_manifest avec
                 None -> "None"
               | Some e -> Odoc_info.string_of_type_expr e
               );
            );


    méthode! scan_module_pre m =
      p fmt "#\n# module %s:\n" m.m_name ;
      si self#must_display_types alors
        (
         p fmt "# Odoc_info.string_of_module_type:\n<[%s]>\n"
           (Odoc_info.string_of_module_type m.m_type);
         p fmt "# Odoc_info.string_of_module_type ~complete: true :\n<[%s]>\n"
           (Odoc_info.string_of_module_type ~complete: vrai m.m_type);
        );
      vrai

    méthode! scan_module_type_pre m =
      p fmt "#\n# module type %s:\n" m.mt_name ;
      si self#must_display_types alors
        (
         p fmt "# Odoc_info.string_of_module_type:\n<[%s]>\n"
           (filtre m.mt_type avec
             None -> "None"
           | Some t -> Odoc_info.string_of_module_type t
           );
         p fmt "# Odoc_info.string_of_module_type ~complete: true :\n<[%s]>\n"
           (filtre m.mt_type avec
             None -> "None"
           | Some t -> Odoc_info.string_of_module_type ~complete: vrai t
           );
        );
      vrai

    méthode generate (module_list: Odoc_info.Module.t_module list) =
      soit oc = open_out !Odoc_info.Global.out_file dans
      fmt <- Format.formatter_of_out_channel oc;
      (
       essaie
         List.iter
           (fonc m ->
             self#set_test_kinds_from_module m;
             self#scan_module_list [m];
           )
           module_list
       avec
         e ->
           prerr_endline (Printexc.to_string e)
      );
      Format.pp_print_flush fmt ();
      close_out oc
  fin

  classe generator =
    soit g = nouv string_gen dans
    objet
      hérite G.generator tel base

      méthode generate l =
        base#generate l;
        g#generate l
    fin
fin;;

soit _ = Odoc_args.extend_base_generator (module Generator : Odoc_gen.Base_functor);;
