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

(** Main module for bytecode.
@todo coucou le todo*)

ouvre Config
ouvre Clflags
ouvre Misc
ouvre Format
ouvre Typedtree

module M = Odoc_messages

soit print_DEBUG s = print_string s ; print_newline ()

(* we check if we must load a module given on the command line *)
soit arg_list = Array.to_list Sys.argv
soit (plugins, paths) =
  soit rec iter (files, incs) = fonction
      [] | _ :: [] -> (List.rev files, List.rev incs)
    | "-g" :: file :: q quand
        ((Filename.check_suffix file "cmo") ||
         (Filename.check_suffix file "cma") ||
           (Filename.check_suffix file "cmxs")) ->
      iter (file :: files, incs) q
  | "-i" :: dir :: q ->
      iter (files, dir :: incs) q
  | _ :: q ->
        iter (files, incs) q
  dans
  iter ([], []) arg_list

soit _ = print_DEBUG "Fin analyse des arguments pour le dynamic load"

(** Return the real name of the file to load,
   searching it in the paths if it is
   a simple name and not in the current directory. *)
soit get_real_filename name =
   si Filename.basename name <> name alors
     name
   sinon
     (
      soit paths = Filename.current_dir_name :: paths @ [Odoc_config.custom_generators_path] dans
      essaie
        soit d = List.find
            (fonc d -> Sys.file_exists (Filename.concat d name))
            paths
        dans
        Filename.concat d name
      avec
        Not_found ->
          failwith (M.file_not_found_in_paths paths name)
     )

soit load_plugin file =
  soit file = Dynlink.adapt_filename file dans
  Dynlink.allow_unsafe_modules vrai;
  essaie
    soit real_file = get_real_filename file dans
    ignore(Dynlink.loadfile real_file)
  avec
    Dynlink.Error e ->
      prerr_endline (Odoc_messages.load_file_error file (Dynlink.error_message e)) ;
      exit 1
  | Not_found ->
      prerr_endline (Odoc_messages.load_file_error file "Not_found");
      exit 1
  | Sys_error s
  | Failure s ->
      prerr_endline (Odoc_messages.load_file_error file s);
      exit 1
;;
List.iter load_plugin plugins;;

soit () = print_DEBUG "Fin du chargement dynamique eventuel"

soit () = Odoc_args.parse ()


soit loaded_modules =
  List.flatten
    (List.map
       (fonc f ->
         Odoc_info.verbose (Odoc_messages.loading f);
         essaie
           soit l = Odoc_analyse.load_modules f dans
           Odoc_info.verbose Odoc_messages.ok;
           l
         avec Failure s ->
           prerr_endline s ;
           incr Odoc_global.errors ;
           []
       )
       !Odoc_global.load
    )

soit modules = Odoc_analyse.analyse_files ~init: loaded_modules !Odoc_global.files

soit _ =
  filtre !Odoc_global.dump avec
    None -> ()
  | Some f ->
      essaie Odoc_analyse.dump_modules f modules
      avec Failure s ->
        prerr_endline s ;
        incr Odoc_global.errors


soit _ =
  filtre !Odoc_args.current_generator avec
    None ->
      ()
  | Some gen ->
      soit generator = Odoc_gen.get_minimal_generator gen dans
      Odoc_info.verbose Odoc_messages.generating_doc;
      generator#generate modules;
      Odoc_info.verbose Odoc_messages.ok

soit _ =
  si !Odoc_global.errors > 0 alors
  (
   prerr_endline (Odoc_messages.errors_occured !Odoc_global.errors) ;
   exit 1
  )
  sinon
    exit 0
