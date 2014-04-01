(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                  Fabrice Le Fessant, INRIA Saclay                   *)
(*                                                                     *)
(*  Copyright 2012 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

soit gen_annot = ref faux
soit gen_ml = ref faux
soit print_info_arg = ref faux
soit target_filename = ref None

soit arg_list = [
  "-o", Arg.String (fonc s ->
    target_filename := Some s
  ), " FILE (or -) : dump to file FILE (or stdout)";
  "-annot", Arg.Set gen_annot, " : generate the corresponding .annot file";
  "-src", Arg.Set gen_ml, " : generate an equivalent of the original source file (without comments) from a .cmt or a .cmti file";
  "-info", Arg.Set print_info_arg, " : print information on the file";
  ]

soit arg_usage = "read_cmt [OPTIONS] FILE.cmt : read FILE.cmt and print related information"

soit print_info cmt =
  soit ouvre Cmt_format dans
      Printf.printf "module name: %s\n" cmt.cmt_modname;
      début filtre cmt.cmt_annots avec
          Packed (_, list) -> Printf.printf "pack: %s\n" (String.concat " " list)
        | Implementation _ -> Printf.printf "kind: implementation\n"
        | Interface _ -> Printf.printf "kind: interface\n"
        | Partial_implementation _ -> Printf.printf "kind: implementation with errors\n"
        | Partial_interface _ -> Printf.printf "kind: interface with errors\n"
      fin;
      Printf.printf "command: %s\n" (String.concat " " (Array.to_list cmt.cmt_args));
      début filtre cmt.cmt_sourcefile avec
          None -> ()
        | Some name ->
          Printf.printf "sourcefile: %s\n" name;
      fin;
      Printf.printf "build directory: %s\n" cmt.cmt_builddir;
      List.iter (fonc dir -> Printf.printf "load path: %s\n%!" dir) cmt.cmt_loadpath;
      début
      filtre cmt.cmt_source_digest avec
          None -> ()
        | Some digest -> Printf.printf "source digest: %s\n" (Digest.to_hex digest);
      fin;
      début
      filtre cmt.cmt_interface_digest avec
          None -> ()
        | Some digest -> Printf.printf "interface digest: %s\n" (Digest.to_hex digest);
      fin;
      List.iter (fonc (name, digest) ->
        Printf.printf "import: %s %s\n" name (Digest.to_hex digest);
      ) (List.sort compare cmt.cmt_imports);
      Printf.printf "%!";
      ()

soit _ =
  Clflags.annotations := vrai;

  Arg.parse arg_list  (fonc filename ->
    si
      Filename.check_suffix filename ".cmt" ||
        Filename.check_suffix filename ".cmti"
    alors début
      (*      init_path(); *)
      soit cmt = Cmt_format.read_cmt filename dans
      si !gen_annot alors Cmt2annot.gen_annot !target_filename filename cmt;
      si !gen_ml alors Cmt2annot.gen_ml !target_filename filename cmt;
      si !print_info_arg || not (!gen_ml || !gen_annot) alors print_info cmt;
    fin sinon début
      Printf.fprintf stderr "Error: the file must have an extension in .cmt or .cmti.\n%!";
      Arg.usage arg_list arg_usage
    fin
  ) arg_usage
