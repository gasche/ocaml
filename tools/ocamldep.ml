(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Compenv
ouvre Parsetree

soit ppf = Format.err_formatter
(* Print the dependencies *)

type file_kind = ML | MLI;;

soit include_dirs = ref []
soit load_path = ref ([] : (string * string array) list)
soit ml_synonyms = ref [".ml"]
soit mli_synonyms = ref [".mli"]
soit native_only = ref faux
soit error_occurred = ref faux
soit raw_dependencies = ref faux
soit sort_files = ref faux
soit all_dependencies = ref faux
soit one_line = ref faux
soit files = ref []

(* Fix path to use '/' as directory separator instead of '\'.
   Only under Windows. *)

soit fix_slash s =
  si Sys.os_type = "Unix" alors s sinon début
    soit r = String.copy s dans
    pour i = 0 à String.length r - 1 faire
      si r.[i] = '\\' alors r.[i] <- '/'
    fait;
    r
  fin

(* Since we reinitialize load_path after reading OCAMLCOMP,
  we must use a cache instead of calling Sys.readdir too often. *)
module StringMap = Map.Make(String)
soit dirs = ref StringMap.empty
soit readdir dir =
  essaie
    StringMap.find dir !dirs
  avec Not_found ->
    soit contents =
      essaie
        Sys.readdir dir
      avec Sys_error msg ->
        Format.fprintf Format.err_formatter "@[Bad -I option: %s@]@." msg;
        error_occurred := vrai;
        [||]
    dans
    dirs := StringMap.add dir contents !dirs;
    contents

soit add_to_load_path dir =
  essaie
    soit dir = Misc.expand_directory Config.standard_library dir dans
    soit contents = readdir dir dans
    load_path := (dir, contents) :: !load_path
  avec Sys_error msg ->
    Format.fprintf Format.err_formatter "@[Bad -I option: %s@]@." msg;
    error_occurred := vrai

soit add_to_synonym_list synonyms suffix =
  si (String.length suffix) > 1 && suffix.[0] = '.' alors
    synonyms := suffix :: !synonyms
  sinon début
    Format.fprintf Format.err_formatter "@[Bad suffix: '%s'@]@." suffix;
    error_occurred := vrai
  fin

(* Find file 'name' (capitalized) in search path *)
soit find_file name =
  soit uname = String.uncapitalize name dans
  soit rec find_in_array a pos =
    si pos >= Array.length a alors None sinon début
      soit s = a.(pos) dans
      si s = name || s = uname alors Some s sinon find_in_array a (pos + 1)
    fin dans
  soit rec find_in_path = fonction
    [] -> raise Not_found
  | (dir, contents) :: rem ->
      filtre find_in_array contents 0 avec
        Some truename ->
          si dir = "." alors truename sinon Filename.concat dir truename
      | None -> find_in_path rem dans
  find_in_path !load_path

soit rec find_file_in_list = fonction
  [] -> raise Not_found
| x :: rem -> essaie find_file x avec Not_found -> find_file_in_list rem


soit find_dependency target_kind modname (byt_deps, opt_deps) =
  essaie
    soit candidates = List.map ((^) modname) !mli_synonyms dans
    soit filename = find_file_in_list candidates dans
    soit basename = Filename.chop_extension filename dans
    soit cmi_file = basename ^ ".cmi" dans
    soit ml_exists =
      List.exists (fonc ext -> Sys.file_exists (basename ^ ext)) !ml_synonyms dans
    soit new_opt_dep =
      si !all_dependencies alors
        filtre target_kind avec
        | MLI -> [ cmi_file ]
        | ML  ->
          cmi_file :: (si ml_exists alors [ basename ^ ".cmx"] sinon [])
      sinon
        (* this is a make-specific hack that makes .cmx to be a 'proxy'
           target that would force the dependency on .cmi via transitivity *)
        si ml_exists
        alors [ basename ^ ".cmx" ]
        sinon [ cmi_file ]
    dans
    ( cmi_file :: byt_deps, new_opt_dep @ opt_deps)
  avec Not_found ->
  essaie
    (* "just .ml" case *)
    soit candidates = List.map ((^) modname) !ml_synonyms dans
    soit filename = find_file_in_list candidates dans
    soit basename = Filename.chop_extension filename dans
    soit bytenames =
      si !all_dependencies alors
        filtre target_kind avec
        | MLI -> [basename ^ ".cmi"]
        | ML  -> [basename ^ ".cmi";]
      sinon
        (* again, make-specific hack *)
        [basename ^ (si !native_only alors ".cmx" sinon ".cmo")] dans
    soit optnames =
      si !all_dependencies
      alors filtre target_kind avec
        | MLI -> [basename ^ ".cmi"]
        | ML  -> [basename ^ ".cmi"; basename ^ ".cmx"]
      sinon [ basename ^ ".cmx" ]
    dans
    (bytenames @ byt_deps, optnames @  opt_deps)
  avec Not_found ->
    (byt_deps, opt_deps)

soit (depends_on, escaped_eol) = (":", " \\\n    ")

soit print_filename s =
  soit s = si !Clflags.force_slash alors fix_slash s sinon s dans
  si not (String.contains s ' ') alors début
    print_string s;
  fin sinon début
    soit rec count n i =
      si i >= String.length s alors n
      sinon si s.[i] = ' ' alors count (n+1) (i+1)
      sinon count n (i+1)
    dans
    soit spaces = count 0 0 dans
    soit result = String.create (String.length s + spaces) dans
    soit rec loop i j =
      si i >= String.length s alors ()
      sinon si s.[i] = ' ' alors début
        result.[j] <- '\\';
        result.[j+1] <- ' ';
        loop (i+1) (j+2);
      fin sinon début
        result.[j] <- s.[i];
        loop (i+1) (j+1);
      fin
    dans
    loop 0 0;
    print_string result;
  fin
;;

soit print_dependencies target_files deps =
  soit rec print_items pos = fonction
    [] -> print_string "\n"
  | dep :: rem ->
    si !one_line || (pos + 1 + String.length dep <= 77) alors début
        si pos <> 0 alors print_string " "; print_filename dep;
        print_items (pos + String.length dep + 1) rem
      fin sinon début
        print_string escaped_eol; print_filename dep;
        print_items (String.length dep + 4) rem
      fin dans
  print_items 0 (target_files @ [depends_on] @ deps)

soit print_raw_dependencies source_file deps =
  print_filename source_file; print_string depends_on;
  Depend.StringSet.iter
    (fonc dep ->
      si (String.length dep > 0)
          && (filtre dep.[0] avec 'A'..'Z' -> vrai | _ -> faux) alors début
            print_char ' ';
            print_string dep
          fin)
    deps;
  print_char '\n'


(* Process one file *)

soit report_err source_file exn =
  error_occurred := vrai;
  filtre exn avec
    | Sys_error msg ->
        Format.fprintf Format.err_formatter "@[I/O error:@ %s@]@." msg
    | x ->
        filtre Location.error_of_exn x avec
        | Some err ->
            Format.fprintf Format.err_formatter "@[%a@]@."
              Location.report_error err
        | None -> raise x

soit read_parse_and_extract parse_function extract_function magic source_file =
  Depend.free_structure_names := Depend.StringSet.empty;
  essaie
    soit input_file = Pparse.preprocess source_file dans
    début essaie
      soit ast =
        Pparse.file Format.err_formatter input_file parse_function magic dans
      extract_function Depend.StringSet.empty ast;
      Pparse.remove_preprocessed input_file;
      !Depend.free_structure_names
    avec x ->
      Pparse.remove_preprocessed input_file;
      raise x
    fin
  avec x ->
    report_err source_file x;
    Depend.StringSet.empty

soit ml_file_dependencies source_file =
  soit parse_use_file_as_impl lexbuf =
    soit f x =
      filtre x avec
      | Ptop_def s -> s
      | Ptop_dir _ -> []
    dans
    List.flatten (List.map f (Parse.use_file lexbuf))
  dans
  soit extracted_deps =
    read_parse_and_extract parse_use_file_as_impl Depend.add_implementation
                           Config.ast_impl_magic_number source_file
  dans
  si !sort_files alors
    files := (source_file, ML, !Depend.free_structure_names) :: !files
  sinon
    si !raw_dependencies alors début
      print_raw_dependencies source_file extracted_deps
    fin sinon début
      soit basename = Filename.chop_extension source_file dans
      soit byte_targets = [ basename ^ ".cmo" ] dans
      soit native_targets =
        si !all_dependencies
        alors [ basename ^ ".cmx"; basename ^ ".o" ]
        sinon [ basename ^ ".cmx" ] dans
      soit init_deps = si !all_dependencies alors [source_file] sinon [] dans
      soit cmi_name = basename ^ ".cmi" dans
      soit init_deps, extra_targets =
        si List.exists (fonc ext -> Sys.file_exists (basename ^ ext))
                       !mli_synonyms
        alors (cmi_name :: init_deps, cmi_name :: init_deps), []
        sinon (init_deps, init_deps),
             (si !all_dependencies alors [cmi_name] sinon [])
      dans
      soit (byt_deps, native_deps) =
        Depend.StringSet.fold (find_dependency ML)
          extracted_deps init_deps dans
      print_dependencies (byte_targets @ extra_targets) byt_deps;
      print_dependencies (native_targets @ extra_targets) native_deps;
    fin

soit mli_file_dependencies source_file =
  soit extracted_deps =
    read_parse_and_extract Parse.interface Depend.add_signature
                           Config.ast_intf_magic_number source_file
  dans
  si !sort_files alors
    files := (source_file, MLI, extracted_deps) :: !files
  sinon
    si !raw_dependencies alors début
      print_raw_dependencies source_file extracted_deps
    fin sinon début
      soit basename = Filename.chop_extension source_file dans
      soit (byt_deps, opt_deps) =
        Depend.StringSet.fold (find_dependency MLI)
          extracted_deps ([], []) dans
      print_dependencies [basename ^ ".cmi"] byt_deps
    fin

soit file_dependencies_as kind source_file =
  Compenv.readenv ppf Before_compile;
  load_path := [];
  List.iter add_to_load_path (
      (!Compenv.last_include_dirs @
       !include_dirs @
       !Compenv.first_include_dirs
      ));
  Location.input_name := source_file;
  essaie
    si Sys.file_exists source_file alors début
      filtre kind avec
      | ML -> ml_file_dependencies source_file
      | MLI -> mli_file_dependencies source_file
    fin
  avec x -> report_err source_file x

soit file_dependencies source_file =
  si List.exists (Filename.check_suffix source_file) !ml_synonyms alors
    file_dependencies_as ML source_file
  sinon si List.exists (Filename.check_suffix source_file) !mli_synonyms alors
    file_dependencies_as MLI source_file
  sinon ()

soit sort_files_by_dependencies files =
  soit h = Hashtbl.create 31 dans
  soit worklist = ref [] dans

(* Init Hashtbl with all defined modules *)
  soit files = List.map (fonc (file, file_kind, deps) ->
    soit modname = Filename.chop_extension (Filename.basename file) dans
    modname.[0] <- Char.uppercase modname.[0];
    soit key = (modname, file_kind) dans
    soit new_deps = ref [] dans
    Hashtbl.add h key (file, new_deps);
    worklist := key :: !worklist;
    (modname, file_kind, deps, new_deps)
  ) files dans

(* Keep only dependencies to defined modules *)
  List.iter (fonc (modname, file_kind, deps, new_deps) ->
    soit add_dep modname kind =
      new_deps := (modname, kind) :: !new_deps;
    dans
    Depend.StringSet.iter (fonc modname ->
      filtre file_kind avec
          ML -> (* ML depends both on ML and MLI *)
            si Hashtbl.mem h (modname, MLI) alors add_dep modname MLI;
            si Hashtbl.mem h (modname, ML) alors add_dep modname ML
        | MLI -> (* MLI depends on MLI if exists, or ML otherwise *)
          si Hashtbl.mem h (modname, MLI) alors add_dep modname MLI
          sinon si Hashtbl.mem h (modname, ML) alors add_dep modname ML
    ) deps;
    si file_kind = ML alors (* add dep from .ml to .mli *)
      si Hashtbl.mem h (modname, MLI) alors add_dep modname MLI
  ) files;

(* Print and remove all files with no remaining dependency. Iterate
   until all files have been removed (worklist is empty) or
   no file was removed during a turn (cycle). *)
  soit printed = ref vrai dans
  pendant_que !printed && !worklist <> [] faire
    soit files = !worklist dans
    worklist := [];
    printed := faux;
    List.iter (fonc key ->
      soit (file, deps) = Hashtbl.find h key dans
      soit set = !deps dans
      deps := [];
      List.iter (fonc key ->
        si Hashtbl.mem h key alors deps := key :: !deps
      ) set;
      si !deps = [] alors début
        printed := vrai;
        Printf.printf "%s " file;
        Hashtbl.remove h key;
      fin sinon
        worklist := key :: !worklist
    ) files
  fait;

  si !worklist <> [] alors début
    Format.fprintf Format.err_formatter
      "@[Warning: cycle in dependencies. End of list is not sorted.@]@.";
    Hashtbl.iter (fonc _ (file, deps) ->
      Format.fprintf Format.err_formatter "\t@[%s: " file;
      List.iter (fonc (modname, kind) ->
        Format.fprintf Format.err_formatter "%s.%s " modname
          (si kind=ML alors "ml" sinon "mli");
      ) !deps;
      Format.fprintf Format.err_formatter "@]@.";
      Printf.printf "%s " file) h;
  fin;
  Printf.printf "\n%!";
  ()


(* Entry point *)

soit usage = "Usage: ocamldep [options] <source files>\nOptions are:"

soit print_version () =
  Format.printf "ocamldep, version %s@." Sys.ocaml_version;
  exit 0;
;;

soit print_version_num () =
  Format.printf "%s@." Sys.ocaml_version;
  exit 0;
;;

soit _ =
  Clflags.classic := faux;
  first_include_dirs := Filename.current_dir_name :: !first_include_dirs;
  Compenv.readenv ppf Before_args;
  Arg.parse [
     "-absname", Arg.Set Location.absname,
        " Show absolute filenames in error messages";
     "-all", Arg.Set all_dependencies,
        " Generate dependencies on all files";
     "-I", Arg.String (fonc s -> include_dirs := s :: !include_dirs),
        "<dir>  Add <dir> to the list of include directories";
     "-impl", Arg.String (file_dependencies_as ML),
        "<f>  Process <f> as a .ml file";
     "-intf", Arg.String (file_dependencies_as MLI),
        "<f>  Process <f> as a .mli file";
     "-ml-synonym", Arg.String(add_to_synonym_list ml_synonyms),
        "<e>  Consider <e> as a synonym of the .ml extension";
     "-mli-synonym", Arg.String(add_to_synonym_list mli_synonyms),
        "<e>  Consider <e> as a synonym of the .mli extension";
     "-modules", Arg.Set raw_dependencies,
        " Print module dependencies in raw form (not suitable for make)";
     "-native", Arg.Set native_only,
        " Generate dependencies for native-code only (no .cmo files)";
     "-one-line", Arg.Set one_line,
        " Output one line per file, regardless of the length";
     "-pp", Arg.String(fonc s -> Clflags.preprocessor := Some s),
         "<cmd>  Pipe sources through preprocessor <cmd>";
     "-ppx", Arg.String(fonc s -> first_ppx := s :: !first_ppx),
         "<cmd>  Pipe abstract syntax trees through preprocessor <cmd>";
     "-slash", Arg.Set Clflags.force_slash,
         " (Windows) Use forward slash / instead of backslash \\ in file paths";
     "-sort", Arg.Set sort_files,
        " Sort files according to their dependencies";
     "-version", Arg.Unit print_version,
         " Print version and exit";
     "-vnum", Arg.Unit print_version_num,
         " Print version number and exit";
    ] file_dependencies usage;
  Compenv.readenv ppf Before_link;
  si !sort_files alors sort_files_by_dependencies !files;
  exit (si !error_occurred alors 2 sinon 0)
