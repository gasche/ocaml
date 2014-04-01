(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*      Fabrice Le Fessant, EPI Gallium, INRIA Paris-Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Clflags

soit output_prefix name =
  soit oname =
    filtre !output_name avec
    | None -> name
    | Some n -> si !compile_only alors (output_name := None; n) sinon name dans
  Misc.chop_extension_if_any oname

soit print_version_and_library compiler =
  Printf.printf "The Chamelle %s, version " compiler;
  print_string Config.version; print_newline();
  print_string "Dossier de la bibliothèque standard : ";
  print_string Config.standard_library; print_newline();
  exit 0

soit print_version_string () =
  print_string Config.version; print_newline(); exit 0

soit print_standard_library () =
  print_string Config.standard_library; print_newline(); exit 0

soit fatal err =
  prerr_endline err;
  exit 2

soit extract_output = fonction
  | Some s -> s
  | None ->
      fatal "Veuillez spécifier le nom du fichier de sortie, en utilisant l'option -o"

soit default_output = fonction
  | Some s -> s
  | None -> Config.default_executable_name

soit implicit_modules = ref []
soit first_include_dirs = ref []
soit last_include_dirs = ref []
soit first_ccopts = ref []
soit last_ccopts = ref []
soit first_ppx = ref []
soit last_ppx = ref []
soit first_objfiles = ref []
soit last_objfiles = ref []

(* Note: this function is duplicated in optcompile.ml *)
soit check_unit_name ppf filename name =
  essaie
    début filtre name.[0] avec
    | 'A'..'Z' -> ()
    | _ ->
       Location.print_warning (Location.in_file filename) ppf
        (Warnings.Bad_module_name name);
       raise Exit;
    fin;
    pour i = 1 à String.length name - 1 faire
      filtre name.[i] avec
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' -> ()
      | _ ->
         Location.print_warning (Location.in_file filename) ppf
           (Warnings.Bad_module_name name);
         raise Exit;
    fait;
  avec Exit -> ()
;;







type readenv_position =
  Before_args | Before_compile | Before_link

(* Syntax of OCAMLPARAM: (name=VALUE,)* _ (,name=VALUE)*
   where VALUE should not contain ',' *)
exception SyntaxError de string

soit parse_args s =
  soit args = Misc.split s ',' dans
  soit rec iter is_after args before after =
    filtre args avec
      [] ->
      si not is_after alors
        raise (SyntaxError "no '_' separator found")
      sinon
      (List.rev before, List.rev after)
    | "_" :: _ quand is_after -> raise (SyntaxError "too many '_' separators")
    | "_" :: tail -> iter vrai tail before after
    | arg :: tail ->
      soit binding = essaie
        Misc.cut_at arg '='
      avec Not_found ->
        raise (SyntaxError ("missing '=' in " ^ arg))
      dans
      si is_after alors
        iter is_after tail before (binding :: after)
      sinon
        iter is_after tail (binding :: before) after
  dans
  iter faux args [] []

soit setter ppf f name options s =
  essaie
    soit bool = filtre s avec
      | "0" -> faux
      | "1" -> vrai
      | _ -> raise Not_found
    dans
    List.iter (fonc b -> b := f bool) options
  avec Not_found ->
    Location.print_warning Location.none ppf
      (Warnings.Bad_env_variable ("OCAMLPARAM",
                                  Printf.sprintf "bad value for %s" name))

soit read_OCAMLPARAM ppf position =
  essaie
    soit s = Sys.getenv "OCAMLPARAM" dans
    soit (before, after) =
      essaie
        parse_args s
      avec SyntaxError s ->
         Location.print_warning Location.none ppf
           (Warnings.Bad_env_variable ("OCAMLPARAM", s));
         [],[]
    dans

    soit set name options s =  setter ppf (fonc b -> b) name options s dans
    soit clear name options s = setter ppf (fonc b -> not b) name options s dans
    List.iter (fonc (name, v) ->
      filtre name avec
      | "g" -> set "g" [ Clflags.debug ] v
      | "p" -> set "p" [ Clflags.gprofile ] v
      | "bin-annot" -> set "bin-annot" [ Clflags.binary_annotations ] v
      | "annot" -> set "annot" [ Clflags.annotations ] v
      | "absname" -> set "absname" [ Location.absname ] v
      | "compat-32" -> set "compat-32" [ bytecode_compatible_32 ] v
      | "noassert" -> set "noassert" [ noassert ] v
      | "noautolink" -> set "noautolink" [ no_auto_link ] v
      | "nostdlib" -> set "nostdlib" [ no_std_include ] v
      | "linkall" -> set "linkall" [ link_everything ] v
      | "nolabels" -> set "nolabels" [ classic ] v
      | "principal" -> set "principal"  [ principal ] v
      | "rectypes" -> set "rectypes" [ recursive_types ] v
      | "strict-sequence" -> set "strict-sequence" [ strict_sequence ] v
      | "thread" -> set "thread" [ use_threads ] v
      | "unsafe" -> set "unsafe" [ fast ] v
      | "verbose" -> set "verbose" [ verbose ] v
      | "nopervasives" -> set "nopervasives" [ nopervasives ] v
      | "slash" -> set "slash" [ force_slash ] v (* for ocamldep *)
      | "keep-locs" -> set "keep-locs" [ Clflags.keep_locs ] v

      | "compact" -> clear "compact" [ optimize_for_speed ] v
      | "no-app-funct" -> clear "no-app-funct" [ applicative_functors ] v
      | "nodynlink" -> clear "nodynlink" [ dlcode ] v
      | "short-paths" -> clear "short-paths" [ real_paths ] v
      | "trans-mod" -> set "trans-mod" [ transparent_modules ] v

      | "pp" -> preprocessor := Some v
      | "runtime-variant" -> runtime_variant := v
      | "cc" -> c_compiler := Some v

      (* assembly sources *)
      |  "s" ->
        set "s" [ Clflags.keep_asm_file ; Clflags.keep_startup_file ] v
      |  "S" -> set "S" [ Clflags.keep_asm_file ] v
      |  "dstartup" -> set "dstartup" [ Clflags.keep_startup_file ] v

      (* warn-errors *)
      | "we" | "warn-error" -> Warnings.parse_options vrai v
      (* warnings *)
      |  "w"  ->               Warnings.parse_options faux v
      (* warn-errors *)
      | "wwe" ->               Warnings.parse_options faux v

      (* inlining *)
      | "inline" -> début essaie
          inline_threshold := 8 * int_of_string v
        avec _ ->
          Location.print_warning Location.none ppf
            (Warnings.Bad_env_variable ("OCAMLPARAM",
                                        "non-integer parameter for \"inline\""))
        fin

      | "intf-suffix" -> Config.interface_suffix := v

      | "I" -> début
          filtre position avec
          | Before_args -> first_include_dirs := v :: !first_include_dirs
          | Before_link | Before_compile ->
            last_include_dirs := v :: !last_include_dirs
        fin

      | "cclib" ->
        début
          filtre position avec
          | Before_compile -> ()
          | Before_link | Before_args ->
            ccobjs := Misc.rev_split_words v @ !ccobjs
        fin

      | "ccopts" ->
        début
          filtre position avec
          | Before_link | Before_compile ->
            last_ccopts := v :: !last_ccopts
          | Before_args ->
            first_ccopts := v :: !first_ccopts
        fin

      | "ppx" ->
        début
          filtre position avec
          | Before_link | Before_compile ->
            last_ppx := v :: !last_ppx
          | Before_args ->
            first_ppx := v :: !first_ppx
        fin


      | "cmo" | "cma" ->
        si not !native_code alors
        début
          filtre position avec
          | Before_link | Before_compile ->
            last_objfiles := v ::! last_objfiles
          | Before_args ->
            first_objfiles := v :: !first_objfiles
        fin

      | "cmx" | "cmxa" ->
        si !native_code alors
        début
          filtre position avec
          | Before_link | Before_compile ->
            last_objfiles := v ::! last_objfiles
          | Before_args ->
            first_objfiles := v :: !first_objfiles
        fin

      | _ ->
        Printf.eprintf
            "Warning: discarding value of variable %S in OCAMLPARAM\n%!"
            name
    ) (filtre position avec
        Before_args -> before
      | Before_compile | Before_link -> after)
  avec Not_found -> ()

soit readenv ppf position =
  last_include_dirs := [];
  last_ccopts := [];
  last_ppx := [];
  last_objfiles := [];
  read_OCAMLPARAM ppf position;
  all_ccopts := !last_ccopts @ !first_ccopts;
  all_ppx := !last_ppx @ !first_ppx

soit get_objfiles () =
  List.rev (!last_objfiles @ !objfiles @ !first_objfiles)
