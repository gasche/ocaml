(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Nicolas Pouillard *)
ouvre My_std
ouvre Pathname.Operators
ouvre Tags.Operators
ouvre Tools
ouvre Command
ouvre Ocaml_utils

soit add_suffix s = List.map (fonc x -> x -.- s) ;;

soit ocamldep_command' tags =
  soit tags' = tags++"ocaml"++"ocamldep" dans
    S [!Options.ocamldep; T tags'; ocaml_ppflags (tags++"pp:dep"); A "-modules"]

soit menhir_ocamldep_command' tags ~menhir_spec out =
  soit menhir = si !Options.ocamlyacc = N alors V"MENHIR" sinon !Options.ocamlyacc dans
  Cmd(S[menhir; T tags; A"--raw-depend";
        A"--ocamldep"; Quote (ocamldep_command' Tags.empty);
        menhir_spec ; Sh ">"; Px out])

soit menhir_ocamldep_command arg out env _build =
  soit arg = env arg et out = env out dans
  soit tags = tags_of_pathname arg++"ocaml"++"menhir_ocamldep" dans
  menhir_ocamldep_command' tags ~menhir_spec:(P arg) out

soit import_mlypack build mlypack =
  soit tags1 = tags_of_pathname mlypack dans
  soit files = string_list_of_file mlypack dans
  soit include_dirs = Pathname.include_dirs_of (Pathname.dirname mlypack) dans
  soit files_alternatives =
    List.map début fonc module_name ->
      expand_module include_dirs module_name ["mly"]
    fin files
  dans
  soit files = List.map Outcome.good (build files_alternatives) dans
  soit tags2 =
    List.fold_right
      (fonc file -> Tags.union (tags_of_pathname file))
      files tags1
  dans
  (tags2, files)

soit menhir_modular_ocamldep_command mlypack out env build =
  soit mlypack = env mlypack et out = env out dans
  soit (tags,files) = import_mlypack build mlypack dans
  soit tags = tags++"ocaml"++"menhir_ocamldep" dans
  soit menhir_base = Pathname.remove_extensions mlypack dans
  soit menhir_spec = S[A "--base" ; P menhir_base ; atomize_paths files] dans
  menhir_ocamldep_command' tags ~menhir_spec out

soit menhir_modular menhir_base mlypack mlypack_depends env build =
  soit menhir = si !Options.ocamlyacc = N alors V"MENHIR" sinon !Options.ocamlyacc dans
  soit menhir_base = env menhir_base dans
  soit mlypack = env mlypack dans
  soit mlypack_depends = env mlypack_depends dans
  soit (tags,files) = import_mlypack build mlypack dans
  soit () = List.iter Outcome.ignore_good (build [[mlypack_depends]]) dans
  Ocaml_compiler.prepare_compile build mlypack;
  soit ocamlc_tags = tags++"ocaml"++"byte"++"compile" dans
  soit tags = tags++"ocaml"++"parser"++"menhir" dans
  Cmd(S[menhir ;
        A "--ocamlc"; Quote(S[!Options.ocamlc; T ocamlc_tags; ocaml_include_flags mlypack]);
        T tags ; A "--infer" ; A "--base" ; Px menhir_base ; atomize_paths files])

soit ocamldep_command arg out env _build =
  soit arg = env arg et out = env out dans
  soit tags = tags_of_pathname arg dans
  Cmd(S[ocamldep_command' tags; P arg; Sh ">"; Px out])

soit ocamlyacc mly env _build =
  soit mly = env mly dans
  soit ocamlyacc = si !Options.ocamlyacc = N alors V"OCAMLYACC" sinon !Options.ocamlyacc dans
  Cmd(S[ocamlyacc; T(tags_of_pathname mly++"ocaml"++"parser"++"ocamlyacc"); Px mly])

soit ocamllex mll env _build =
  soit mll = env mll dans
  Cmd(S[!Options.ocamllex; T(tags_of_pathname mll++"ocaml"++"lexer"++"ocamllex"); Px mll])

soit infer_interface ml mli env build =
  soit ml = env ml et mli = env mli dans
  soit tags = tags_of_pathname ml++"ocaml" dans
  Ocaml_compiler.prepare_compile build ml;
  Cmd(S[!Options.ocamlc; ocaml_ppflags tags; ocaml_include_flags ml; A"-i";
        (si Tags.mem "thread" tags alors A"-thread" sinon N);
        T(tags++"infer_interface"); P ml; Sh">"; Px mli])

soit menhir mly env build =
  soit mly = env mly dans
  soit menhir = si !Options.ocamlyacc = N alors V"MENHIR" sinon !Options.ocamlyacc dans
  soit tags = tags_of_pathname mly dans
  soit ocamlc_tags = tags++"ocaml"++"byte"++"compile" dans
  soit menhir_tags = tags++"ocaml"++"parser"++"menhir" dans
  Ocaml_compiler.prepare_compile build mly;
  Cmd(S[menhir;
        A"--ocamlc"; Quote(S[!Options.ocamlc; T ocamlc_tags; ocaml_include_flags mly]);
        T menhir_tags; A"--infer"; Px mly])

soit ocamldoc_c tags arg odoc =
  soit tags = tags++"ocaml" dans
  Cmd (S [!Options.ocamldoc; A"-dump"; Px odoc; T(tags++"doc");
          ocaml_ppflags (tags++"pp:doc");
          ocaml_include_flags arg; P arg])

soit ocamldoc_l_dir tags deps _docout docdir =
  Seq[Cmd (S[A"rm"; A"-rf"; Px docdir]);
      Cmd (S[A"mkdir"; A"-p"; Px docdir]);
      Cmd (S [!Options.ocamldoc;
              S(List.map (fonc a -> S[A"-load"; P a]) deps);
              T(tags++"doc"++"docdir"); A"-d"; Px docdir])]

soit ocamldoc_l_file tags deps docout _docdir =
  Seq[Cmd (S[A"rm"; A"-rf"; Px docout]);
      Cmd (S[A"mkdir"; A"-p"; Px (Pathname.dirname docout)]);
      Cmd (S [!Options.ocamldoc;
              S(List.map (fonc a -> S[A"-load"; P a]) deps);
              T(tags++"doc"++"docfile"); A"-o"; Px docout])]

soit document_ocaml_interf mli odoc env build =
  soit mli = env mli et odoc = env odoc dans
  Ocaml_compiler.prepare_compile build mli;
  ocamldoc_c (tags_of_pathname mli++"interf") mli odoc

soit document_ocaml_implem ml odoc env build =
  soit ml = env ml et odoc = env odoc dans
  Ocaml_compiler.prepare_compile build ml;
  ocamldoc_c (tags_of_pathname ml++"implem") ml odoc

soit document_ocaml_project ?(ocamldoc=ocamldoc_l_file) odocl docout docdir env build =
  soit odocl = env odocl et docout = env docout et docdir = env docdir dans
  soit contents = string_list_of_file odocl dans
  soit include_dirs = Pathname.include_dirs_of (Pathname.dirname odocl) dans
  soit to_build =
    List.map début fonc module_name ->
      expand_module include_dirs module_name ["odoc"]
    fin contents dans
  soit module_paths = List.map Outcome.good (build to_build) dans
  soit tags = (Tags.union (tags_of_pathname docout) (tags_of_pathname docdir))++"ocaml" dans
  ocamldoc tags module_paths docout docdir

soit camlp4 ?(default=A"camlp4o") tag i o env build =
  soit ml = env i et pp_ml = env o dans
  soit tags = tags_of_pathname ml++"ocaml"++"pp"++tag dans
  soit _ = Rule.build_deps_of_tags build tags dans
  soit pp = Command.reduce (Flags.of_tags tags) dans
  soit pp =
    filtre pp avec
    | N -> default
    | _ -> pp
  dans
  Cmd(S[pp; P ml; A"-printer"; A"o"; A"-o"; Px pp_ml])
