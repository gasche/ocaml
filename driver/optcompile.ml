(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* The batch compiler *)

ouvre Misc
ouvre Config
ouvre Format
ouvre Typedtree
ouvre Compenv

(* Compile a .mli file *)

(* Keep in sync with the copy in compile.ml *)

soit interface ppf sourcefile outputprefix =
  Compmisc.init_path faux;
  soit modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) dans
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  soit initial_env = Compmisc.initial_env () dans
  soit ast = Pparse.parse_interface ppf sourcefile dans
  si !Clflags.dump_parsetree alors fprintf ppf "%a@." Printast.interface ast;
  si !Clflags.dump_source alors fprintf ppf "%a@." Pprintast.signature ast;
  soit tsg = Typemod.transl_signature initial_env ast dans
  si !Clflags.dump_typedtree alors fprintf ppf "%a@." Printtyped.interface tsg;
  soit sg = tsg.sig_type dans
  si !Clflags.print_types alors
    Printtyp.wrap_printing_env initial_env (fonc () ->
        fprintf std_formatter "%a@."
          Printtyp.signature (Typemod.simplify_signature sg));
  ignore (Includemod.signatures initial_env sg sg);
  Typecore.force_delayed_checks ();
  Warnings.check_fatal ();
  si not !Clflags.print_types alors début
    soit sg = Env.save_signature sg modulename (outputprefix ^ ".cmi") dans
    Typemod.save_signature modulename tsg outputprefix sourcefile
      initial_env sg ;
  fin

(* Compile a .ml file *)

soit print_if ppf flag printer arg =
  si !flag alors fprintf ppf "%a@." printer arg;
  arg

soit (++) x f = f x
soit (+++) (x, y) f = (x, f y)

soit implementation ppf sourcefile outputprefix =
  Compmisc.init_path vrai;
  soit modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) dans
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  soit env = Compmisc.initial_env() dans
  Compilenv.reset ?packname:!Clflags.for_package modulename;
  soit cmxfile = outputprefix ^ ".cmx" dans
  soit objfile = outputprefix ^ ext_obj dans
  soit comp ast =
    si !Clflags.print_types
    alors
      ast
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ print_if ppf Clflags.dump_typedtree
          Printtyped.implementation_with_coercion
      ++ (fonc _ -> ())
    sinon début
      ast
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ print_if ppf Clflags.dump_typedtree
          Printtyped.implementation_with_coercion
      ++ Translmod.transl_store_implementation modulename
      +++ print_if ppf Clflags.dump_rawlambda Printlambda.lambda
      +++ Simplif.simplify_lambda
      +++ print_if ppf Clflags.dump_lambda Printlambda.lambda
      ++ Asmgen.compile_implementation outputprefix ppf;
      Compilenv.save_unit_info cmxfile;
    fin;
    Warnings.check_fatal ();
    Stypes.dump (Some (outputprefix ^ ".annot"))
  dans
  essaie comp (Pparse.parse_implementation ppf sourcefile)
  avec x ->
    Stypes.dump (Some (outputprefix ^ ".annot"));
    remove_file objfile;
    remove_file cmxfile;
    raise x

soit c_file name =
  si Ccomp.compile_file name <> 0 alors exit 2
