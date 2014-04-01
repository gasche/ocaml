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
ouvre Format
ouvre Typedtree
ouvre Compenv

(* Compile a .mli file *)

module Roundtrip = struct
  soit cp src tgt =
    affirme (0 = Sys.command (Printf.sprintf "cp --preserve=all %s %s"
                               (Filename.quote src) (Filename.quote tgt)))

  type 'a result = Ok de 'a | Err de exn

  soit save sourcefile k =
    soit cpfile = sourcefile ^ ".cp" dans
    cp sourcefile cpfile;
    Sys.remove sourcefile;
    soit result = essaie Ok (k ()) avec exn -> Err exn dans
    cp cpfile sourcefile;
    Sys.remove cpfile;
    filtre result avec
    | Ok v -> v
    | Err exn -> raise exn

  (* the proper way to do this would be to add configuration options,
     but it's unclear we ever want to upstream this. *)
  soit reparse_conf = (essaie Sys.getenv "OCAML_PARSE_ROUNDTRIP" <> "" avec _ -> faux)
  soit relex_conf = not (essaie Sys.getenv "OCAML_LEX_NO_ROUNDTRIP" <> "" avec _ -> faux)

  soit reparse sourcefile print parse ast =
    si not reparse_conf alors ast
    sinon save sourcefile début fonc () ->
      soit out = open_out sourcefile dans
      soit ppf = formatter_of_out_channel out dans
      print ppf ast;
      pp_print_flush ppf ();
      close_out out;
      essaie parse sourcefile avec exn ->
        cp sourcefile (sourcefile ^ ".dsource");
        raise exn
    fin

  soit relex parse_fun sourcefile =
    si relex_conf alors début
      soit inc = open_in sourcefile dans
      soit outbuf = Buffer.create 100 dans
      début
        essaie
          Location.input_name := sourcefile;
          soit lexbuf = Lexing.from_channel inc dans
          Location.init lexbuf sourcefile;
          pendant_que
            soit tok = Lexer.token_with_comments_and_whitespace lexbuf dans
            si tok = Parser.EOF alors faux
            sinon début
              Buffer.add_string outbuf (Lexer.string_of_token tok);
              vrai
            fin
          faire () fait;
          close_in inc;
        avec exn ->
          close_in inc; raise exn
      fin;
      essaie
        soit count = ref 1 dans
        soit backup () =
          sourcefile ^ ".bak"
          ^ (si !count = 1 alors "" sinon string_of_int !count) dans
        pendant_que Sys.file_exists (backup ()) faire incr count fait;
        Sys.rename sourcefile (backup ());
        soit outc = open_out sourcefile dans
        Buffer.output_buffer outc outbuf;
        close_out outc;
      avec _ ->
        (* if sourcefile is not writable, so be it, we'll ignore
           errors and leave the file unchanged; some people are averse
           to progress *)
        ();
    fin;
    parse_fun sourcefile
fin

(* Keep in sync with the copy in optcompile.ml *)

soit interface ppf sourcefile outputprefix =
  Compmisc.init_path faux;
  soit modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) dans
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  soit initial_env = Compmisc.initial_env () dans
  soit ast = Roundtrip.relex (Pparse.parse_interface ppf) sourcefile dans
  si !Clflags.dump_parsetree alors fprintf ppf "%a@." Printast.interface ast;
  si !Clflags.dump_source alors fprintf ppf "%a@." Pprintast.signature ast;
  soit ast =
    Roundtrip.reparse sourcefile
      Pprintast.signature (Pparse.parse_interface ppf) ast dans
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

soit implementation ppf sourcefile outputprefix =
  Compmisc.init_path faux;
  soit modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) dans
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  soit env = Compmisc.initial_env() dans
  si !Clflags.print_types alors début
    soit comp ast =
      ast
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ Roundtrip.reparse sourcefile
           Pprintast.structure (Pparse.parse_implementation ppf)
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ print_if ppf Clflags.dump_typedtree
          Printtyped.implementation_with_coercion
      ++ (fonc _ -> ());
      Warnings.check_fatal ();
      Stypes.dump (Some (outputprefix ^ ".annot"))
    dans
    essaie comp (Roundtrip.relex (Pparse.parse_implementation ppf) sourcefile)
    avec x ->
      Stypes.dump (Some (outputprefix ^ ".annot"));
      raise x
  fin sinon début
    soit objfile = outputprefix ^ ".cmo" dans
    soit oc = open_out_bin objfile dans
    soit comp ast =
      ast
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ Roundtrip.reparse sourcefile
           Pprintast.structure (Pparse.parse_implementation ppf)
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ print_if ppf Clflags.dump_typedtree
                  Printtyped.implementation_with_coercion
      ++ Translmod.transl_implementation modulename
      ++ print_if ppf Clflags.dump_rawlambda Printlambda.lambda
      ++ Simplif.simplify_lambda
      ++ print_if ppf Clflags.dump_lambda Printlambda.lambda
      ++ Bytegen.compile_implementation modulename
      ++ print_if ppf Clflags.dump_instr Printinstr.instrlist
      ++ Emitcode.to_file oc modulename;
      Warnings.check_fatal ();
      close_out oc;
      Stypes.dump (Some (outputprefix ^ ".annot"))
    dans
    essaie comp (Roundtrip.relex (Pparse.parse_implementation ppf) sourcefile)
    avec x ->
      close_out oc;
      remove_file objfile;
      Stypes.dump (Some (outputprefix ^ ".annot"));
      raise x
  fin

soit c_file name =
  Location.input_name := name;
  si Ccomp.compile_file name <> 0 alors exit 2
