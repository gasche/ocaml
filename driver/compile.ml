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

open Misc
open Format
open Typedtree
open Compenv

(* Compile a .mli file *)

(* the proper way to do this would be to add a configuration option,
   but it's unclear we ever want to upstream this. *)
let reparse = true

let reparse sourcefile print parse ast =
  if not reparse then ast
  else begin
    let cp src tgt =
      ignore (Sys.command
                (Printf.sprintf "cp --preserve=all %s %s"
                   (Filename.quote src) (Filename.quote tgt))) in
    let save_sourcefile k =
      let cpfile = sourcefile ^ ".cp" in
      cp sourcefile cpfile;
      Sys.remove sourcefile;
      let result = try `Ok (k ()) with exn -> `Err exn in
      cp cpfile sourcefile;
      Sys.remove cpfile;
      match result with
      | `Ok v -> v
      | `Err exn -> raise exn
    in
    save_sourcefile begin fun () ->
      let out = open_out sourcefile in
      let ppf = formatter_of_out_channel out in
      print ppf ast;
      pp_print_flush ppf ();
      close_out out;
      try parse sourcefile with exn ->
        cp sourcefile (sourcefile ^ ".dsource");
        raise exn
    end
  end


(* Keep in sync with the copy in optcompile.ml *)

let interface ppf sourcefile outputprefix =
  Compmisc.init_path false;
  let modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) in
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  let initial_env = Compmisc.initial_env () in
  let ast = Pparse.parse_interface ppf sourcefile in
  if !Clflags.dump_parsetree then fprintf ppf "%a@." Printast.interface ast;
  if !Clflags.dump_source then fprintf ppf "%a@." Pprintast.signature ast;
  let ast =
    reparse sourcefile Pprintast.signature (Pparse.parse_interface ppf) ast in
  let tsg = Typemod.transl_signature initial_env ast in
  if !Clflags.dump_typedtree then fprintf ppf "%a@." Printtyped.interface tsg;
  let sg = tsg.sig_type in
  if !Clflags.print_types then
    Printtyp.wrap_printing_env initial_env (fun () ->
        fprintf std_formatter "%a@."
          Printtyp.signature (Typemod.simplify_signature sg));
  ignore (Includemod.signatures initial_env sg sg);
  Typecore.force_delayed_checks ();
  Warnings.check_fatal ();
  if not !Clflags.print_types then begin
    let sg = Env.save_signature sg modulename (outputprefix ^ ".cmi") in
    Typemod.save_signature modulename tsg outputprefix sourcefile
      initial_env sg ;
  end

(* Compile a .ml file *)

let print_if ppf flag printer arg =
  if !flag then fprintf ppf "%a@." printer arg;
  arg

let (++) x f = f x

let implementation ppf sourcefile outputprefix =
  Compmisc.init_path false;
  let modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) in
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  let env = Compmisc.initial_env() in
  if !Clflags.print_types then begin
    let comp ast =
      ast
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ reparse sourcefile Pprintast.structure (Pparse.parse_implementation ppf)
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ print_if ppf Clflags.dump_typedtree
          Printtyped.implementation_with_coercion
      ++ (fun _ -> ());
      Warnings.check_fatal ();
      Stypes.dump (Some (outputprefix ^ ".annot"))
    in
    try comp (Pparse.parse_implementation ppf sourcefile)
    with x ->
      Stypes.dump (Some (outputprefix ^ ".annot"));
      raise x
  end else begin
    let objfile = outputprefix ^ ".cmo" in
    let oc = open_out_bin objfile in
    let comp ast =
      ast
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ print_if ppf Clflags.dump_source Pprintast.structure
      ++ reparse sourcefile Pprintast.structure (Pparse.parse_implementation ppf)
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
    in
    try comp (Pparse.parse_implementation ppf sourcefile)
    with x ->
      close_out oc;
      remove_file objfile;
      Stypes.dump (Some (outputprefix ^ ".annot"));
      raise x
  end

let c_file name =
  Location.input_name := name;
  if Ccomp.compile_file name <> 0 then exit 2
