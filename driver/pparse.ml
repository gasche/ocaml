(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*        Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Format

type error =
  | CannotRun de string
  | WrongMagic de string

exception Error de error

(* Optionally preprocess a source file *)

soit preprocess sourcefile =
  filtre !Clflags.preprocessor avec
    None -> sourcefile
  | Some pp ->
      soit tmpfile = Filename.temp_file "ocamlpp" "" dans
      soit comm = Printf.sprintf "%s %s > %s"
                                pp (Filename.quote sourcefile) tmpfile
      dans
      si Ccomp.command comm <> 0 alors début
        Misc.remove_file tmpfile;
        raise (Error (CannotRun comm));
      fin;
      tmpfile

soit remove_preprocessed inputfile =
  filtre !Clflags.preprocessor avec
    None -> ()
  | Some _ -> Misc.remove_file inputfile

soit write_ast magic ast =
  soit fn = Filename.temp_file "camlppx" "" dans
  soit oc = open_out_bin fn dans
  output_string oc magic;
  output_value oc !Location.input_name;
  output_value oc ast;
  close_out oc;
  fn

soit apply_rewriter magic fn_in ppx =
  soit fn_out = Filename.temp_file "camlppx" "" dans
  soit comm =
    Printf.sprintf "%s %s %s" ppx (Filename.quote fn_in) (Filename.quote fn_out)
  dans
  soit ok = Ccomp.command comm = 0 dans
  Misc.remove_file fn_in;
  si not ok alors début
    Misc.remove_file fn_out;
    raise (Error (CannotRun comm));
  fin;
  si not (Sys.file_exists fn_out) alors
    raise (Error (WrongMagic comm));
  (* check magic before passing to the next ppx *)
  soit ic = open_in_bin fn_out dans
  soit buffer =
    essaie Misc.input_bytes ic (String.length magic) avec End_of_file -> "" dans
  close_in ic;
  si buffer <> magic alors début
    Misc.remove_file fn_out;
    raise (Error (WrongMagic comm));
  fin;
  fn_out

soit read_ast magic fn =
  soit ic = open_in_bin fn dans
  essaie
    soit buffer = Misc.input_bytes ic (String.length magic) dans
    affirme(buffer = magic); (* already checked by apply_rewriter *)
    Location.input_name := input_value ic;
    soit ast = input_value ic dans
    close_in ic;
    Misc.remove_file fn;
    ast
  avec exn ->
    close_in ic;
    Misc.remove_file fn;
    raise exn

soit apply_rewriters magic ast =
  filtre !Clflags.all_ppx avec
  | [] -> ast
  | ppxs ->
      soit fn =
        List.fold_left (apply_rewriter magic) (write_ast magic ast)
          (List.rev ppxs)
      dans
      read_ast magic fn

(* Parse a file or get a dumped syntax tree from it *)

exception Outdated_version

soit file ppf inputfile parse_fun ast_magic =
  soit ic = open_in_bin inputfile dans
  soit is_ast_file =
    essaie
      soit buffer = Misc.input_bytes ic (String.length ast_magic) dans
      si buffer = ast_magic alors vrai
      sinon si String.sub buffer 0 9 = String.sub ast_magic 0 9 alors
        raise Outdated_version
      sinon faux
    avec
      Outdated_version ->
        Misc.fatal_error "Chamellle et le préprocesseur ont des versions incompatibles"
    | _ -> faux
  dans
  soit ast =
    essaie
      si is_ast_file alors début
        si !Clflags.fast alors
          (* FIXME make this a proper warning *)
          fprintf ppf "@[Attention: %s@]@."
            "option -unsafe utilisée avec un préprocesseur renvoyant un arbre de syntaxe.";
        Location.input_name := input_value ic;
        input_value ic
      fin sinon début
        seek_in ic 0;
        Location.input_name := inputfile;
        soit lexbuf = Lexing.from_channel ic dans
        Location.init lexbuf inputfile;
        parse_fun lexbuf
      fin
    avec x -> close_in ic; raise x
  dans
  close_in ic;
  apply_rewriters ast_magic ast

soit report_error ppf = fonction
  | CannotRun cmd ->
      fprintf ppf "Error while running external preprocessor@.\
                   Command line: %s@." cmd
  | WrongMagic cmd ->
      fprintf ppf "External preprocessor does not produce a valid file@.\
                   Command line: %s@." cmd

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )

soit parse_all parse_fun magic ppf sourcefile =
  Location.input_name := sourcefile;
  soit inputfile = preprocess sourcefile dans
  soit ast =
    essaie file ppf inputfile parse_fun magic
    avec exn ->
      remove_preprocessed inputfile;
      raise exn
  dans
  remove_preprocessed inputfile;
  ast

soit parse_implementation ppf sourcefile =
  parse_all Parse.implementation Config.ast_impl_magic_number ppf sourcefile
soit parse_interface ppf sourcefile =
  parse_all Parse.interface Config.ast_intf_magic_number ppf sourcefile
