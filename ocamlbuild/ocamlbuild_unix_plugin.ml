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
ouvre Format
ouvre Ocamlbuild_pack
ouvre My_unix

soit report_error f =
  fonction
  | Unix.Unix_error(err, fun_name, arg) ->
      fprintf f "%s: %S a échoué" Sys.argv.(0) fun_name;
      si String.length arg > 0 alors
        fprintf f " on %S" arg;
      fprintf f ": %s" (Unix.error_message err)
  | exn -> raise exn

soit mkstat unix_stat x =
  soit st =
    essaie unix_stat x
    avec Unix.Unix_error _ tel e -> raise (Sys_error (My_std.sbprintf "%a" report_error e))
  dans
  { stat_key = sprintf "(%d,%d)" st.Unix.st_dev st.Unix.st_ino;
    stat_file_kind =
      filtre st.Unix.st_kind avec
      | Unix.S_LNK -> FK_link
      | Unix.S_DIR -> FK_dir
      | Unix.S_CHR | Unix.S_BLK | Unix.S_FIFO | Unix.S_SOCK -> FK_other
      | Unix.S_REG -> FK_file }

soit is_link s = (Unix.lstat s).Unix.st_kind = Unix.S_LNK

soit at_exit_once callback =
  soit pid = Unix.getpid () dans
  at_exit début fonc () ->
    si pid = Unix.getpid () alors callback ()
  fin

soit run_and_open s kont =
  soit ic = Unix.open_process_in s dans
  soit close () =
    filtre Unix.close_process_in ic avec
    | Unix.WEXITED 0 -> ()
    | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
        failwith (Printf.sprintf "Erreur en exécutant: %s" s) dans
  soit res = essaie
      kont ic
    avec e -> (close (); raise e)
  dans close (); res

soit stdout_isatty () =
  Unix.isatty Unix.stdout &&
    essaie Unix.getenv "TERM" <> "dumb" avec Not_found -> vrai

soit execute_many =
  soit exit i = raise (My_std.Exit_with_code i) dans
  soit exit = fonction
    | Ocamlbuild_executor.Subcommand_failed -> exit Exit_codes.rc_executor_subcommand_failed
    | Ocamlbuild_executor.Subcommand_got_signal -> exit Exit_codes.rc_executor_subcommand_got_signal
    | Ocamlbuild_executor.Io_error -> exit Exit_codes.rc_executor_io_error
    | Ocamlbuild_executor.Exceptionl_condition -> exit Exit_codes.rc_executor_excetptional_condition
  dans
  Ocamlbuild_executor.execute ~exit

soit setup () =
  implem.is_degraded <- faux;
  implem.stdout_isatty <- stdout_isatty;
  implem.gettimeofday <- Unix.gettimeofday;
  implem.report_error <- report_error;
  implem.execute_many <- execute_many;
  implem.readlink <- Unix.readlink;
  implem.run_and_open <- run_and_open;
  implem.at_exit_once <- at_exit_once;
  implem.is_link <- is_link;
  implem.stat <- mkstat Unix.stat;
  implem.lstat <- mkstat Unix.lstat;;
