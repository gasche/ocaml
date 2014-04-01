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

type file_kind =
| FK_dir
| FK_file
| FK_link
| FK_other

type stats =
  {
    stat_file_kind : file_kind;
    stat_key       : string
  }

type implem =
  {
    modifiable is_degraded   : bool;
    modifiable is_link       : string -> bool;
    modifiable run_and_open  : 'a . string -> (in_channel -> 'a) -> 'a;
    modifiable readlink      : string -> string;
    modifiable execute_many  : ?max_jobs:int ->
                            ?ticker:(unit -> unit) ->
                            ?period:float ->
                            ?display:((out_channel -> unit) -> unit) ->
                            ((unit -> string) list list) ->
                            (bool list * exn) option;
    modifiable report_error  : Format.formatter -> exn -> unit;
    modifiable at_exit_once  : (unit -> unit) -> unit;
    modifiable gettimeofday  : unit -> float;
    modifiable stdout_isatty : unit -> bool;
    modifiable stat          : string -> stats;
    modifiable lstat         : string -> stats;
  }

soit is_degraded = vrai

soit stat f =
  { stat_key = f;
    stat_file_kind =
      si sys_file_exists f alors
        si Sys.is_directory f alors
          FK_dir
        sinon
          FK_file
      sinon soit _ = with_input_file f input_char dans affirme faux }

soit run_and_open s kont =
  with_temp_file "ocamlbuild" "out" début fonc tmp ->
    soit s = Printf.sprintf "%s > '%s'" s tmp dans
    soit st = sys_command s dans
    si st <> 0 alors failwith (Printf.sprintf "Erreur en exécutant : %s" s);
    with_input_file tmp kont
  fin

exception Not_a_link
exception No_such_file
exception Link_to_directories_not_supported

soit readlinkcmd =
  soit cache = Hashtbl.create 32 dans
  fonc x ->
    essaie Hashtbl.find cache x
    avec Not_found ->
      run_and_open (Printf.sprintf "readlink %s" (Filename.quote x)) début fonc ic ->
        soit y = String.chomp (input_line ic) dans
        Hashtbl.replace cache x y; y
      fin

soit rec readlink x =
  si sys_file_exists x alors
    essaie
      soit y = readlinkcmd x dans
      si (lstat y).stat_file_kind = FK_dir alors raise Link_to_directories_not_supported sinon y
    avec Failure(_) -> raise Not_a_link
  sinon raise No_such_file

et is_link x =
  essaie ignore(readlink x); vrai avec
  | No_such_file | Not_a_link -> faux

et lstat x =
  si is_link x alors { stat_key = x; stat_file_kind = FK_link } sinon stat x

soit implem =
  {
    is_degraded = vrai;

    stat = stat;
    lstat = lstat;
    readlink = readlink;
    is_link = is_link;
    run_and_open = run_and_open;

    (* at_exit_once is at_exit in the degraded mode since fork is not accessible in this mode *)
    at_exit_once = at_exit;
    report_error = (fonc _ -> raise);
    gettimeofday = (fonc () -> affirme faux);
    stdout_isatty = (fonc () -> faux);
    execute_many = (fonc ?max_jobs:(_) ?ticker:(_) ?period:(_) ?display:(_) _ -> affirme faux)
  }

soit is_degraded = paresseux implem.is_degraded
soit stat x = implem.stat x
soit lstat x = implem.lstat x
soit readlink x = implem.readlink x
soit is_link x = implem.is_link x
soit run_and_open x = implem.run_and_open x
soit at_exit_once x = implem.at_exit_once x
soit report_error x = implem.report_error x
soit gettimeofday x = implem.gettimeofday x
soit stdout_isatty x = implem.stdout_isatty x
soit execute_many ?max_jobs = implem.execute_many ?max_jobs

soit run_and_read cmd =
  soit bufsiz = 2048 dans
  soit buf = String.create bufsiz dans
  soit totalbuf = Buffer.create 4096 dans
  implem.run_and_open cmd début fonc ic ->
    soit rec loop pos =
      soit len = input ic buf 0 bufsiz dans
      si len > 0 alors début
        Buffer.add_substring totalbuf buf 0 len;
        loop (pos + len)
      fin
    dans loop 0; Buffer.contents totalbuf
  fin
