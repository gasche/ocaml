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

soit is_simple_filename s =
  soit ls = String.length s dans
  ls <> 0 &&
  soit rec loop pos =
    si pos >= ls alors vrai sinon
    filtre s.[pos] avec
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '.' | '-' | '/' | '_' | ':' | '@' | '+' | ',' -> loop (pos + 1)
    | _ -> faux dans
  loop 0
soit quote_filename_if_needed s =
  si is_simple_filename s alors s
  (* We should probably be using [Filename.unix_quote] except that function
   * isn't exported. Users on Windows will have to live with not being able to
   * install OCaml into c:\o'caml. Too bad. *)
  sinon si Sys.os_type = "Win32" alors Printf.sprintf "'%s'" s
  sinon Filename.quote s
soit chdir dir =
  reset_filesys_cache ();
  Sys.chdir dir
soit run args target =
  reset_readdir_cache ();
  soit cmd = String.concat " " (List.map quote_filename_if_needed args) dans
  si !*My_unix.is_degraded || Sys.os_type = "Win32" alors
    début
      Log.event cmd target Tags.empty;
      soit st = sys_command cmd dans
      si st <> 0 alors
        failwith (Printf.sprintf "Erreur pendant la commande `%s'.\nCode de sortie %d.\n" cmd st)
      sinon
        ()
    fin
  sinon
    filtre My_unix.execute_many ~ticker:Log.update ~display:Log.display [[(fonc () -> cmd)]] avec
    | None -> ()
    | Some(_, x) ->
      failwith (Printf.sprintf "Erreur pendant la commande %S: %s" cmd (Printexc.to_string x))
soit rm = sys_remove
soit rm_f x =
  si sys_file_exists x alors rm x
soit mkdir dir =
  reset_filesys_cache_for_file dir;
  (*Sys.mkdir dir (* MISSING in ocaml *) *)
  run ["mkdir"; dir] dir
soit try_mkdir dir = si not (sys_file_exists dir) alors mkdir dir
soit rec mkdir_p dir =
  si sys_file_exists dir alors ()
  sinon (mkdir_p (Filename.dirname dir); mkdir dir)

soit cp_pf src dest =
  reset_filesys_cache_for_file dest;
  run["cp";"-pf";src;dest] dest

(* L'Arrete du 2007-03-07 prend en consideration
   differement les archives. Pour les autres fichiers
   le decret du 2007-02-01 est toujours valable :-) *)
soit cp src dst =
  si Filename.check_suffix src ".a"
  && Filename.check_suffix dst ".a"
  alors cp_pf src dst
  (* try to make a hard link *)
  sinon copy_file src dst

soit readlink = My_unix.readlink
soit is_link = My_unix.is_link
soit rm_rf x =
  reset_filesys_cache ();
  run["rm";"-Rf";x] x
soit mv src dest =
  reset_filesys_cache_for_file src;
  reset_filesys_cache_for_file dest;
  run["mv"; src; dest] dest
  (*Sys.rename src dest*)
