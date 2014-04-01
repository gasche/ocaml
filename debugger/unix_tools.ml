(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(****************** Tools for Unix *************************************)

ouvre Misc
ouvre Unix
ouvre Primitives

(*** Convert a socket name into a socket address. ***)
soit convert_address address =
  essaie
    soit n = String.index address ':' dans
      soit host = String.sub address 0 n
      et port = String.sub address (n + 1) (String.length address - n - 1)
      dans
        (PF_INET,
         ADDR_INET
           ((essaie inet_addr_of_string host avec Failure _ ->
               essaie (gethostbyname host).h_addr_list.(0) avec Not_found ->
                 prerr_endline ("Hôte inconnu: " ^ host);
                 failwith "Impossible de convertir l'adresse"),
            (essaie int_of_string port avec Failure _ ->
               prerr_endline "Le numéro du port doit être un entier";
               failwith "Impossible de convertir l'adresse")))
  avec Not_found ->
    filtre Sys.os_type avec
      "Win32" -> failwith "Les chausettes Unix ne sont pas supportées"
    | _ -> (PF_UNIX, ADDR_UNIX address)

(*** Report a unix error. ***)
soit report_error = fonction
  | Unix_error (err, fun_name, arg) ->
     prerr_string "Unix error: '";
     prerr_string fun_name;
     prerr_string "' failed";
     si String.length arg > 0 alors
       (prerr_string " on '";
        prerr_string arg;
        prerr_string "'");
     prerr_string ": ";
     prerr_endline (error_message err)
  | _ -> fatal_error "report_error: ce n'est pas une erreur Unix"

(* Find program `name' in `PATH'. *)
(* Return the full path if found. *)
(* Raise `Not_found' otherwise. *)
soit search_in_path name =
  Printf.fprintf Pervasives.stderr "search_in_path [%s]\n%!" name;
  soit check name =
    essaie access name [X_OK]; name avec Unix_error _ -> raise Not_found
  dans
    si not (Filename.is_implicit name) alors
      check name
    sinon
      soit path = Sys.getenv "PATH" dans
        soit length = String.length path dans
          soit rec traverse pointer =
            si (pointer >= length) || (path.[pointer] = ':') alors
              pointer
            sinon
              traverse (pointer + 1)
          dans
            soit rec find pos =
              soit pos2 = traverse pos dans
                soit directory = (String.sub path pos (pos2 - pos)) dans
                  soit fullname =
                    si directory = "" alors name sinon directory ^ "/" ^ name
                  dans
                    essaie check fullname avec
                    | Not_found ->
                        si pos2 < length alors find (pos2 + 1)
                        sinon raise Not_found
          dans
            find 0

(* Expand a path. *)
(* ### path -> path' *)
soit rec expand_path ch =
  soit rec subst_variable ch =
    essaie
      soit pos = String.index ch '$' dans
        si (pos + 1 < String.length ch) && (ch.[pos + 1] = '$') alors
          (String.sub ch 0 (pos + 1))
            ^ (subst_variable
                 (String.sub ch (pos + 2) (String.length ch - pos - 2)))
        sinon
          (String.sub ch 0 pos)
            ^ (subst2 (String.sub ch (pos + 1) (String.length ch - pos - 1)))
    avec Not_found ->
      ch
  et subst2 ch =
    soit suiv =
      soit i = ref 0 dans
        pendant_que !i < String.length ch &&
              (soit c = ch.[!i] dans (c >= 'a' && c <= 'z')
                               || (c >= 'A' && c <= 'Z')
                               || (c >= '0' && c <= '9')
                               || c = '_')
        faire incr i fait;
        !i
    dans (Sys.getenv (String.sub ch 0 suiv))
       ^ (subst_variable (String.sub ch suiv (String.length ch - suiv)))
  dans
    soit ch = subst_variable ch dans
      soit concat_root nom ch2 =
        essaie Filename.concat (getpwnam nom).pw_dir ch2
        avec Not_found ->
          "~" ^ nom
      dans
        si ch.[0] = '~' alors
          essaie
            filtre String.index ch '/' avec
              1 ->
                (soit tail = String.sub ch 2 (String.length ch - 2)
                 dans
                   essaie Filename.concat (Sys.getenv "HOME") tail
                   avec Not_found ->
                     concat_root (Sys.getenv "LOGNAME") tail)
            |  n -> concat_root
                      (String.sub ch 1 (n - 1))
                      (String.sub ch (n + 1) (String.length ch - n - 1))
          avec
            Not_found ->
              expand_path (ch ^ "/")
        sinon ch

soit make_absolute name =
  si Filename.is_relative name
  alors Filename.concat (getcwd ()) name
  sinon name
;;
