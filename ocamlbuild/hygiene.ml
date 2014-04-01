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


(* Original author: Berke Durak *)
(* Hygiene *)
ouvre My_std
ouvre Slurp

exception Exit_hygiene_violations

type rule =
| Implies_not de pattern * pattern
| Not de pattern
et pattern = suffix
et suffix = string

type penalty = Warn | Fail

type law = {
  law_name : string;
  law_rules : rule list;
  law_penalty : penalty
}

soit list_collect f l =
  soit rec loop result = fonction
    | [] -> List.rev result
    | x :: rest ->
        filtre f x avec
        | None -> loop result rest
        | Some y -> loop (y :: result) rest
  dans
  loop [] l

soit list_none_for_all f l =
  soit rec loop = fonction
    | [] -> None
    | x :: rest ->
        filtre f x avec
        | None -> loop rest
        | y -> y
  dans
  loop l

soit sf = Printf.sprintf

module SS = Set.Make(String);;

soit check ?sanitize laws entry =
  soit penalties = ref [] dans
  soit microbes = ref SS.empty dans
  soit () =
    filtre sanitize avec
    | Some fn -> si sys_file_exists fn alors sys_remove fn
    | None -> ()
  dans
  soit remove path name =
    si sanitize <> None alors
      microbes := SS.add (filename_concat path name) !microbes
  dans
  soit check_rule = fonc entries -> fonction
    | Not suffix ->
        list_collect
          début fonction
            | File(path, name, _, vrai) ->
                si Filename.check_suffix name suffix
                  && not ( Pathname.link_to_dir (filename_concat path name) !Options.build_dir ) alors
                  début
                    remove path name;
                    Some(sf "File %s in %s has suffix %s" name path suffix)
                  fin
                sinon
                  None
            | File _ | Dir _| Error _ | Nothing -> None
          fin
          entries
    | Implies_not(suffix1, suffix2) ->
        list_collect
          début fonction
            | File(path, name, _, vrai) ->
                si Filename.check_suffix name suffix1 alors
                  début
                    soit base = Filename.chop_suffix name suffix1 dans
                    soit name' = base ^ suffix2 dans
                    si List.exists
                       début fonction
                         | File(_, name'', _, vrai) -> name' = name''
                         | File _ | Dir _ | Error _ | Nothing -> faux
                       fin
                       entries
                    alors
                      début
                        remove path name';
                        Some(sf "Files %s and %s should not be together in %s" name name' path)
                      fin
                    sinon
                      None
                  fin
                sinon
                  None
            | File _ | Dir _ | Error _ | Nothing -> None
          fin
          entries
  dans
  soit rec check_entry = fonction
    | Dir(_,_,_,vrai,entries) ->
        List.iter
          début fonc law ->
            filtre List.concat (List.map (check_rule !*entries) law.law_rules) avec
            | [] -> ()
            | explanations ->
              penalties := (law, explanations) :: !penalties
          fin
          laws;
        List.iter check_entry !*entries
    | Dir _ | File _ | Error _ | Nothing -> ()
  dans
  check_entry entry;
  début
    soit microbes = !microbes dans
    si not (SS.is_empty microbes) alors
      début
        filtre sanitize avec
        | None ->
            Log.eprintf "sanitize: the following are files that should probably not be in your\n\
                         source tree:\n";
            SS.iter
              début fonc fn ->
                Log.eprintf " %s" fn
              fin
              microbes;
            Log.eprintf "Remove them manually, don't use the -no-sanitize option, use -no-hygiene, or\n\
                          define hygiene exceptions using the tags or plugin mechanism.\n";
            raise Exit_hygiene_violations
        | Some fn ->
            soit m = SS.cardinal microbes dans
            Log.eprintf
              "@[<hov 2>SANITIZE:@ a@ total@ of@ %d@ file%s@ that@ should@ probably\
               @ not@ be@ in@ your@ source@ tree@ has@ been@ found.\
               @ A@ script@ shell@ file@ %S@ is@ being@ created.\
               @ Check@ this@ script@ and@ run@ it@ to@ remove@ unwanted@ files\
               @ or@ use@ other@ options@ (such@ as@ defining@ hygiene@ exceptions\
               @ or@ using@ the@ -no-hygiene@ option).@]"
               m (si m = 1 alors "" sinon "s") fn;
            soit oc = open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_binary] 0o777 fn dans
            (* See PR #5338: under mingw, one produces a shell script, which must follow
               Unix eol convention; hence Open_binary. *)
            soit fp = Printf.fprintf dans
            fp oc "#!/bin/sh\n\
                   # File generated by ocamlbuild\n\
                   \n\
                   cd %s\n\
                   \n" (Shell.quote_filename_if_needed Pathname.pwd);
            SS.iter
              début fonc fn ->
                fp oc "rm -f %s\n" (Shell.quote_filename_if_needed fn)
              fin
              microbes;
            (* Also clean itself *)
            fp oc "# Also clean the script itself\n";
            fp oc "rm -f %s\n" (Shell.quote_filename_if_needed fn);
            close_out oc
      fin;
    !penalties
  fin
;;
