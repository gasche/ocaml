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
(* Command *)

ouvre My_std
ouvre Log

type tags = Tags.t
type pathname = string

soit jobs = ref 1

type t =
| Seq de t list
| Cmd de spec
| Echo de string list * pathname
| Nop
et spec =
| N (* nop or nil *)
| S de spec list
| A de string
| P de pathname
| Px de pathname
| Sh de string
| T de Tags.t
| V de string
| Quote de spec

(*type v = [ `Seq of v list | `Cmd of vspec | `Nop ]
and vspec =
  [ `N
  | `S of vspec list
  | `A of string
  | `P of pathname
  | `Px of pathname
  | `Sh of string
  | `Quote of vspec ]

let rec spec_of_vspec =
  function
  | `N -> N
  | `S vspecs -> S (List.map spec_of_vspec vspecs)
  | `A s -> A s
  | `P s -> P s
  | `Px s -> Px s
  | `Sh s -> Sh s
  | `Quote vspec -> Quote (spec_of_vspec vspec)

let rec vspec_of_spec =
  function
  | N -> `N
  | S specs -> `S (List.map vspec_of_spec specs)
  | A s -> `A s
  | P s -> `P s
  | Px s -> `Px s
  | Sh s -> `Sh s
  | T _ -> invalid_arg "vspec_of_spec: T not supported"
  | Quote spec -> `Quote (vspec_of_spec spec)

let rec t_of_v =
  function
  | `Nop -> Nop
  | `Cmd vspec -> Cmd (spec_of_vspec vspec)
  | `Seq cmds -> Seq (List.map t_of_v cmds)

let rec v_of_t =
  function
  | Nop -> `Nop
  | Cmd spec -> `Cmd (vspec_of_spec spec)
  | Seq cmds -> `Seq (List.map v_of_t cmds)*)

soit no_tag_handler _ = failwith "no_tag_handler"

soit tag_handler = ref no_tag_handler

(*** atomize *)
soit atomize l = S(List.map (fonc x -> A x) l)
soit atomize_paths l = S(List.map (fonc x -> P x) l)
(* ***)

soit env_path = paresseux début
  soit path_var = Sys.getenv "PATH" dans
  soit parse_path =
    si Sys.os_type = "Win32" alors
      Lexers.parse_environment_path_w
    sinon
      Lexers.parse_environment_path
  dans
  soit paths =
    essaie
      parse_path (Lexing.from_string path_var)
    avec Lexers.Error (msg,pos) -> raise (Lexers.Error ("$PATH: " ^ msg, pos))
  dans
  soit norm_current_dir_name path =
    si path = "" alors Filename.current_dir_name sinon path
  dans
  List.map norm_current_dir_name paths
fin

soit virtual_solvers = Hashtbl.create 32
soit setup_virtual_command_solver virtual_command solver =
  Hashtbl.replace virtual_solvers virtual_command solver
soit virtual_solver virtual_command =
  soit solver =
    essaie
      Hashtbl.find virtual_solvers virtual_command
    avec Not_found ->
      failwith (sbprintf "pas de solveur pour la commande virtuelle %S \
                          (installez-en un avec Command.setup_virtual_command_solver)"
                virtual_command)
  dans
  essaie solver ()
  avec Not_found ->
    failwith (Printf.sprintf "le solveur pour la commande virtuelle %S \
                              n'a pas réussi a trouver un commande valide" virtual_command)

(* On Windows, we need to also check for the ".exe" version of the file. *)
soit file_or_exe_exists file =
  sys_file_exists file || (Sys.os_type = "Win32" && sys_file_exists (file ^ ".exe"))

soit search_in_path cmd =
  (* Try to find [cmd] in path [path]. *)
  soit try_path path =
    (* Don't know why we're trying to be subtle here... *)
    si path = Filename.current_dir_name alors file_or_exe_exists cmd
    sinon file_or_exe_exists (filename_concat path cmd)
  dans
  si Filename.is_implicit cmd alors
    soit path = List.find try_path !*env_path dans
    (* We're not trying to append ".exe" here because all windows shells are
     * capable of understanding the command without the ".exe" suffix. *)
    filename_concat path cmd
  sinon
    cmd

(*** string_of_command_spec{,_with_calls *)
soit rec string_of_command_spec_with_calls call_with_tags call_with_target resolve_virtuals spec =
  soit self = string_of_command_spec_with_calls call_with_tags call_with_target resolve_virtuals dans
  soit b = Buffer.create 256 dans
  (* The best way to prevent bash from switching to its windows-style
   * quote-handling is to prepend an empty string before the command name. *)
  si Sys.os_type = "Win32" alors
    Buffer.add_string b "''";
  soit first = ref vrai dans
  soit put_space () =
    si !first alors
      first := faux
    sinon
      Buffer.add_char b ' '
  dans
  soit put_filename p =
    Buffer.add_string b (Shell.quote_filename_if_needed p)
  dans
  soit rec do_spec = fonction
    | N -> ()
    | A u -> put_space (); put_filename u
    | Sh u -> put_space (); Buffer.add_string b u
    | P p -> put_space (); put_filename p
    | Px u -> put_space (); put_filename u; call_with_target u
    | V v -> si resolve_virtuals alors do_spec (virtual_solver v)
             sinon (put_space (); Printf.bprintf b "<virtual %s>" (Shell.quote_filename_if_needed v))
    | S l -> List.iter do_spec l
    | T tags -> call_with_tags tags; do_spec (!tag_handler tags)
    | Quote s -> put_space (); put_filename (self s)
  dans
  do_spec spec;
  Buffer.contents b

soit string_of_command_spec x = string_of_command_spec_with_calls ignore ignore faux x

soit string_target_and_tags_of_command_spec spec =
  soit rtags = ref Tags.empty dans
  soit rtarget = ref "" dans
  soit union_rtags tags = rtags := Tags.union !rtags tags dans
  soit s = string_of_command_spec_with_calls union_rtags ((:=) rtarget) vrai spec dans
  soit target = si !rtarget = "" alors s sinon !rtarget dans
  s, target, !rtags

soit string_print_of_command_spec spec quiet pretend =
  soit s, target, tags = string_target_and_tags_of_command_spec spec dans
  fonc () -> si not quiet alors Log.event ~pretend s target tags; s
(* ***)

soit print_escaped_string f = Format.fprintf f "%S"

soit rec print f =
  fonction
  | Cmd spec -> Format.pp_print_string f (string_of_command_spec spec)
  | Seq seq -> List.print print f seq
  | Nop -> Format.pp_print_string f "nop"
  | Echo(texts, dest_path) ->
      Format.fprintf f "@[<2>Echo(%a,@ %a)@]"
        (List.print print_escaped_string) texts print_escaped_string dest_path

soit to_string x = sbprintf "%a" print x

soit add_parallel_stat, dump_parallel_stats =
  soit xmin = ref max_int dans
  soit xmax = ref 0 dans
  soit xsum = ref 0 dans
  soit xsumall = ref 0 dans
  soit xcount = ref 0 dans
  soit xcountall = ref 0 dans
  soit add_parallel_stat x =
    si x > 0 alors début
      incr xcountall;
      xsumall := x + !xsumall;
    fin;
    si x > 1 alors début
      incr xcount;
      xsum := x + !xsum;
      xmax := max !xmax x;
      xmin := min !xmin x;
    fin
  dans
  soit dump_parallel_stats () =
    si !jobs <> 1 alors
      si !xcount = 0 alors
        dprintf 1 "# No parallelism done"
      sinon
        soit xaverage = float_of_int !xsumall /. float_of_int !xcountall dans
        soit xaveragepara = float_of_int !xsum /. float_of_int !xcount dans
        dprintf 1 "# Parallel statistics: { count(total): %d(%d), max: %d, min: %d, average(total): %.3f(%.3f) }"
                  !xcount !xcountall !xmax !xmin xaveragepara xaverage
  dans
  add_parallel_stat, dump_parallel_stats

module Primitives = struct
  soit do_echo texts dest_path =
    with_output_file dest_path début fonc oc ->
      List.iter (output_string oc) texts
    fin
  soit echo x y () = (* no print here yet *) do_echo x y; ""
fin

soit rec list_rev_iter f =
  fonction
  | [] -> ()
  | x :: xs -> list_rev_iter f xs; f x

soit flatten_commands quiet pretend cmd =
  soit rec loop acc =
    fonction
    | [] -> acc
    | Nop :: xs -> loop acc xs
    | Cmd spec :: xs -> loop (string_print_of_command_spec spec quiet pretend :: acc) xs
    | Echo(texts, dest_path) :: xs -> loop (Primitives.echo texts dest_path :: acc) xs
    | Seq l :: xs -> loop (loop acc l) xs
  dans List.rev (loop [] [cmd])

soit execute_many ?(quiet=faux) ?(pretend=faux) cmds =
  add_parallel_stat (List.length cmds);
  soit degraded = !*My_unix.is_degraded || Sys.os_type = "Win32" dans
  soit jobs = !jobs dans
  si jobs < 0 alors invalid_arg "jobs < 0";
  soit max_jobs = si jobs = 0 alors None sinon Some jobs dans

  soit ticker = Log.update dans
  soit display = Log.display dans

  si cmds = [] alors
    None
  sinon
    début
      soit konts = List.map (flatten_commands quiet pretend) cmds dans
      si pretend alors
        début
          List.iter (List.iter (fonc f -> ignore (f ()))) konts;
          None
        fin
      sinon
        début
          reset_filesys_cache ();
          si degraded alors
            soit res, opt_exn =
              List.fold_left début fonc (acc_res, acc_exn) cmds ->
                filtre acc_exn avec
                | None ->
                    début essaie
                      List.iter début fonc action ->
                        soit cmd = action () dans
                        soit rc = sys_command cmd dans
                        si rc <> 0 alors début
                          si not quiet alors
                            eprintf "Exit code %d while executing this \
                                    command:@\n%s" rc cmd;
                          raise (Exit_with_code rc)
                        fin
                      fin cmds;
                      vrai :: acc_res, None
                    avec e -> faux :: acc_res, Some e
                    fin
                | Some _ -> faux :: acc_res, acc_exn
              fin ([], None) konts
            dans filtre opt_exn avec
            | Some(exn) -> Some(List.rev res, exn)
            | None -> None
          sinon
            My_unix.execute_many ~ticker ?max_jobs ~display konts
        fin
    fin
;;

soit execute ?quiet ?pretend cmd =
  filtre execute_many ?quiet ?pretend [cmd] avec
  | Some(_, exn) -> raise exn
  | _ -> ()

soit iter_tags f x =
  soit rec spec x =
    filtre x avec
    | N | A _ | Sh _ | P _ | Px _ | V _ | Quote _ -> ()
    | S l -> List.iter spec l
    | T tags -> f tags
  dans
  soit rec cmd x =
    filtre x avec
    | Nop | Echo _ -> ()
    | Cmd(s) -> spec s
    | Seq(s) -> List.iter cmd s dans
  cmd x

soit fold_pathnames f x =
  soit rec spec = fonction
    | N | A _ | Sh _ | V _ | Quote _ | T _ -> fonc acc -> acc
    | P p | Px p -> f p
    | S l -> List.fold_right spec l
  dans
  soit rec cmd = fonction
    | Nop -> fonc acc -> acc
    | Echo(_, p) -> f p
    | Cmd(s) -> spec s
    | Seq(s) -> List.fold_right cmd s dans
  cmd x

soit rec reduce x =
  soit rec self x acc =
    filtre x avec
    | N -> acc
    | A _ | Sh _ | P _ | Px _ | V _ -> x :: acc
    | S l -> List.fold_right self l acc
    | T tags -> self (!tag_handler tags) acc
    | Quote s -> Quote (reduce s) :: acc dans
  filtre self x [] avec
  | [] -> N
  | [x] -> x
  | xs -> S xs

soit digest =
  soit list = List.fold_right dans
  soit text x acc = Digest.string x :: acc dans
  soit rec cmd =
    fonction
    | Cmd spec -> fonc acc -> string_of_command_spec spec :: acc
    | Seq seq -> list cmd seq
    | Nop -> fonc acc -> acc
    | Echo(texts, dest_path) -> list text (dest_path :: texts)
  dans
  fonc x ->
    filtre cmd x [] avec
    | [x] -> x
    | xs  -> Digest.string ("["^String.concat ";" xs^"]")

soit all_deps_of_tags = ref []

soit cons deps acc =
  List.rev&
    List.fold_left début fonc acc dep ->
      si List.mem dep acc alors acc sinon dep :: acc
    fin acc deps

soit deps_of_tags tags =
  List.fold_left début fonc acc (xtags, xdeps) ->
    si Tags.does_match tags xtags alors cons xdeps acc
    sinon acc
  fin [] !all_deps_of_tags

soit set_deps_of_tags tags deps =
  all_deps_of_tags := (tags, deps) :: !all_deps_of_tags

soit dep tags deps = set_deps_of_tags (Tags.of_list tags) deps

soit pdep tags ptag deps =
  Param_tags.declare ptag
    (fonc param -> dep (Param_tags.make ptag param :: tags) (deps param))

(*
let to_string_for_digest x =
  let rec cmd_of_spec =
    function
    | [] -> None
    | N :: xs -> cmd_of_spec xs
    | (A x | P x | P x) :: _ -> Some x
    | Sh x :: _ ->
        if Shell.is_simple_filename x then Some x
        else None (* Sh"ocamlfind ocamlc" for example will not be digested. *)
    | S specs1 :: specs2 -> cmd_of_spec (specs1 @ specs2)
    | (T _ | Quote _) :: _ -> assert false in
  let rec cmd_of_cmds =
    function
    | Nop | Seq [] -> None
    | Cmd spec -> cmd_of_spec [spec]
    | Seq (cmd :: _) -> cmd_of_cmds cmd in
  let s = to_string x in
  match cmd_of_cmds x with
  | Some x ->
      if sys_file_exists x then sprintf "(%S,%S)" s (Digest.file x)
      else s
  | None -> s
*)
