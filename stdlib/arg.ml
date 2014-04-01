(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*             Damien Doligez, projet Para, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type key = string
type doc = string
type usage_msg = string
type anon_fun = (string -> unit)

type spec =
  | Unit de (unit -> unit)     (* Call the function with unit argument *)
  | Bool de (bool -> unit)     (* Call the function with a bool argument *)
  | Set de bool ref            (* Set the reference to true *)
  | Clear de bool ref          (* Set the reference to false *)
  | String de (string -> unit) (* Call the function with a string argument *)
  | Set_string de string ref   (* Set the reference to the string argument *)
  | Int de (int -> unit)       (* Call the function with an int argument *)
  | Set_int de int ref         (* Set the reference to the int argument *)
  | Float de (float -> unit)   (* Call the function with a float argument *)
  | Set_float de float ref     (* Set the reference to the float argument *)
  | Tuple de spec list         (* Take several arguments according to the
                                  spec list *)
  | Symbol de string list * (string -> unit)
                               (* Take one of the symbols as argument and
                                  call the function with the symbol. *)
  | Rest de (string -> unit)   (* Stop interpreting keywords and call the
                                  function with each remaining argument *)

exception Bad de string
exception Help de string

type error =
  | Unknown de string
  | Wrong de string * string * string  (* option, actual, expected *)
  | Missing de string
  | Message de string

exception Stop de error;; (* used internally *)

ouvre Printf

soit rec assoc3 x l =
  filtre l avec
  | [] -> raise Not_found
  | (y1, y2, y3) :: t quand y1 = x -> y2
  | _ :: t -> assoc3 x t
;;

soit make_symlist prefix sep suffix l =
  filtre l avec
  | [] -> "<none>"
  | h::t -> (List.fold_left (fonc x y -> x ^ sep ^ y) (prefix ^ h) t) ^ suffix
;;

soit print_spec buf (key, spec, doc) =
  si String.length doc > 0 alors
    filtre spec avec
    | Symbol (l, _) ->
        bprintf buf "  %s %s%s\n" key (make_symlist "{" "|" "}" l) doc
    | _ ->
        bprintf buf "  %s %s\n" key doc
;;

soit help_action () = raise (Stop (Unknown "-help"));;

soit add_help speclist =
  soit add1 =
    essaie ignore (assoc3 "-help" speclist); []
    avec Not_found ->
            ["-help", Unit help_action, " Display this list of options"]
  et add2 =
    essaie ignore (assoc3 "--help" speclist); []
    avec Not_found ->
            ["--help", Unit help_action, " Display this list of options"]
  dans
  speclist @ (add1 @ add2)
;;

soit usage_b buf speclist errmsg =
  bprintf buf "%s\n" errmsg;
  List.iter (print_spec buf) (add_help speclist);
;;

soit usage_string speclist errmsg =
  soit b = Buffer.create 200 dans
  usage_b b speclist errmsg;
  Buffer.contents b;
;;

soit usage speclist errmsg =
  eprintf "%s" (usage_string speclist errmsg);
;;

soit current = ref 0;;

soit parse_argv_dynamic ?(current=current) argv speclist anonfun errmsg =
  soit l = Array.length argv dans
  soit b = Buffer.create 200 dans
  soit initpos = !current dans
  soit stop error =
    soit progname = si initpos < l alors argv.(initpos) sinon "(?)" dans
    début filtre error avec
      | Unknown "-help" -> ()
      | Unknown "--help" -> ()
      | Unknown s ->
          bprintf b "%s: unknown option `%s'.\n" progname s
      | Missing s ->
          bprintf b "%s: option `%s' needs an argument.\n" progname s
      | Wrong (opt, arg, expected) ->
          bprintf b "%s: wrong argument `%s'; option `%s' expects %s.\n"
                  progname arg opt expected
      | Message s ->
          bprintf b "%s: %s.\n" progname s
    fin;
    usage_b b !speclist errmsg;
    si error = Unknown "-help" || error = Unknown "--help"
    alors raise (Help (Buffer.contents b))
    sinon raise (Bad (Buffer.contents b))
  dans
  incr current;
  pendant_que !current < l faire
    soit s = argv.(!current) dans
    si String.length s >= 1 && String.get s 0 = '-' alors début
      soit action =
        essaie assoc3 s !speclist
        avec Not_found -> stop (Unknown s)
      dans
      début essaie
        soit rec treat_action = fonction
        | Unit f -> f ();
        | Bool f quand !current + 1 < l ->
            soit arg = argv.(!current + 1) dans
            début essaie f (bool_of_string arg)
            avec Invalid_argument "bool_of_string" ->
                   raise (Stop (Wrong (s, arg, "a boolean")))
            fin;
            incr current;
        | Set r -> r := vrai;
        | Clear r -> r := faux;
        | String f quand !current + 1 < l ->
            f argv.(!current + 1);
            incr current;
        | Symbol (symb, f) quand !current + 1 < l ->
            soit arg = argv.(!current + 1) dans
            si List.mem arg symb alors début
              f argv.(!current + 1);
              incr current;
            fin sinon début
              raise (Stop (Wrong (s, arg, "one of: "
                                          ^ (make_symlist "" " " "" symb))))
            fin
        | Set_string r quand !current + 1 < l ->
            r := argv.(!current + 1);
            incr current;
        | Int f quand !current + 1 < l ->
            soit arg = argv.(!current + 1) dans
            début essaie f (int_of_string arg)
            avec Failure "int_of_string" ->
                   raise (Stop (Wrong (s, arg, "an integer")))
            fin;
            incr current;
        | Set_int r quand !current + 1 < l ->
            soit arg = argv.(!current + 1) dans
            début essaie r := (int_of_string arg)
            avec Failure "int_of_string" ->
                   raise (Stop (Wrong (s, arg, "an integer")))
            fin;
            incr current;
        | Float f quand !current + 1 < l ->
            soit arg = argv.(!current + 1) dans
            début essaie f (float_of_string arg);
            avec Failure "float_of_string" ->
                   raise (Stop (Wrong (s, arg, "a float")))
            fin;
            incr current;
        | Set_float r quand !current + 1 < l ->
            soit arg = argv.(!current + 1) dans
            début essaie r := (float_of_string arg);
            avec Failure "float_of_string" ->
                   raise (Stop (Wrong (s, arg, "a float")))
            fin;
            incr current;
        | Tuple specs ->
            List.iter treat_action specs;
        | Rest f ->
            pendant_que !current < l - 1 faire
              f argv.(!current + 1);
              incr current;
            fait;
        | _ -> raise (Stop (Missing s))
        dans
        treat_action action
      avec Bad m -> stop (Message m);
         | Stop e -> stop e;
      fin;
      incr current;
    fin sinon début
      (essaie anonfun s avec Bad m -> stop (Message m));
      incr current;
    fin;
  fait;
;;

soit parse_argv ?(current=current) argv speclist anonfun errmsg =
  parse_argv_dynamic ~current:current argv (ref speclist) anonfun errmsg;
;;

soit parse l f msg =
  essaie
    parse_argv Sys.argv l f msg;
  avec
  | Bad msg -> eprintf "%s" msg; exit 2;
  | Help msg -> printf "%s" msg; exit 0;
;;

soit parse_dynamic l f msg =
  essaie
    parse_argv_dynamic Sys.argv l f msg;
  avec
  | Bad msg -> eprintf "%s" msg; exit 2;
  | Help msg -> printf "%s" msg; exit 0;
;;

soit second_word s =
  soit len = String.length s dans
  soit rec loop n =
    si n >= len alors len
    sinon si s.[n] = ' ' alors loop (n+1)
    sinon n
  dans
  essaie loop (String.index s ' ')
  avec Not_found -> len
;;

soit max_arg_len cur (kwd, spec, doc) =
  filtre spec avec
  | Symbol _ -> max cur (String.length kwd)
  | _ -> max cur (String.length kwd + second_word doc)
;;

soit add_padding len ksd =
  filtre ksd avec
  | (_, _, "") ->
      (* Do not pad undocumented options, so that they still don't show up when
       * run through [usage] or [parse]. *)
      ksd
  | (kwd, (Symbol (l, _) tel spec), msg) ->
      soit cutcol = second_word msg dans
      soit spaces = String.make (len - cutcol + 3) ' ' dans
      (kwd, spec, "\n" ^ spaces ^ msg)
  | (kwd, spec, msg) ->
      soit cutcol = second_word msg dans
      soit spaces = String.make (len - String.length kwd - cutcol) ' ' dans
      soit prefix = String.sub msg 0 cutcol dans
      soit suffix = String.sub msg cutcol (String.length msg - cutcol) dans
      (kwd, spec, prefix ^ spaces ^ suffix)
;;

soit align speclist =
  soit completed = add_help speclist dans
  soit len = List.fold_left max_arg_len 0 completed dans
  List.map (add_padding len) completed
;;
