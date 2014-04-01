(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

ouvre Printf;;

soit printers = ref []

soit locfmt = format_of_string "File \"%s\", line %d, characters %d-%d: %s";;

soit field x i =
  soit f = Obj.field x i dans
  si not (Obj.is_block f) alors
    sprintf "%d" (Obj.magic f : int)           (* can also be a char *)
  sinon si Obj.tag f = Obj.string_tag alors
    sprintf "%S" (Obj.magic f : string)
  sinon si Obj.tag f = Obj.double_tag alors
    string_of_float (Obj.magic f : float)
  sinon
    "_"
;;
soit rec other_fields x i =
  si i >= Obj.size x alors ""
  sinon sprintf ", %s%s" (field x i) (other_fields x (i+1))
;;
soit fields x =
  filtre Obj.size x avec
  | 0 -> ""
  | 1 -> ""
  | 2 -> sprintf "(%s)" (field x 1)
  | n -> sprintf "(%s%s)" (field x 1) (other_fields x 2)
;;

soit to_string x =
  soit rec conv = fonction
    | hd :: tl ->
        (filtre essaie hd x avec _ -> None avec
        | Some s -> s
        | None -> conv tl)
    | [] ->
        filtre x avec
        | Out_of_memory -> "Out of memory"
        | Stack_overflow -> "Stack overflow"
        | Match_failure(file, line, char) ->
            sprintf locfmt file line char (char+5) "Pattern matching failed"
        | Assert_failure(file, line, char) ->
            sprintf locfmt file line char (char+6) "Assertion failed"
        | Undefined_recursive_module(file, line, char) ->
            sprintf locfmt file line char (char+6) "Undefined recursive module"
        | _ ->
            soit x = Obj.repr x dans
            si Obj.tag x <> 0 alors
              (Obj.magic (Obj.field x 0) : string)
            sinon
              soit constructor =
                (Obj.magic (Obj.field (Obj.field x 0) 0) : string) dans
              constructor ^ (fields x) dans
  conv !printers

soit print fct arg =
  essaie
    fct arg
  avec x ->
    eprintf "Uncaught exception: %s\n" (to_string x);
    flush stderr;
    raise x

soit catch fct arg =
  essaie
    fct arg
  avec x ->
    flush stdout;
    eprintf "Uncaught exception: %s\n" (to_string x);
    exit 2

type raw_backtrace

dehors get_raw_backtrace:
  unit -> raw_backtrace = "caml_get_exception_raw_backtrace"

type loc_info =
  | Known_location de bool   (* is_raise *)
                    * string (* filename *)
                    * int    (* line number *)
                    * int    (* start char *)
                    * int    (* end char *)
  | Unknown_location de bool (*is_raise*)

(* to avoid warning *)
soit _ = [Known_location (faux, "", 0, 0, 0); Unknown_location faux]

type backtrace = loc_info array

dehors convert_raw_backtrace:
  raw_backtrace -> backtrace option = "caml_convert_raw_backtrace"

soit format_loc_info pos li =
  soit is_raise =
    filtre li avec
    | Known_location(is_raise, _, _, _, _) -> is_raise
    | Unknown_location(is_raise) -> is_raise dans
  soit info =
    si is_raise alors
      si pos = 0 alors "Raised at" sinon "Re-raised at"
    sinon
      si pos = 0 alors "Raised by primitive operation at" sinon "Called from"
  dans
  filtre li avec
  | Known_location(is_raise, filename, lineno, startchar, endchar) ->
      sprintf "%s file \"%s\", line %d, characters %d-%d"
              info filename lineno startchar endchar
  | Unknown_location(is_raise) ->
      sprintf "%s unknown location"
              info

soit print_exception_backtrace outchan backtrace =
  filtre backtrace avec
  | None ->
      fprintf outchan
        "(Program not linked with -g, cannot print stack backtrace)\n"
  | Some a ->
      pour i = 0 à Array.length a - 1 faire
        si a.(i) <> Unknown_location vrai alors
          fprintf outchan "%s\n" (format_loc_info i a.(i))
      fait

soit print_raw_backtrace outchan raw_backtrace =
  print_exception_backtrace outchan (convert_raw_backtrace raw_backtrace)

(* confusingly named: prints the global current backtrace *)
soit print_backtrace outchan =
  print_raw_backtrace outchan (get_raw_backtrace ())

soit backtrace_to_string backtrace =
  filtre backtrace avec
  | None ->
     "(Program not linked with -g, cannot print stack backtrace)\n"
  | Some a ->
      soit b = Buffer.create 1024 dans
      pour i = 0 à Array.length a - 1 faire
        si a.(i) <> Unknown_location vrai alors
          bprintf b "%s\n" (format_loc_info i a.(i))
      fait;
      Buffer.contents b

soit raw_backtrace_to_string raw_backtrace =
  backtrace_to_string (convert_raw_backtrace raw_backtrace)

(* confusingly named:
   returns the *string* corresponding to the global current backtrace *)
soit get_backtrace () =
  (* we could use the caml_get_exception_backtrace primitive here, but
     we hope to deprecate it so it's better to just compose the
     raw stuff *)
  backtrace_to_string (convert_raw_backtrace (get_raw_backtrace ()))

dehors record_backtrace: bool -> unit = "caml_record_backtrace"
dehors backtrace_status: unit -> bool = "caml_backtrace_status"

soit register_printer fn =
  printers := fn :: !printers


dehors get_callstack: int -> raw_backtrace = "caml_get_current_callstack"


soit exn_slot x =
  soit x = Obj.repr x dans
  si Obj.tag x = 0 alors Obj.field x 0 sinon x

soit exn_slot_id x =
  soit slot = exn_slot x dans
  (Obj.obj (Obj.field slot 1) : int)

soit exn_slot_name x =
  soit slot = exn_slot x dans
  (Obj.obj (Obj.field slot 0) : string)
