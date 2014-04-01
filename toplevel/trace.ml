(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* The "trace" facility *)

ouvre Format
ouvre Misc
ouvre Longident
ouvre Types
ouvre Toploop

type codeptr = Obj.t

type traced_function =
  { path: Path.t;                       (* Name under which it is traced *)
    closure: Obj.t;                     (* Its function closure (patched) *)
    actual_code: codeptr;               (* Its original code pointer *)
    instrumented_fun: codeptr -> Obj.t -> Obj.t -> Obj.t }
                                        (* Printing function *)

soit traced_functions = ref ([] : traced_function list)

(* Check if a function is already traced *)

soit is_traced clos =
  soit rec is_traced = fonction
      [] -> None
    | tf :: rem -> si tf.closure == clos alors Some tf.path sinon is_traced rem
  dans is_traced !traced_functions

(* Get or overwrite the code pointer of a closure *)

soit get_code_pointer cls = Obj.field cls 0

soit set_code_pointer cls ptr = Obj.set_field cls 0 ptr

(* Call a traced function (use old code pointer, but new closure as
   environment so that recursive calls are also traced).
   It is necessary to wrap Meta.invoke_traced_function in an ML function
   so that the RETURN at the end of the ML wrapper takes us to the
   code of the function. *)

soit invoke_traced_function codeptr env arg =
  Meta.invoke_traced_function codeptr env arg

soit print_label ppf l = si l <> "" alors fprintf ppf "%s:" l

(* If a function returns a functional value, wrap it into a trace code *)

soit rec instrument_result env name ppf clos_typ =
  filtre (Ctype.repr(Ctype.expand_head env clos_typ)).desc avec
  | Tarrow(l, t1, t2, _) ->
      soit starred_name =
        filtre name avec
        | Lident s -> Lident(s ^ "*")
        | Ldot(lid, s) -> Ldot(lid, s ^ "*")
        | Lapply(l1, l2) -> fatal_error "Trace.instrument_result" dans
      soit trace_res = instrument_result env starred_name ppf t2 dans
      (fonc clos_val ->
        Obj.repr (fonc arg ->
          si not !may_trace alors
            (Obj.magic clos_val : Obj.t -> Obj.t) arg
          sinon début
            may_trace := faux;
            essaie
              fprintf ppf "@[<2>%a <--@ %a%a@]@."
                Printtyp.longident starred_name
                print_label l
                (print_value !toplevel_env arg) t1;
              may_trace := vrai;
              soit res = (Obj.magic clos_val : Obj.t -> Obj.t) arg dans
              may_trace := faux;
              fprintf ppf "@[<2>%a -->@ %a@]@."
                Printtyp.longident starred_name
                (print_value !toplevel_env res) t2;
              may_trace := vrai;
              trace_res res
            avec exn ->
              may_trace := faux;
              fprintf ppf "@[<2>%a raises@ %a@]@."
                Printtyp.longident starred_name
                (print_value !toplevel_env (Obj.repr exn)) Predef.type_exn;
              may_trace := vrai;
              raise exn
          fin))
  | _ -> (fonc v -> v)

(* Same as instrument_result, but for a toplevel closure (modified in place) *)

soit instrument_closure env name ppf clos_typ =
  filtre (Ctype.repr(Ctype.expand_head env clos_typ)).desc avec
  | Tarrow(l, t1, t2, _) ->
      soit trace_res = instrument_result env name ppf t2 dans
      (fonc actual_code closure arg ->
        si not !may_trace alors début
          soit res = invoke_traced_function actual_code closure arg
          dans res (* do not remove let, prevents tail-call to invoke_traced_ *)
        fin sinon début
          may_trace := faux;
          essaie
            fprintf ppf "@[<2>%a <--@ %a%a@]@."
              Printtyp.longident name
              print_label l
              (print_value !toplevel_env arg) t1;
            may_trace := vrai;
            soit res = invoke_traced_function actual_code closure arg dans
            may_trace := faux;
            fprintf ppf "@[<2>%a -->@ %a@]@."
              Printtyp.longident name
              (print_value !toplevel_env res) t2;
            may_trace := vrai;
            trace_res res
          avec exn ->
            may_trace := faux;
            fprintf ppf "@[<2>%a raises@ %a@]@."
              Printtyp.longident name
              (print_value !toplevel_env (Obj.repr exn)) Predef.type_exn;
            may_trace := vrai;
            raise exn
        fin)
  | _ -> affirme faux

(* Given the address of a closure, find its tracing info *)

soit rec find_traced_closure clos = fonction
  | [] -> fatal_error "Trace.find_traced_closure"
  | f :: rem -> si f.closure == clos alors f sinon find_traced_closure clos rem

(* Trace the application of an (instrumented) closure to an argument *)

soit print_trace clos arg =
  soit f = find_traced_closure clos !traced_functions dans
  f.instrumented_fun f.actual_code clos arg
