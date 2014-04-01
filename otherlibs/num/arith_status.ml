(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*    Valerie Menissier-Morain, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

ouvre Arith_flags;;

soit get_error_when_null_denominator () =
  !error_when_null_denominator_flag
et set_error_when_null_denominator choice =
 error_when_null_denominator_flag := choice;;

soit get_normalize_ratio () = !normalize_ratio_flag
et set_normalize_ratio choice = normalize_ratio_flag := choice;;

soit get_normalize_ratio_when_printing () =
  !normalize_ratio_when_printing_flag
et set_normalize_ratio_when_printing choice =
 normalize_ratio_when_printing_flag := choice;;

soit get_floating_precision () = !floating_precision
et set_floating_precision i = floating_precision := i;;

soit get_approx_printing () = !approx_printing_flag
et set_approx_printing b = approx_printing_flag := b;;

soit arith_print_string s = print_string s; print_string " --> ";;

soit arith_print_bool = fonction
  vrai -> print_string "ON"
| _ -> print_string "OFF"
;;

soit arith_status () =
  print_newline ();

  arith_print_string
  "Normalization during computation";
  arith_print_bool (get_normalize_ratio ());
  print_newline ();
  print_string "     (returned by get_normalize_ratio ())";
  print_newline ();
  print_string "     (modifiable with set_normalize_ratio <your choice>)";
  print_newline ();
  print_newline ();

  arith_print_string
  "Normalization when printing";
  arith_print_bool (get_normalize_ratio_when_printing ());
  print_newline ();
  print_string
  "     (returned by get_normalize_ratio_when_printing ())";
  print_newline ();
  print_string
  "     (modifiable with set_normalize_ratio_when_printing <your choice>)";
  print_newline ();
  print_newline ();

  arith_print_string
  "Floating point approximation when printing rational numbers";
  arith_print_bool (get_approx_printing ());
  print_newline ();
  print_string
  "     (returned by get_approx_printing ())";
  print_newline ();
  print_string
  "     (modifiable with set_approx_printing <your choice>)";
  print_newline ();
  (si (get_approx_printing ())
      alors (print_string "  Default precision = ";
            print_int (get_floating_precision ());
            print_newline ();
            print_string "     (returned by get_floating_precision ())";
            print_newline ();
            print_string
              "     (modifiable with set_floating_precision <your choice>)";
            print_newline ();
            print_newline ())
      sinon print_newline());

  arith_print_string
  "Error when a rational denominator is null";
  arith_print_bool (get_error_when_null_denominator ());
  print_newline ();
  print_string "     (returned by get_error_when_null_denominator ())";
  print_newline ();
  print_string
  "     (modifiable with set_error_when_null_denominator <your choice>)";
  print_newline ()
;;
