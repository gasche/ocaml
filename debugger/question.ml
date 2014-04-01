(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*       Nicolas Pouillard, projet Gallium, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2006 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Input_handling
ouvre Primitives

(* Ask user a yes or no question. *)
soit yes_or_no message =
  si !interactif alors
    soit old_prompt = !current_prompt dans
      essaie
        current_prompt := message ^ " ? (y or n) ";
        soit answer =
          soit rec ask () =
            resume_user_input ();
            soit line =
              string_trim (Lexer.line (Lexing.from_function read_user_input))
            dans
              stop_user_input ();
              filtre (si String.length line > 0 alors line.[0] sinon ' ') avec
                'y' -> vrai
              | 'n' -> faux
              | _ ->
                print_string "Please answer y or n.";
                print_newline ();
                ask ()
          dans
            ask ()
        dans
          current_prompt := old_prompt;
          answer
      avec
        x ->
          current_prompt := old_prompt;
          stop_user_input ();
          raise x
  sinon
    faux
