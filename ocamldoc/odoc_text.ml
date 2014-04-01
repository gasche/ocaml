(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

exception Text_syntax de int * int * string (* line, char, string *)

ouvre Odoc_types

module Texter =
  struct
    (* builds a text structure from a string. *)
    soit text_of_string s =
      soit lexbuf = Lexing.from_string s dans
      essaie
        Odoc_text_lexer.init ();
        Odoc_text_parser.main Odoc_text_lexer.main lexbuf
      avec
        _ ->
          raise (Text_syntax (!Odoc_text_lexer.line_number,
                              !Odoc_text_lexer.char_number,
                              s)
                )

    soit count s c =
      soit count = ref 0 dans
      pour i = 0 à String.length s - 1 faire
        si s.[i] = c alors incr count
      fait;
      !count

    soit escape_n s c n =
      soit remain = ref n dans
      soit len = String.length s dans
      soit b = Buffer.create (len + n) dans
      pour i = 0 à len - 1 faire
        si s.[i] = c && !remain > 0 alors
          (
           Printf.bprintf b "\\%c" c;
           decr remain
          )
        sinon
          Buffer.add_char b s.[i]
      fait;
      Buffer.contents b

    soit escape_code s =
      soit open_brackets = count s '[' dans
      soit close_brackets = count s ']' dans
      si open_brackets > close_brackets alors
        escape_n s '[' (open_brackets - close_brackets)
      sinon
        si close_brackets > open_brackets alors
          escape_n s ']' (close_brackets - open_brackets)
        sinon
          s

    soit escape_raw s =
      soit len = String.length s dans
      soit b = Buffer.create len dans
      pour i = 0 à len - 1 faire
        filtre s.[i] avec
          '[' | ']' | '{' | '}' ->
            Printf.bprintf b "\\%c" s.[i]
        | c ->
            Buffer.add_char b c
      fait;
      Buffer.contents b

    soit p = Printf.bprintf

    soit rec p_text b t =
      List.iter (p_text_element b) t

    et p_list b l =
      List.iter
        (fonc t -> p b "{- " ; p_text b t ; p b "}\n")
        l

    et p_text_element b = fonction
      | Raw s -> p b "%s" (escape_raw s)
      | Code s -> p b "[%s]" (escape_code s)
      | CodePre s -> p b "{[%s]}" s
      | Verbatim s -> p b "{v %s v}" s
      | Bold t -> p b "{b " ; p_text b t ; p b "}"
      | Italic t -> p b "{i " ; p_text b t ; p b "}"
      | Emphasize t -> p b "{e " ; p_text b t ; p b "}"
      | Center t -> p b "{C " ; p_text b t ; p b "}"
      | Left t -> p b "{L " ; p_text b t ; p b "}"
      | Right t -> p b "{R " ; p_text b t ; p b "}"
      | List l -> p b "{ul\n"; p_list b l; p b "}"
      | Enum l -> p b "{ol\n"; p_list b l; p b "}"
      | Newline -> p b "\n"
      | Block  t -> p_text b t
      | Title (n, l_opt, t) ->
          p b "{%d%s "
            n
            (filtre l_opt avec
              None -> ""
            | Some s -> ":"^s
            );
          p_text b t ;
          p b "}"
      | Latex s -> p b "{%% %s%%}" s
      | Link (s,t) ->
          p b "{{:%s}" s;
          p_text b t ;
          p b "}"
      | Ref (name, kind_opt, text_opt) ->
        début
          p b "%s{!%s%s}"
            (filtre text_opt avec None -> "" | Some _ -> "{")
            (filtre kind_opt avec
               None -> ""
             | Some k ->
                 soit s =
                   filtre k avec
                     RK_module -> "module"
                   | RK_module_type -> "modtype"
                   | RK_class -> "class"
                   | RK_class_type -> "classtype"
                   | RK_value -> "val"
                   | RK_type -> "type"
                   | RK_exception -> "exception"
                   | RK_attribute -> "attribute"
                   | RK_method -> "method"
                   | RK_section _ -> "section"
                   | RK_recfield -> "recfield"
                   | RK_const -> "const"
                 dans
                 s^":"
            )
            name;
          filtre text_opt avec
            None -> ()
          | Some t -> p_text b t; p b "}"
        fin
      | Superscript t -> p b "{^" ; p_text b t ; p b "}"
      | Subscript t -> p b "{_" ; p_text b t ; p b "}"
      | Module_list l ->
          p b "{!modules:";
          List.iter (fonc s -> p b " %s" s) l;
          p b "}"
      | Index_list ->
          p b "{!indexlist}"
      | Custom (s,t) ->
          p b "{%s " s;
          p_text b t;
          p b "}"
      | Target (target, code) ->
          p b "{%%%s: %s}" target (escape_raw code)

    soit string_of_text s =
      soit b = Buffer.create 256 dans
      p_text b s;
      Buffer.contents b

  fin
