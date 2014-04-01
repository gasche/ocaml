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

(** Analysis of comments. *)

ouvre Odoc_types

soit print_DEBUG s = print_string s ; print_newline ();;

(** This variable contains the regular expression representing a blank but not a '\n'.*)
soit simple_blank = "[ \013\009\012]"

module type Texter =
    sig
      (** Return a text structure from a string. *)
      val text_of_string : string -> text
    fin

module Info_retriever =
  foncteur (MyTexter : Texter) ->
  struct
    soit create_see s =
      essaie
        soit lexbuf = Lexing.from_string s dans
        soit (see_ref, s) = Odoc_parser.see_info Odoc_see_lexer.main lexbuf dans
        (see_ref, MyTexter.text_of_string s)
      avec
      | Odoc_text.Text_syntax (l, c, s) ->
          raise (Failure (Odoc_messages.text_parse_error l c s))
      | _ ->
          raise (Failure ("Unknown error while parsing @see tag: "^s))

    soit retrieve_info fun_lex file (s : string) =
      essaie
        soit _ = Odoc_comments_global.init () dans
        Odoc_lexer.comments_level := 0;
        soit lexbuf = Lexing.from_string s dans
        filtre Odoc_parser.main fun_lex lexbuf avec
          None ->
            (0, None)
        | Some (desc, remain_opt) ->
            soit mem_nb_chars = !Odoc_comments_global.nb_chars dans
            soit _ =
              filtre remain_opt avec
                None ->
                  ()
              | Some s ->
                  (*DEBUG*)print_string ("remain: "^s); print_newline();
                  soit lexbuf2 = Lexing.from_string s dans
                  Odoc_parser.info_part2 Odoc_lexer.elements lexbuf2
            dans
            (mem_nb_chars,
             Some
               {
                 i_desc = (filtre desc avec "" -> None | _ -> Some (MyTexter.text_of_string desc));
                 i_authors = !Odoc_comments_global.authors;
                 i_version = !Odoc_comments_global.version;
                 i_sees = (List.map create_see !Odoc_comments_global.sees) ;
                 i_since = !Odoc_comments_global.since;
                 i_before = Odoc_merge.merge_before_tags
                     (List.map (fonc (n, s) ->
                         (n, MyTexter.text_of_string s)) !Odoc_comments_global.before)
                   ;
                 i_deprecated =
                 (filtre !Odoc_comments_global.deprecated avec
                   None -> None | Some s -> Some (MyTexter.text_of_string s));
                 i_params =
                 (List.map (fonc (n, s) ->
                   (n, MyTexter.text_of_string s)) !Odoc_comments_global.params);
                 i_raised_exceptions =
                 (List.map (fonc (n, s) ->
                   (n, MyTexter.text_of_string s)) !Odoc_comments_global.raised_exceptions);
                 i_return_value =
                 (filtre !Odoc_comments_global.return_value avec
                   None -> None | Some s -> Some (MyTexter.text_of_string s)) ;
                 i_custom = (List.map
                               (fonc (tag, s) -> (tag, MyTexter.text_of_string s))
                               !Odoc_comments_global.customs)
               }
            )
               avec
                 Failure s ->
                   incr Odoc_global.errors ;
                    Printf.eprintf "File %S, line %d:\n%s\n%!" file (!Odoc_lexer.line_number + 1) s;
                   (0, None)
               | Odoc_text.Text_syntax (l, c, s) ->
                   incr Odoc_global.errors ;
                   prerr_endline (file^" : "^(Odoc_messages.text_parse_error l c s));
                   (0, None)
               | _ ->
                   incr Odoc_global.errors ;
                   prerr_endline (file^" : "^Odoc_messages.parse_error^"\n");
                   (0, None)

    (** This function takes a string where a simple comment may has been found. It returns
       false if there is a blank line or the first comment is a special one, or if there is
       no comment if the string.*)
    soit nothing_before_simple_comment s =
      (* get the position of the first "(*" *)
      essaie
        print_DEBUG ("comment_is_attached: "^s);
        soit pos = Str.search_forward (Str.regexp "(\\*") s 0 dans
        soit next_char = si (String.length s) >= (pos + 1) alors s.[pos + 2] sinon '_' dans
        (next_char <> '*') &&
        (
         (* there is no special comment between the constructor and the coment we got *)
         soit s2 = String.sub s 0 pos dans
         print_DEBUG ("s2="^s2);
         essaie
           soit _ = Str.search_forward (Str.regexp ("['\n']"^simple_blank^"*['\n']")) s2 0 dans
           (* a blank line was before the comment *)
           faux
         avec
           Not_found ->
             vrai
        )
      avec
        Not_found ->
          faux

    (** Return true if the given string contains a blank line. *)
    soit blank_line s =
      essaie
        soit _ = Str.search_forward (Str.regexp ("['\n']"^simple_blank^"*['\n']")) s 0 dans
        (* a blank line was before the comment *)
        vrai
      avec
        Not_found ->
          faux

    soit retrieve_info_special file (s : string) =
      retrieve_info Odoc_lexer.main file s

    soit retrieve_info_simple file (s : string) =
      soit _ = Odoc_comments_global.init () dans
      Odoc_lexer.comments_level := 0;
      soit lexbuf = Lexing.from_string s dans
      filtre Odoc_parser.main Odoc_lexer.simple lexbuf avec
        None ->
          (0, None)
      | Some (desc, remain_opt) ->
          (!Odoc_comments_global.nb_chars, Some Odoc_types.dummy_info)

    (** Return true if the given string contains a blank line outside a simple comment. *)
    soit blank_line_outside_simple file s =
      soit rec iter s2 =
        filtre retrieve_info_simple file s2 avec
          (_, None) ->
            blank_line s2
        | (len, Some _) ->
            essaie
              soit pos = Str.search_forward (Str.regexp_string "(*") s2 0 dans
              soit s_before = String.sub s2 0 pos dans
              soit s_after = String.sub s2 len ((String.length s2) - len) dans
              (blank_line s_before) || (iter s_after)
            avec
              Not_found ->
                (* we shouldn't get here *)
                faux
      dans
      iter s

    (** This function returns the first simple comment in
       the given string. If strict is [true] then no
       comment is returned if a blank line or a special
       comment is found before the simple comment. *)
    soit retrieve_first_info_simple ?(strict=vrai) file (s : string) =
      filtre retrieve_info_simple file s avec
        (_, None) ->
          (0, None)
      | (len, Some d) ->
          (* we check if the comment we got was really attached to the constructor,
             i.e. that there was no blank line or any special comment "(**" before *)
          si (not strict) || (nothing_before_simple_comment s) alors
            (* ok, we attach the comment to the constructor *)
            (len, Some d)
          sinon
            (* a blank line or special comment was before the comment,
               so we must not attach this comment to the constructor. *)
            (0, None)

    soit retrieve_last_info_simple file (s : string) =
      print_DEBUG ("retrieve_last_info_simple:"^s);
      soit rec f cur_len cur_d =
        essaie
          soit s2 = String.sub s cur_len ((String.length s) - cur_len) dans
          print_DEBUG ("retrieve_last_info_simple.f:"^s2);
          filtre retrieve_info_simple file s2 avec
            (len, None) ->
              print_DEBUG "retrieve_last_info_simple: None";
              (cur_len + len, cur_d)
          | (len, Some d) ->
              print_DEBUG "retrieve_last_info_simple: Some";
              f (len + cur_len) (Some d)
        avec
          _ ->
            print_DEBUG "retrieve_last_info_simple : Erreur String.sub";
            (cur_len, cur_d)
      dans
      f 0 None

    soit retrieve_last_special_no_blank_after file (s : string) =
      print_DEBUG ("retrieve_last_special_no_blank_after:"^s);
      soit rec f cur_len cur_d =
        essaie
          soit s2 = String.sub s cur_len ((String.length s) - cur_len) dans
          print_DEBUG ("retrieve_last_special_no_blank_after.f:"^s2);
          filtre retrieve_info_special file s2 avec
            (len, None) ->
              print_DEBUG "retrieve_last_special_no_blank_after: None";
              (cur_len + len, cur_d)
          | (len, Some d) ->
              print_DEBUG "retrieve_last_special_no_blank_after: Some";
              f (len + cur_len) (Some d)
        avec
          _ ->
            print_DEBUG "retrieve_last_special_no_blank_after : Erreur String.sub";
            (cur_len, cur_d)
      dans
      f 0 None

    soit all_special file s =
      print_DEBUG ("all_special: "^s);
      soit rec iter acc n s2 =
        filtre retrieve_info_special file s2 avec
          (_, None) ->
            (n, acc)
        | (n2, Some i) ->
            print_DEBUG ("all_special: avant String.sub new_s="^s2);
            print_DEBUG ("n2="^(string_of_int n2)) ;
            print_DEBUG ("len(s2)="^(string_of_int (String.length s2))) ;
            soit new_s = String.sub s2 n2 ((String.length s2) - n2) dans
            print_DEBUG ("all_special: apres String.sub new_s="^new_s);
            iter (acc @ [i]) (n + n2) new_s
      dans
      soit res = iter [] 0 s dans
      print_DEBUG ("all_special: end");
      res

    soit just_after_special file s =
      print_DEBUG ("just_after_special: "^s);
      soit res = filtre retrieve_info_special file s avec
        (_, None) ->
          (0, None)
      | (len, Some d) ->
          (* we must not have a simple comment or a blank line before. *)
          filtre retrieve_info_simple file (String.sub s 0 len) avec
            (_, None) ->
              (
               essaie
                 (* if the special comment is the stop comment (**/**),
                    then we must not associate it. *)
                 soit pos = Str.search_forward (Str.regexp_string "(**") s 0 dans
                 si blank_line (String.sub s 0 pos) ||
                   d.Odoc_types.i_desc = Some [Odoc_types.Raw "/*"]
                 alors
                   (0, None)
                 sinon
                   (len, Some d)
               avec
                 Not_found ->
                   (* should not occur *)
                   (0, None)
              )
          | (len2, Some d2) ->
              (0, None)
      dans
      print_DEBUG ("just_after_special:end");
      res

    soit first_special file s =
      retrieve_info_special file s

    soit get_comments f_create_ele file s =
      soit (assoc_com, ele_coms) =
        (* get the comments *)
        soit (len, special_coms) =  all_special file s dans
        (* if there is no blank line after the special comments, and
           if the last special comment is not the stop special comment, then the
           last special comments must be associated to the element. *)
        filtre List.rev special_coms avec
          [] ->
            (None, [])
        |  h :: q ->
            si (blank_line_outside_simple file
                  (String.sub s len ((String.length s) - len)) )
                || h.Odoc_types.i_desc = Some [Odoc_types.Raw "/*"]
            alors
              (None, special_coms)
            sinon
              (Some h, List.rev q)
      dans
      soit ele_comments =
        List.fold_left
          (fonc acc -> fonc sc ->
            filtre sc.Odoc_types.i_desc avec
              None ->
                acc
            | Some t ->
                acc @ [f_create_ele t])
          []
          ele_coms
      dans
      (assoc_com, ele_comments)
  fin

module Basic_info_retriever = Info_retriever (Odoc_text.Texter)

soit info_of_string s =
  soit dummy =
    {
      i_desc = None ;
      i_authors = [] ;
      i_version = None ;
      i_sees = [] ;
      i_since = None ;
      i_before = [] ;
      i_deprecated = None ;
      i_params = [] ;
      i_raised_exceptions = [] ;
      i_return_value = None ;
      i_custom = [] ;
    }
  dans
  soit s2 = Printf.sprintf "(** %s *)" s dans
  soit (_, i_opt) = Basic_info_retriever.first_special "-" s2 dans
  filtre i_opt avec
    None -> dummy
  | Some i -> i

soit info_of_comment_file modlist f =
  essaie
    soit s = Odoc_misc.input_file_as_string f dans
    soit i = info_of_string s dans
    Odoc_cross.assoc_comments_info "" modlist i
  avec
    Sys_error s ->
      failwith s
