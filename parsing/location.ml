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

ouvre Lexing

soit absname = ref faux
    (* This reference should be in Clflags, but it would create an additional
       dependency and make bootstrapping Camlp4 more difficult. *)

type t = { loc_start: position; loc_end: position; loc_ghost: bool };;

soit in_file name =
  soit loc = {
    pos_fname = name;
    pos_lnum = 1;
    pos_bol = 0;
    pos_cnum = -1;
  } dans
  { loc_start = loc; loc_end = loc; loc_ghost = vrai }
;;

soit none = in_file "_none_";;

soit curr lexbuf = {
  loc_start = lexbuf.lex_start_p;
  loc_end = lexbuf.lex_curr_p;
  loc_ghost = faux
};;

soit init lexbuf fname =
  lexbuf.lex_curr_p <- {
    pos_fname = fname;
    pos_lnum = 1;
    pos_bol = 0;
    pos_cnum = 0;
  }
;;

soit symbol_rloc () = {
  loc_start = Parsing.symbol_start_pos ();
  loc_end = Parsing.symbol_end_pos ();
  loc_ghost = faux;
};;

soit symbol_gloc () = {
  loc_start = Parsing.symbol_start_pos ();
  loc_end = Parsing.symbol_end_pos ();
  loc_ghost = vrai;
};;

soit rhs_loc n = {
  loc_start = Parsing.rhs_start_pos n;
  loc_end = Parsing.rhs_end_pos n;
  loc_ghost = faux;
};;

soit input_name = ref "_none_"
soit input_lexbuf = ref (None : lexbuf option)

(* Terminal info *)

soit status = ref Terminfo.Uninitialised

soit num_loc_lines = ref 0 (* number of lines already printed after input *)

(* Highlight the locations using standout mode. *)

soit highlight_terminfo ppf num_lines lb locs =
  Format.pp_print_flush ppf ();  (* avoid mixing Format and normal output *)
  (* Char 0 is at offset -lb.lex_abs_pos in lb.lex_buffer. *)
  soit pos0 = -lb.lex_abs_pos dans
  (* Do nothing if the buffer does not contain the whole phrase. *)
  si pos0 < 0 alors raise Exit;
  (* Count number of lines in phrase *)
  soit lines = ref !num_loc_lines dans
  pour i = pos0 à lb.lex_buffer_len - 1 faire
    si lb.lex_buffer.[i] = '\n' alors incr lines
  fait;
  (* If too many lines, give up *)
  si !lines >= num_lines - 2 alors raise Exit;
  (* Move cursor up that number of lines *)
  flush stdout; Terminfo.backup !lines;
  (* Print the input, switching to standout for the location *)
  soit bol = ref faux dans
  print_string "# ";
  pour pos = 0 à lb.lex_buffer_len - pos0 - 1 faire
    si !bol alors (print_string "  "; bol := faux);
    si List.exists (fonc loc -> pos = loc.loc_start.pos_cnum) locs alors
      Terminfo.standout vrai;
    si List.exists (fonc loc -> pos = loc.loc_end.pos_cnum) locs alors
      Terminfo.standout faux;
    soit c = lb.lex_buffer.[pos + pos0] dans
    print_char c;
    bol := (c = '\n')
  fait;
  (* Make sure standout mode is over *)
  Terminfo.standout faux;
  (* Position cursor back to original location *)
  Terminfo.resume !num_loc_lines;
  flush stdout

(* Highlight the location by printing it again. *)

soit highlight_dumb ppf lb loc =
  (* Char 0 is at offset -lb.lex_abs_pos in lb.lex_buffer. *)
  soit pos0 = -lb.lex_abs_pos dans
  (* Do nothing if the buffer does not contain the whole phrase. *)
  si pos0 < 0 alors raise Exit;
  soit end_pos = lb.lex_buffer_len - pos0 - 1 dans
  (* Determine line numbers for the start and end points *)
  soit line_start = ref 0 et line_end = ref 0 dans
  pour pos = 0 à end_pos faire
    si lb.lex_buffer.[pos + pos0] = '\n' alors début
      si loc.loc_start.pos_cnum > pos alors incr line_start;
      si loc.loc_end.pos_cnum   > pos alors incr line_end;
    fin
  fait;
  (* Print character location (useful for Emacs) *)
  Format.fprintf ppf "Lettres %i-%i:@."
                 loc.loc_start.pos_cnum loc.loc_end.pos_cnum;
  (* Print the input, underlining the location *)
  Format.pp_print_string ppf "  ";
  soit line = ref 0 dans
  soit pos_at_bol = ref 0 dans
  pour pos = 0 à end_pos faire
    filtre lb.lex_buffer.[pos + pos0] avec
    | '\n' ->
      si !line = !line_start && !line = !line_end alors début
        (* loc is on one line: underline location *)
        Format.fprintf ppf "@.  ";
        pour _i = !pos_at_bol à loc.loc_start.pos_cnum - 1 faire
          Format.pp_print_char ppf ' '
        fait;
        pour _i = loc.loc_start.pos_cnum à loc.loc_end.pos_cnum - 1 faire
          Format.pp_print_char ppf '^'
        fait
      fin;
      si !line >= !line_start && !line <= !line_end alors début
        Format.fprintf ppf "@.";
        si pos < loc.loc_end.pos_cnum alors Format.pp_print_string ppf "  "
      fin;
      incr line;
      pos_at_bol := pos + 1
    | '\r' -> () (* discard *)
    | c ->
      si !line = !line_start && !line = !line_end alors
        (* loc is on one line: print whole line *)
        Format.pp_print_char ppf c
      sinon si !line = !line_start alors
        (* first line of multiline loc:
           print a dot for each char before loc_start *)
        si pos < loc.loc_start.pos_cnum alors
          Format.pp_print_char ppf '.'
        sinon
          Format.pp_print_char ppf c
      sinon si !line = !line_end alors
        (* last line of multiline loc: print a dot for each char
           after loc_end, even whitespaces *)
        si pos < loc.loc_end.pos_cnum alors
          Format.pp_print_char ppf c
        sinon
          Format.pp_print_char ppf '.'
      sinon si !line > !line_start && !line < !line_end alors
        (* intermediate line of multiline loc: print whole line *)
        Format.pp_print_char ppf c
  fait

(* Highlight the location using one of the supported modes. *)

soit rec highlight_locations ppf locs =
  filtre !status avec
    Terminfo.Uninitialised ->
      status := Terminfo.setup stdout; highlight_locations ppf locs
  | Terminfo.Bad_term ->
      début filtre !input_lexbuf avec
        None -> faux
      | Some lb ->
          soit norepeat =
            essaie Sys.getenv "TERM" = "norepeat" avec Not_found -> faux dans
          si norepeat alors faux sinon
            soit loc1 = List.hd locs dans
            essaie highlight_dumb ppf lb loc1; vrai
            avec Exit -> faux
      fin
  | Terminfo.Good_term num_lines ->
      début filtre !input_lexbuf avec
        None -> faux
      | Some lb ->
          essaie highlight_terminfo ppf num_lines lb locs; vrai
          avec Exit -> faux
      fin

(* Print the location in some way or another *)

ouvre Format

soit absolute_path s = (* This function could go into Filename *)
  soit ouvre Filename dans
  soit s = si is_relative s alors concat (Sys.getcwd ()) s sinon s dans
  (* Now simplify . and .. components *)
  soit rec aux s =
    soit base = basename s dans
    soit dir = dirname s dans
    si dir = s alors dir
    sinon si base = current_dir_name alors aux dir
    sinon si base = parent_dir_name alors dirname (aux dir)
    sinon concat (aux dir) base
  dans
  aux s

soit show_filename file =
  si !absname alors absolute_path file sinon file

soit print_filename ppf file =
  Format.fprintf ppf "%s" (show_filename file)

soit reset () =
  num_loc_lines := 0

soit (msg_file, msg_line, msg_chars, msg_to, msg_colon) =
  ("Fichier \"", "\", ligne ", ", lettres ", "-", ":")

(* return file, line, char from the given position *)
soit get_pos_info pos =
  (pos.pos_fname, pos.pos_lnum, pos.pos_cnum - pos.pos_bol)
;;

soit print_loc ppf loc =
  soit (file, line, startchar) = get_pos_info loc.loc_start dans
  soit endchar = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar dans
  si file = "//toplevel//" alors début
    si highlight_locations ppf [loc] alors () sinon
      fprintf ppf "Lettres %i-%i"
              loc.loc_start.pos_cnum loc.loc_end.pos_cnum
  fin sinon début
    fprintf ppf "%s%a%s%i" msg_file print_filename file msg_line line;
    si startchar >= 0 alors
      fprintf ppf "%s%i%s%i" msg_chars startchar msg_to endchar
  fin
;;

soit print ppf loc =
  si loc.loc_start.pos_fname = "//toplevel//"
  && highlight_locations ppf [loc] alors ()
  sinon fprintf ppf "%a%s@." print_loc loc msg_colon
;;

soit print_error ppf loc =
  print ppf loc;
  fprintf ppf "Erreur: ";
;;

soit print_error_cur_file ppf = print_error ppf (in_file !input_name);;

soit print_warning loc ppf w =
  si Warnings.is_active w alors début
    soit printw ppf w =
      soit n = Warnings.print ppf w dans
      num_loc_lines := !num_loc_lines + n
    dans
    print ppf loc;
    fprintf ppf "Avertissement %a@." printw w;
    pp_print_flush ppf ();
    incr num_loc_lines;
  fin
;;

soit prerr_warning loc w = print_warning loc err_formatter w;;

soit echo_eof () =
  print_newline ();
  incr num_loc_lines

type 'a loc = {
  txt : 'a;
  loc : t;
}

soit mkloc txt loc = { txt ; loc }
soit mknoloc txt = mkloc txt none


type error =
  {
    loc: t;
    msg: string;
    sub: error list;
    if_highlight: string; (* alternative message if locations are highlighted *)
  }

soit errorf ?(loc = none) ?(sub = []) ?(if_highlight = "") =
  Printf.ksprintf (fonc msg -> {loc; msg; sub; if_highlight})

soit error ?(loc = none) ?(sub = []) ?(if_highlight = "") msg =
  {loc; msg; sub; if_highlight}

soit error_of_exn : (exn -> error option) list ref = ref []

soit register_error_of_exn f = error_of_exn := f :: !error_of_exn

soit error_of_exn exn =
  soit rec loop = fonction
    | [] -> None
    | f :: rest ->
        filtre f exn avec
        | Some _ tel r -> r
        | None -> loop rest
  dans
  loop !error_of_exn

soit rec report_error ppf ({loc; msg; sub; if_highlight} tel err) =
  soit highlighted =
    si if_highlight <> "" alors
      soit rec collect_locs locs {loc; sub; if_highlight; _} =
        List.fold_left collect_locs (loc :: locs) sub
      dans
      soit locs = collect_locs [] err dans
      highlight_locations ppf locs
    sinon
      faux
  dans
  si highlighted alors
    Format.pp_print_string ppf if_highlight
  sinon début
    print ppf loc;
    Format.pp_print_string ppf msg;
    List.iter (fonc err -> Format.fprintf ppf "@\n@[<2>%a@]" report_error err) sub
  fin

soit error_of_printer loc print x =
  soit buf = Buffer.create 64 dans
  soit ppf = Format.formatter_of_buffer buf dans
  pp_print_string ppf "Erreur: ";
  print ppf x;
  pp_print_flush ppf ();
  soit msg = Buffer.contents buf dans
  errorf ~loc "%s" msg

soit error_of_printer_file print x =
  error_of_printer (in_file !input_name) print x

soit () =
  register_error_of_exn
    (fonction
      | Sys_error msg ->
          Some (errorf ~loc:(in_file !input_name) "Erreur: erreur E/S: %s" msg)
      | Warnings.Errors n ->
          Some
            (errorf ~loc:(in_file !input_name)
               "Erreur: des avertissements mortels ont retenti (%d fois)" n)
      | _ ->
          None
    )


soit report_exception ppf exn =
  filtre error_of_exn exn avec
  | Some err -> fprintf ppf "@[%a@]@." report_error err
  | None -> raise exn
