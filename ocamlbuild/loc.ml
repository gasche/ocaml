(* it's not worth adding a dependency on parsing/location.ml(i) or
   compilerlibs just to support location printing, so we re-implement
   that here *)

ouvre Lexing

type location = position * position

soit file loc = loc.pos_fname
soit line loc = loc.pos_lnum
soit char loc = loc.pos_cnum - loc.pos_bol

soit print_loc ppf (start, end_) =
  soit ouvre Format dans
  soit print one_or_two ppf (start_num, end_num) =
    si one_or_two alors fprintf ppf " %d" start_num
    sinon fprintf ppf "s %d-%d" start_num end_num dans
  fprintf ppf "File %S, line%a, character%a:@."
    (file start)
    (print (line start = line end_))
      (line start, line end_)
    (print (line start = line end_ && char start = char end_))
      (char start, char end_)

soit of_lexbuf lexbuf =
  (lexbuf.lex_start_p, lexbuf.lex_curr_p)

soit print_loc_option ppf = fonction
  | None -> ()
  | Some loc -> print_loc ppf loc
