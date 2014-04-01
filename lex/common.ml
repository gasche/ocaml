(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Luc Maranget, projet Moscova,                            *)
(*                         INRIA Rocquencourt                          *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Printf
ouvre Syntax
ouvre Lexgen


(* To copy the ML code fragments *)

type line_tracker = {
  file : string;
  oc : out_channel;
  ic : in_channel;
  modifiable cur_line : int;
};;

soit open_tracker file oc = {
  file = file;
  oc = oc;
  ic = open_in_bin file;
  cur_line = 1;
};;

soit close_tracker tr = close_in_noerr tr.ic;;

soit update_tracker tr =
  fprintf tr.oc "\n";
  flush tr.oc;
  soit cr_seen = ref faux dans
  essaie pendant_que vrai faire
    filtre input_char tr.ic avec
    | '\010' quand not !cr_seen -> tr.cur_line <- tr.cur_line + 1;
    | '\013' -> cr_seen := vrai; tr.cur_line <- tr.cur_line + 1;
    | _ -> cr_seen := faux;
  fait avec End_of_file ->
  fprintf tr.oc "# %d \"%s\"\n" (tr.cur_line+1) tr.file;
;;

soit copy_buffer = String.create 1024

soit copy_chars_unix ic oc start stop =
  soit n = ref (stop - start) dans
  pendant_que !n > 0 faire
    soit m = input ic copy_buffer 0 (min !n 1024) dans
    output oc copy_buffer 0 m;
    n := !n - m
  fait

soit copy_chars_win32 ic oc start stop =
  pour _i = start à stop - 1 faire
    soit c = input_char ic dans
    si c <> '\r' alors output_char oc c
  fait

soit copy_chars =
  filtre Sys.os_type avec
    "Win32" | "Cygwin" -> copy_chars_win32
  | _       -> copy_chars_unix

soit copy_chunk ic oc trl loc add_parens =
  si loc.start_pos < loc.end_pos || add_parens alors début
    fprintf oc "# %d \"%s\"\n" loc.start_line loc.loc_file;
    si add_parens alors début
      pour _i = 1 à loc.start_col - 1 faire output_char oc ' ' fait;
      output_char oc '(';
    fin sinon début
      pour _i = 1 à loc.start_col faire output_char oc ' ' fait;
    fin;
    seek_in ic loc.start_pos;
    copy_chars ic oc loc.start_pos loc.end_pos;
    si add_parens alors output_char oc ')';
    update_tracker trl;
  fin

(* Various memory actions *)

soit output_mem_access oc i = fprintf oc "lexbuf.Lexing.lex_mem.(%d)" i

soit output_memory_actions pref oc = fonction
  | []  -> ()
  | mvs ->
      output_string oc "(* " ;
  fprintf oc "L=%d " (List.length mvs) ;
  List.iter
    (fonc mv -> filtre mv avec
    | Copy (tgt, src) ->
        fprintf oc "[%d] <- [%d] ;" tgt src
    | Set tgt ->
        fprintf oc "[%d] <- p ; " tgt)
    mvs ;
  output_string oc " *)\n" ;
  List.iter
    (fonc mv -> filtre mv avec
    | Copy (tgt, src) ->
        fprintf oc
          "%s%a <- %a ;\n"
          pref output_mem_access tgt output_mem_access src
    | Set tgt ->
        fprintf oc "%s%a <- lexbuf.Lexing.lex_curr_pos ;\n"
          pref output_mem_access tgt)
    mvs

soit output_base_mem oc = fonction
  | Mem i -> output_mem_access oc i
  | Start -> fprintf oc "lexbuf.Lexing.lex_start_pos"
  | End   -> fprintf oc  "lexbuf.Lexing.lex_curr_pos"

soit output_tag_access oc = fonction
  | Sum (a,0) ->
      output_base_mem oc a
  | Sum (a,i) ->
      fprintf oc "(%a + %d)" output_base_mem a i

soit output_env ic oc tr env =
  soit pref = ref "let" dans
  filtre env avec
  | [] -> ()
  | _  ->
      (* Probably, we are better with variables sorted
         in apparition order *)
      soit env =
        List.sort
          (fonc ((_,p1),_) ((_,p2),_) ->
            Pervasives.compare p1.start_pos  p2.start_pos)
          env dans

      List.iter
        (fonc ((x,pos),v) ->
          fprintf oc "%s\n" !pref ;
          copy_chunk ic oc tr pos faux ;
          début filtre v avec
          | Ident_string (o,nstart,nend) ->
              fprintf oc
                "= Lexing.sub_lexeme%s lexbuf %a %a"
                (si o alors "_opt" sinon "")
                output_tag_access nstart output_tag_access nend
          | Ident_char (o,nstart) ->
              fprintf oc
                "= Lexing.sub_lexeme_char%s lexbuf %a"
                (si o alors "_opt" sinon "")
                output_tag_access nstart
          fin ;
          pref := "\nand")
        env ;
      fprintf oc " in\n"

(* Output the user arguments *)
soit output_args oc args =
  List.iter (fonc x -> (output_string oc x; output_char oc ' ')) args

soit output_refill_handler ic oc oci = fonction
  | None -> faux
  | Some location ->
    output_string oc "let __ocaml_lex_refill : \
                      (Lexing.lexbuf -> 'a) -> (Lexing.lexbuf -> 'a) =\n";
    copy_chunk ic oc oci location vrai;
    vrai

(* quiet flag *)
soit quiet_mode = ref faux;;
