(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Damien Doligez, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2003 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Recording and dumping (partial) type information *)

(*
  We record all types in a list as they are created.
  This means we can dump type information even if type inference fails,
  which is extremely important, since type information is most
  interesting in case of errors.
*)

ouvre Annot;;
ouvre Lexing;;
ouvre Location;;
ouvre Typedtree;;

soit output_int oc i = output_string oc (string_of_int i)

type annotation =
  | Ti_pat   de pattern
  | Ti_expr  de expression
  | Ti_class de class_expr
  | Ti_mod   de module_expr
  | An_call de Location.t * Annot.call
  | An_ident de Location.t * string * Annot.ident
;;

soit get_location ti =
  filtre ti avec
    Ti_pat p   -> p.pat_loc
  | Ti_expr e  -> e.exp_loc
  | Ti_class c -> c.cl_loc
  | Ti_mod m   -> m.mod_loc
  | An_call (l, k) -> l
  | An_ident (l, s, k) -> l
;;

soit annotations = ref ([] : annotation list);;
soit phrases = ref ([] : Location.t list);;

soit record ti =
  si !Clflags.annotations && not (get_location ti).Location.loc_ghost alors
    annotations := ti :: !annotations
;;

soit record_phrase loc =
  si !Clflags.annotations alors phrases := loc :: !phrases;
;;

(* comparison order:
   the intervals are sorted by order of increasing upper bound
   same upper bound -> sorted by decreasing lower bound
*)
soit cmp_loc_inner_first loc1 loc2 =
  filtre compare loc1.loc_end.pos_cnum loc2.loc_end.pos_cnum avec
  | 0 -> compare loc2.loc_start.pos_cnum loc1.loc_start.pos_cnum
  | x -> x
;;
soit cmp_ti_inner_first ti1 ti2 =
  cmp_loc_inner_first (get_location ti1) (get_location ti2)
;;

soit print_position pp pos =
  si pos = dummy_pos alors
    output_string pp "--"
  sinon début
    output_char pp '\"';
    output_string pp (String.escaped pos.pos_fname);
    output_string pp "\" ";
    output_int pp pos.pos_lnum;
    output_char pp ' ';
    output_int pp pos.pos_bol;
    output_char pp ' ';
    output_int pp pos.pos_cnum;
  fin
;;

soit print_location pp loc =
  print_position pp loc.loc_start;
  output_char pp ' ';
  print_position pp loc.loc_end;
;;

soit sort_filter_phrases () =
  soit ph = List.sort (fonc x y -> cmp_loc_inner_first y x) !phrases dans
  soit rec loop accu cur l =
    filtre l avec
    | [] -> accu
    | loc :: t ->
       si cur.loc_start.pos_cnum <= loc.loc_start.pos_cnum
          && cur.loc_end.pos_cnum >= loc.loc_end.pos_cnum
       alors loop accu cur t
       sinon loop (loc :: accu) loc t
  dans
  phrases := loop [] Location.none ph;
;;

soit rec printtyp_reset_maybe loc =
  filtre !phrases avec
  | cur :: t quand cur.loc_start.pos_cnum <= loc.loc_start.pos_cnum ->
     Printtyp.reset ();
     phrases := t;
     printtyp_reset_maybe loc;
  | _ -> ()
;;

soit call_kind_string k =
  filtre k avec
  | Tail -> "tail"
  | Stack -> "stack"
  | Inline -> "inline"
;;

soit print_ident_annot pp str k =
  filtre k avec
  | Idef l ->
      output_string pp "def ";
      output_string pp str;
      output_char pp ' ';
      print_location pp l;
      output_char pp '\n'
  | Iref_internal l ->
      output_string pp "int_ref ";
      output_string pp str;
      output_char pp ' ';
      print_location pp l;
      output_char pp '\n'
  | Iref_external ->
      output_string pp "ext_ref ";
      output_string pp str;
      output_char pp '\n'
;;

(* The format of the annotation file is documented in emacs/caml-types.el. *)

soit print_info pp prev_loc ti =
  filtre ti avec
  | Ti_class _ | Ti_mod _ -> prev_loc
  | Ti_pat  {pat_loc = loc; pat_type = typ; pat_env = env}
  | Ti_expr {exp_loc = loc; exp_type = typ; exp_env = env} ->
      si loc <> prev_loc alors début
        print_location pp loc;
        output_char pp '\n'
      fin;
      output_string pp "type(\n";
      printtyp_reset_maybe loc;
      Printtyp.mark_loops typ;
      Format.pp_print_string Format.str_formatter "  ";
      Printtyp.wrap_printing_env env
                       (fonc () -> Printtyp.type_sch Format.str_formatter typ);
      Format.pp_print_newline Format.str_formatter ();
      soit s = Format.flush_str_formatter () dans
      output_string pp s;
      output_string pp ")\n";
      loc
  | An_call (loc, k) ->
      si loc <> prev_loc alors début
        print_location pp loc;
        output_char pp '\n'
      fin;
      output_string pp "call(\n  ";
      output_string pp (call_kind_string k);
      output_string pp "\n)\n";
      loc
  | An_ident (loc, str, k) ->
      si loc <> prev_loc alors début
        print_location pp loc;
        output_char pp '\n'
      fin;
      output_string pp "ident(\n  ";
      print_ident_annot pp str k;
      output_string pp ")\n";
      loc
;;

soit get_info () =
  soit info = List.fast_sort cmp_ti_inner_first !annotations dans
  annotations := [];
  info
;;

soit dump filename =
  si !Clflags.annotations alors début
    soit info = get_info () dans
    soit pp =
      filtre filename avec
          None -> stdout
        | Some filename -> open_out filename dans
    sort_filter_phrases ();
    ignore (List.fold_left (print_info pp) Location.none info);
    phrases := [];
  fin sinon début
    annotations := [];
  fin;
;;
