(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Pierre Weis, projet Cristal, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* A pretty-printing facility and definition of formatters for 'parallel'
   (i.e. unrelated or independent) pretty-printing on multiple out channels. *)

(**************************************************************

  Data structures definitions.

 **************************************************************)

type size;;

dehors size_of_int : int -> size = "%identity"
;;
dehors int_of_size : size -> int = "%identity"
;;

(* Tokens are one of the following : *)

type pp_token =
| Pp_text de string            (* normal text *)
| Pp_break de int * int        (* complete break *)
| Pp_tbreak de int * int       (* go to next tabulation *)
| Pp_stab                      (* set a tabulation *)
| Pp_begin de int * block_type (* beginning of a block *)
| Pp_end                       (* end of a block *)
| Pp_tbegin de tblock          (* beginning of a tabulation block *)
| Pp_tend                      (* end of a tabulation block *)
| Pp_newline                   (* to force a newline inside a block *)
| Pp_if_newline                (* to do something only if this very
                                  line has been broken *)
| Pp_open_tag de tag           (* opening a tag name *)
| Pp_close_tag                 (* closing the most recently opened tag *)

et tag = string

et block_type =
| Pp_hbox   (* Horizontal block no line breaking *)
| Pp_vbox   (* Vertical block each break leads to a new line *)
| Pp_hvbox  (* Horizontal-vertical block: same as vbox, except if this block
               is small enough to fit on a single line *)
| Pp_hovbox (* Horizontal or Vertical block: breaks lead to new line
               only when necessary to print the content of the block *)
| Pp_box    (* Horizontal or Indent block: breaks lead to new line
               only when necessary to print the content of the block, or
               when it leads to a new indentation of the current line *)
| Pp_fits   (* Internal usage: when a block fits on a single line *)

et tblock =
  | Pp_tbox de int list ref  (* Tabulation box *)
;;

(* The Queue:
   contains all formatting elements.
   elements are tuples (size, token, length), where
   size is set when the size of the block is known
   len is the declared length of the token. *)
type pp_queue_elem = {
  modifiable elem_size : size;
  token : pp_token;
  length : int;
}
;;

(* Scan stack:
   each element is (left_total, queue element) where left_total
   is the value of pp_left_total when the element has been enqueued. *)
type pp_scan_elem = Scan_elem de int * pp_queue_elem;;

(* Formatting stack:
   used to break the lines while printing tokens.
   The formatting stack contains the description of
   the currently active blocks. *)
type pp_format_elem = Format_elem de block_type * int;;

(* General purpose queues, used in the formatter. *)
type 'a queue_elem =
   | Nil
   | Cons de 'a queue_cell

et 'a queue_cell = {
  modifiable head : 'a;
  modifiable tail : 'a queue_elem;
}
;;

type 'a queue = {
  modifiable insert : 'a queue_elem;
  modifiable body : 'a queue_elem;
}
;;

(* The formatter specific tag handling functions. *)
type formatter_tag_functions = {
  mark_open_tag : tag -> string;
  mark_close_tag : tag -> string;
  print_open_tag : tag -> unit;
  print_close_tag : tag -> unit;
}
;;

(* A formatter with all its machinery. *)
type formatter = {
  modifiable pp_scan_stack : pp_scan_elem list;
  modifiable pp_format_stack : pp_format_elem list;
  modifiable pp_tbox_stack : tblock list;
  modifiable pp_tag_stack : tag list;
  modifiable pp_mark_stack : tag list;
  (* Global variables: default initialization is
     set_margin 78
     set_min_space_left 0. *)
  (* Value of right margin. *)
  modifiable pp_margin : int;
  (* Minimal space left before margin, when opening a block. *)
  modifiable pp_min_space_left : int;
  (* Maximum value of indentation:
     no blocks can be opened further. *)
  modifiable pp_max_indent : int;
  (* Space remaining on the current line. *)
  modifiable pp_space_left : int;
  (* Current value of indentation. *)
  modifiable pp_current_indent : int;
  (* True when the line has been broken by the pretty-printer. *)
  modifiable pp_is_new_line : bool;
  (* Total width of tokens already printed. *)
  modifiable pp_left_total : int;
  (* Total width of tokens ever put in queue. *)
  modifiable pp_right_total : int;
  (* Current number of opened blocks. *)
  modifiable pp_curr_depth : int;
  (* Maximum number of blocks which can be simultaneously opened. *)
  modifiable pp_max_boxes : int;
  (* Ellipsis string. *)
  modifiable pp_ellipsis : string;
  (* Output function. *)
  modifiable pp_out_string : string -> int -> int -> unit;
  (* Flushing function. *)
  modifiable pp_out_flush : unit -> unit;
  (* Output of new lines. *)
  modifiable pp_out_newline : unit -> unit;
  (* Output of indentation spaces. *)
  modifiable pp_out_spaces : int -> unit;
  (* Are tags printed ? *)
  modifiable pp_print_tags : bool;
  (* Are tags marked ? *)
  modifiable pp_mark_tags : bool;
  (* Find opening and closing markers of tags. *)
  modifiable pp_mark_open_tag : tag -> string;
  modifiable pp_mark_close_tag : tag -> string;
  modifiable pp_print_open_tag : tag -> unit;
  modifiable pp_print_close_tag : tag -> unit;
  (* The pretty-printer queue. *)
  modifiable pp_queue : pp_queue_elem queue;
}
;;

(**************************************************************

  Auxilliaries and basic functions.

 **************************************************************)


(* Queues auxilliaries. *)
soit make_queue () = { insert = Nil; body = Nil; };;

soit clear_queue q = q.insert <- Nil; q.body <- Nil;;

soit add_queue x q =
  soit c = Cons { head = x; tail = Nil; } dans
  filtre q avec
  | { insert = Cons cell; body = _; } ->
    q.insert <- c; cell.tail <- c
  (* Invariant: when insert is Nil body should be Nil. *)
  | { insert = Nil; body = _; } ->
    q.insert <- c; q.body <- c
;;

exception Empty_queue;;

soit peek_queue = fonction
  | { body = Cons { head = x; tail = _; }; _ } -> x
  | { body = Nil; insert = _; } -> raise Empty_queue
;;

soit take_queue = fonction
  | { body = Cons { head = x; tail = tl; }; _ } tel q ->
    q.body <- tl;
    si tl = Nil alors q.insert <- Nil; (* Maintain the invariant. *)
    x
  | { body = Nil; insert = _; } -> raise Empty_queue
;;

(* Enter a token in the pretty-printer queue. *)
soit pp_enqueue state ({ length = len; _} tel token) =
  state.pp_right_total <- state.pp_right_total + len;
  add_queue token state.pp_queue
;;

soit pp_clear_queue state =
  state.pp_left_total <- 1; state.pp_right_total <- 1;
  clear_queue state.pp_queue
;;

(* Pp_infinity: large value for default tokens size.

   Pp_infinity is documented as being greater than 1e10; to avoid
   confusion about the word 'greater', we choose pp_infinity greater
   than 1e10 + 1; for correct handling of tests in the algorithm,
   pp_infinity must be even one more than 1e10 + 1; let's stand on the
   safe side by choosing 1.e10+10.

   Pp_infinity could probably be 1073741823 that is 2^30 - 1, that is
   the minimal upper bound for integers; now that max_int is defined,
   this limit could also be defined as max_int - 1.

   However, before setting pp_infinity to something around max_int, we
   must carefully double-check all the integer arithmetic operations
   that involve pp_infinity, since any overflow would wreck havoc the
   pretty-printing algorithm's invariants. Given that this arithmetic
   correctness check is difficult and error prone and given that 1e10
   + 1 is in practice large enough, there is no need to attempt to set
   pp_infinity to the theoretically maximum limit. It is not worth the
   burden ! *)

soit pp_infinity = 1000000010;;

(* Output functions for the formatter. *)
soit pp_output_string state s = state.pp_out_string s 0 (String.length s)
et pp_output_newline state = state.pp_out_newline ()
et pp_output_spaces state n = state.pp_out_spaces n
;;

(* To format a break, indenting a new line. *)
soit break_new_line state offset width =
  pp_output_newline state;
  state.pp_is_new_line <- vrai;
  soit indent = state.pp_margin - width + offset dans
  (* Don't indent more than pp_max_indent. *)
  soit real_indent = min state.pp_max_indent indent dans
  state.pp_current_indent <- real_indent;
  state.pp_space_left <- state.pp_margin - state.pp_current_indent;
  pp_output_spaces state state.pp_current_indent
;;

(* To force a line break inside a block: no offset is added. *)
soit break_line state width = break_new_line state 0 width;;

(* To format a break that fits on the current line. *)
soit break_same_line state width =
  state.pp_space_left <- state.pp_space_left - width;
  pp_output_spaces state width
;;

(* To indent no more than pp_max_indent, if one tries to open a block
   beyond pp_max_indent, then the block is rejected on the left
   by simulating a break. *)
soit pp_force_break_line state =
  filtre state.pp_format_stack avec
  | Format_elem (bl_ty, width) :: _ ->
    si width > state.pp_space_left alors
      (filtre bl_ty avec
       | Pp_fits -> () | Pp_hbox -> ()
       | Pp_vbox | Pp_hvbox | Pp_hovbox | Pp_box ->
         break_line state width)
  | [] -> pp_output_newline state
;;

(* To skip a token, if the previous line has been broken. *)
soit pp_skip_token state =
  (* When calling pp_skip_token the queue cannot be empty. *)
  filtre take_queue state.pp_queue avec
  | { elem_size = size; length = len; token = _; } ->
    state.pp_left_total <- state.pp_left_total - len;
    state.pp_space_left <- state.pp_space_left + int_of_size size
;;

(**************************************************************

  The main pretty printing functions.

 **************************************************************)

(* To format a token. *)
soit format_pp_token state size = fonction

  | Pp_text s ->
    state.pp_space_left <- state.pp_space_left - size;
    pp_output_string state s;
    state.pp_is_new_line <- faux

  | Pp_begin (off, ty) ->
    soit insertion_point = state.pp_margin - state.pp_space_left dans
    si insertion_point > state.pp_max_indent alors
      (* can't open a block right there. *)
      début pp_force_break_line state fin;
    soit offset = state.pp_space_left - off dans
    soit bl_type =
      début filtre ty avec
      | Pp_vbox -> Pp_vbox
      | Pp_hbox | Pp_hvbox | Pp_hovbox | Pp_box | Pp_fits ->
        si size > state.pp_space_left alors ty sinon Pp_fits
      fin dans
    state.pp_format_stack <-
      Format_elem (bl_type, offset) :: state.pp_format_stack

  | Pp_end ->
    début filtre state.pp_format_stack avec
    | _ :: ls -> state.pp_format_stack <- ls
    | [] -> () (* No more block to close. *)
    fin

  | Pp_tbegin (Pp_tbox _ tel tbox) ->
    state.pp_tbox_stack <- tbox :: state.pp_tbox_stack

  | Pp_tend ->
    début filtre state.pp_tbox_stack avec
    | _ :: ls -> state.pp_tbox_stack <- ls
    | [] -> () (* No more tabulation block to close. *)
    fin

  | Pp_stab ->
    début filtre state.pp_tbox_stack avec
    | Pp_tbox tabs :: _ ->
      soit rec add_tab n = fonction
        | [] -> [n]
        | x :: l tel ls -> si n < x alors n :: ls sinon x :: add_tab n l dans
      tabs := add_tab (state.pp_margin - state.pp_space_left) !tabs
    | [] -> () (* No opened tabulation block. *)
    fin

  | Pp_tbreak (n, off) ->
    soit insertion_point = state.pp_margin - state.pp_space_left dans
    début filtre state.pp_tbox_stack avec
    | Pp_tbox tabs :: _ ->
      soit rec find n = fonction
        | x :: l -> si x >= n alors x sinon find n l
        | [] -> raise Not_found dans
      soit tab =
        filtre !tabs avec
        | x :: _ ->
          début
            essaie find insertion_point !tabs avec
            | Not_found -> x
          fin
        | _ -> insertion_point dans
      soit offset = tab - insertion_point dans
      si offset >= 0
      alors break_same_line state (offset + n)
      sinon break_new_line state (tab + off) state.pp_margin
    | [] -> () (* No opened tabulation block. *)
    fin

  | Pp_newline ->
    début filtre state.pp_format_stack avec
    | Format_elem (_, width) :: _ -> break_line state width
    | [] -> pp_output_newline state (* No opened block. *)
    fin

  | Pp_if_newline ->
    si state.pp_current_indent != state.pp_margin - state.pp_space_left
    alors pp_skip_token state

  | Pp_break (n, off) ->
    début filtre state.pp_format_stack avec
    | Format_elem (ty, width) :: _ ->
      début filtre ty avec
      | Pp_hovbox ->
        si size > state.pp_space_left
        alors break_new_line state off width
        sinon break_same_line state n
      | Pp_box ->
        (* Have the line just been broken here ? *)
        si state.pp_is_new_line alors break_same_line state n sinon
        si size > state.pp_space_left
         alors break_new_line state off width sinon
        (* break the line here leads to new indentation ? *)
        si state.pp_current_indent > state.pp_margin - width + off
        alors break_new_line state off width
        sinon break_same_line state n
      | Pp_hvbox -> break_new_line state off width
      | Pp_fits -> break_same_line state n
      | Pp_vbox -> break_new_line state off width
      | Pp_hbox -> break_same_line state n
      fin
    | [] -> () (* No opened block. *)
    fin

   | Pp_open_tag tag_name ->
     soit marker = state.pp_mark_open_tag tag_name dans
     pp_output_string state marker;
     state.pp_mark_stack <- tag_name :: state.pp_mark_stack

   | Pp_close_tag ->
     début filtre state.pp_mark_stack avec
     | tag_name :: tags ->
       soit marker = state.pp_mark_close_tag tag_name dans
       pp_output_string state marker;
       state.pp_mark_stack <- tags
     | [] -> () (* No more tag to close. *)
     fin
;;

(* Print if token size is known or printing is delayed.
   Size is known when not negative.
   Printing is delayed when the text waiting in the queue requires
   more room to format than exists on the current line.

   Note: [advance_loop] must be tail recursive to prevent stack overflows. *)
soit rec advance_loop state =
  filtre peek_queue state.pp_queue avec
  | {elem_size = size; token = tok; length = len} ->
    soit size = int_of_size size dans
    si not
         (size < 0 &&
          (state.pp_right_total - state.pp_left_total < state.pp_space_left))
    alors début
      ignore (take_queue state.pp_queue);
      format_pp_token state (si size < 0 alors pp_infinity sinon size) tok;
      state.pp_left_total <- len + state.pp_left_total;
      advance_loop state
    fin
;;

soit advance_left state =
  essaie advance_loop state avec
  | Empty_queue -> ()
;;

soit enqueue_advance state tok = pp_enqueue state tok; advance_left state;;

(* To enqueue a string : try to advance. *)
soit make_queue_elem size tok len =
  { elem_size = size; token = tok; length = len; };;

soit enqueue_string_as state size s =
  soit len = int_of_size size dans
  enqueue_advance state (make_queue_elem size (Pp_text s) len)
;;

soit enqueue_string state s =
  soit len = String.length s dans
  enqueue_string_as state (size_of_int len) s
;;

(* Routines for scan stack
   determine sizes of blocks. *)

(* The scan_stack is never empty. *)
soit scan_stack_bottom =
  soit q_elem = make_queue_elem (size_of_int (-1)) (Pp_text "") 0 dans
  [Scan_elem (-1, q_elem)]
;;

(* Set size of blocks on scan stack:
   if ty = true then size of break is set else size of block is set;
   in each case pp_scan_stack is popped. *)
soit clear_scan_stack state = state.pp_scan_stack <- scan_stack_bottom;;

(* Pattern matching on scan stack is exhaustive,
   since scan_stack is never empty.
   Pattern matching on token in scan stack is also exhaustive,
   since scan_push is used on breaks and opening of boxes. *)
soit set_size state ty =
  filtre state.pp_scan_stack avec
  | Scan_elem
      (left_tot,
       ({ elem_size = size; token = tok; length = _; } tel queue_elem)) :: t ->
    soit size = int_of_size size dans
    (* test if scan stack contains any data that is not obsolete. *)
    si left_tot < state.pp_left_total alors clear_scan_stack state sinon
      début filtre tok avec
      | Pp_break (_, _) | Pp_tbreak (_, _) ->
        si ty alors
        début
          queue_elem.elem_size <- size_of_int (state.pp_right_total + size);
          state.pp_scan_stack <- t
        fin
      | Pp_begin (_, _) ->
        si not ty alors
        début
          queue_elem.elem_size <- size_of_int (state.pp_right_total + size);
          state.pp_scan_stack <- t
        fin
      | Pp_text _ | Pp_stab | Pp_tbegin _ | Pp_tend | Pp_end
      | Pp_newline | Pp_if_newline
      | Pp_open_tag _ | Pp_close_tag ->
        () (* scan_push is only used for breaks and boxes. *)
      fin
  | [] -> () (* scan_stack is never empty. *)
;;

(* Push a token on scan stack. If b is true set_size is called. *)
soit scan_push state b tok =
  pp_enqueue state tok;
  si b alors set_size state vrai;
  state.pp_scan_stack <-
    Scan_elem (state.pp_right_total, tok) :: state.pp_scan_stack
;;

(* To open a new block :
   the user may set the depth bound pp_max_boxes
   any text nested deeper is printed as the ellipsis string. *)
soit pp_open_box_gen state indent br_ty =
  state.pp_curr_depth <- state.pp_curr_depth + 1;
  si state.pp_curr_depth < state.pp_max_boxes alors
    soit elem =
      make_queue_elem
        (size_of_int (- state.pp_right_total))
        (Pp_begin (indent, br_ty))
        0 dans
    scan_push state faux elem sinon
  si state.pp_curr_depth = state.pp_max_boxes
  alors enqueue_string state state.pp_ellipsis
;;

(* The box which is always opened. *)
soit pp_open_sys_box state = pp_open_box_gen state 0 Pp_hovbox;;

(* Close a block, setting sizes of its sub blocks. *)
soit pp_close_box state () =
  si state.pp_curr_depth > 1 alors
  début
    si state.pp_curr_depth < state.pp_max_boxes alors
    début
      pp_enqueue state
        { elem_size = size_of_int 0; token = Pp_end; length = 0; };
      set_size state vrai; set_size state faux
    fin;
    state.pp_curr_depth <- state.pp_curr_depth - 1;
  fin
;;

(* Open a tag, pushing it on the tag stack. *)
soit pp_open_tag state tag_name =
  si state.pp_print_tags alors
  début
    state.pp_tag_stack <- tag_name :: state.pp_tag_stack;
    state.pp_print_open_tag tag_name
  fin;
  si state.pp_mark_tags alors
    pp_enqueue state {
      elem_size = size_of_int 0;
      token = Pp_open_tag tag_name;
      length = 0;
    }
;;

(* Close a tag, popping it from the tag stack. *)
soit pp_close_tag state () =
  si state.pp_mark_tags alors
    pp_enqueue state {
      elem_size = size_of_int 0;
      token = Pp_close_tag;
      length = 0;
    };
  si state.pp_print_tags alors
  début
    filtre state.pp_tag_stack avec
    | tag_name :: tags ->
      state.pp_print_close_tag tag_name;
      state.pp_tag_stack <- tags
    | _ -> () (* No more tag to close. *)
  fin
;;

soit pp_set_print_tags state b = state.pp_print_tags <- b;;
soit pp_set_mark_tags state b = state.pp_mark_tags <- b;;
soit pp_get_print_tags state () = state.pp_print_tags;;
soit pp_get_mark_tags state () = state.pp_mark_tags;;
soit pp_set_tags state b = pp_set_print_tags state b; pp_set_mark_tags state b;;

soit pp_get_formatter_tag_functions state () = {
  mark_open_tag = state.pp_mark_open_tag;
  mark_close_tag = state.pp_mark_close_tag;
  print_open_tag = state.pp_print_open_tag;
  print_close_tag = state.pp_print_close_tag;
}
;;

soit pp_set_formatter_tag_functions state {
     mark_open_tag = mot;
     mark_close_tag = mct;
     print_open_tag = pot;
     print_close_tag = pct;
  } =
   state.pp_mark_open_tag <- mot;
   state.pp_mark_close_tag <- mct;
   state.pp_print_open_tag <- pot;
   state.pp_print_close_tag <- pct
;;

(* Initialize pretty-printer. *)
soit pp_rinit state =
  pp_clear_queue state;
  clear_scan_stack state;
  state.pp_format_stack <- [];
  state.pp_tbox_stack <- [];
  state.pp_tag_stack <- [];
  state.pp_mark_stack <- [];
  state.pp_current_indent <- 0;
  state.pp_curr_depth <- 0;
  state.pp_space_left <- state.pp_margin;
  pp_open_sys_box state;;

(* Flushing pretty-printer queue. *)
soit pp_flush_queue state b =
  pendant_que state.pp_curr_depth > 1 faire
    pp_close_box state ()
  fait;
  state.pp_right_total <- pp_infinity;
  advance_left state;
  si b alors pp_output_newline state;
  pp_rinit state
;;

(**************************************************************

  Procedures to format objects, and use boxes

 **************************************************************)

(* To format a string. *)
soit pp_print_as_size state size s =
  si state.pp_curr_depth < state.pp_max_boxes
  alors enqueue_string_as state size s
;;

soit pp_print_as state isize s =
  pp_print_as_size state (size_of_int isize) s
;;

soit pp_print_string state s =
  pp_print_as state (String.length s) s
;;

(* To format an integer. *)
soit pp_print_int state i = pp_print_string state (string_of_int i);;

(* To format a float. *)
soit pp_print_float state f = pp_print_string state (string_of_float f);;

(* To format a boolean. *)
soit pp_print_bool state b = pp_print_string state (string_of_bool b);;

(* To format a char. *)
soit pp_print_char state c =
  soit s = String.create 1 dans
  s.[0] <- c;
  pp_print_as state 1 s
;;

(* Opening boxes. *)
soit pp_open_hbox state () = pp_open_box_gen state 0 Pp_hbox
et pp_open_vbox state indent = pp_open_box_gen state indent Pp_vbox

et pp_open_hvbox state indent = pp_open_box_gen state indent Pp_hvbox
et pp_open_hovbox state indent = pp_open_box_gen state indent Pp_hovbox
et pp_open_box state indent = pp_open_box_gen state indent Pp_box;;

(* Print a new line after printing all queued text
   (same for print_flush but without a newline). *)
soit pp_print_newline state () =
  pp_flush_queue state vrai; state.pp_out_flush ()
et pp_print_flush state () =
  pp_flush_queue state faux; state.pp_out_flush ();;

(* To get a newline when one does not want to close the current block. *)
soit pp_force_newline state () =
  si state.pp_curr_depth < state.pp_max_boxes alors
    enqueue_advance state (make_queue_elem (size_of_int 0) Pp_newline 0)
;;

(* To format something if the line has just been broken. *)
soit pp_print_if_newline state () =
  si state.pp_curr_depth < state.pp_max_boxes alors
    enqueue_advance state (make_queue_elem (size_of_int 0) Pp_if_newline 0)
;;

(* Breaks: indicate where a block may be broken.
   If line is broken then offset is added to the indentation of the current
   block else (the value of) width blanks are printed.
   To do (?) : add a maximum width and offset value. *)
soit pp_print_break state width offset =
  si state.pp_curr_depth < state.pp_max_boxes alors
    soit elem =
      make_queue_elem
        (size_of_int (- state.pp_right_total))
        (Pp_break (width, offset))
        width dans
    scan_push state vrai elem
;;

soit pp_print_space state () = pp_print_break state 1 0
et pp_print_cut state () = pp_print_break state 0 0
;;

(* Tabulation boxes. *)
soit pp_open_tbox state () =
  state.pp_curr_depth <- state.pp_curr_depth + 1;
  si state.pp_curr_depth < state.pp_max_boxes alors
    soit elem =
      make_queue_elem (size_of_int 0) (Pp_tbegin (Pp_tbox (ref []))) 0 dans
    enqueue_advance state elem
;;

(* Close a tabulation block. *)
soit pp_close_tbox state () =
  si state.pp_curr_depth > 1 alors
  début
   si state.pp_curr_depth < state.pp_max_boxes alors
     soit elem = make_queue_elem (size_of_int 0) Pp_tend 0 dans
     enqueue_advance state elem;
     state.pp_curr_depth <- state.pp_curr_depth - 1
  fin
;;

(* Print a tabulation break. *)
soit pp_print_tbreak state width offset =
  si state.pp_curr_depth < state.pp_max_boxes alors
    soit elem =
      make_queue_elem
        (size_of_int (- state.pp_right_total))
        (Pp_tbreak (width, offset))
        width dans
    scan_push state vrai elem
;;

soit pp_print_tab state () = pp_print_tbreak state 0 0;;

soit pp_set_tab state () =
  si state.pp_curr_depth < state.pp_max_boxes alors
    soit elem =
      make_queue_elem (size_of_int 0) Pp_stab 0 dans
    enqueue_advance state elem
;;


(* Convenience functions *)

(* To format a list *)
soit rec pp_print_list ?(pp_sep = pp_print_cut) pp_v ppf = fonction
  | [] -> ()
  | [v] -> pp_v ppf v
  | v :: vs ->
    pp_v ppf v;
    pp_sep ppf ();
    pp_print_list ~pp_sep pp_v ppf vs

(* To format free-flowing text *)
soit pp_print_text ppf s =
  soit len = String.length s dans
  soit left = ref 0 dans
  soit right = ref 0 dans
  soit flush () =
    pp_print_string ppf (String.sub s !left (!right - !left));
    incr right; left := !right;
  dans
  pendant_que (!right <> len) faire
    filtre s.[!right] avec
      | '\n' ->
        flush ();
        pp_force_newline ppf ()
      | ' ' ->
        flush (); pp_print_space ppf ()
      (* there is no specific support for '\t'
         as it is unclear what a right semantics would be *)
      | _ -> incr right
  fait;
  si !left <> len alors flush ()


(**************************************************************

  Procedures to control the pretty-printers

 **************************************************************)

(* Fit max_boxes. *)
soit pp_set_max_boxes state n = si n > 1 alors state.pp_max_boxes <- n;;

(* To know the current maximum number of boxes allowed. *)
soit pp_get_max_boxes state () = state.pp_max_boxes;;

soit pp_over_max_boxes state () = state.pp_curr_depth = state.pp_max_boxes;;

(* Ellipsis. *)
soit pp_set_ellipsis_text state s = state.pp_ellipsis <- s
et pp_get_ellipsis_text state () = state.pp_ellipsis
;;

(* To set the margin of pretty-printer. *)
soit pp_limit n =
  si n < pp_infinity alors n sinon pred pp_infinity
;;

soit pp_set_min_space_left state n =
  si n >= 1 alors
    soit n = pp_limit n dans
    state.pp_min_space_left <- n;
    state.pp_max_indent <- state.pp_margin - state.pp_min_space_left;
    pp_rinit state
;;

(* Initially, we have :
  pp_max_indent = pp_margin - pp_min_space_left, and
  pp_space_left = pp_margin. *)
soit pp_set_max_indent state n =
  pp_set_min_space_left state (state.pp_margin - n)
;;
soit pp_get_max_indent state () = state.pp_max_indent;;

soit pp_set_margin state n =
  si n >= 1 alors
    soit n = pp_limit n dans
    state.pp_margin <- n;
    soit new_max_indent =
      (* Try to maintain max_indent to its actual value. *)
      si state.pp_max_indent <= state.pp_margin
      alors state.pp_max_indent sinon
      (* If possible maintain pp_min_space_left to its actual value,
         if this leads to a too small max_indent, take half of the
         new margin, if it is greater than 1. *)
       max (max (state.pp_margin - state.pp_min_space_left)
                (state.pp_margin / 2)) 1 dans
    (* Rebuild invariants. *)
    pp_set_max_indent state new_max_indent
;;

soit pp_get_margin state () = state.pp_margin;;

type formatter_out_functions = {
  out_string : string -> int -> int -> unit;
  out_flush : unit -> unit;
  out_newline : unit -> unit;
  out_spaces : int -> unit;
}
;;

soit pp_set_formatter_out_functions state {
      out_string = f;
      out_flush = g;
      out_newline = h;
      out_spaces = i;
    } =
  state.pp_out_string <- f;
  state.pp_out_flush <- g;
  state.pp_out_newline <- h;
  state.pp_out_spaces <- i;
;;

soit pp_get_formatter_out_functions state () = {
  out_string = state.pp_out_string;
  out_flush = state.pp_out_flush;
  out_newline = state.pp_out_newline;
  out_spaces = state.pp_out_spaces;
}
;;

soit pp_set_formatter_output_functions state f g =
  state.pp_out_string <- f; state.pp_out_flush <- g;;
soit pp_get_formatter_output_functions state () =
  (state.pp_out_string, state.pp_out_flush)
;;

soit pp_set_all_formatter_output_functions state
    ~out:f ~flush:g ~newline:h ~spaces:i =
  pp_set_formatter_output_functions state f g;
  state.pp_out_newline <- h;
  state.pp_out_spaces <- i;
;;
soit pp_get_all_formatter_output_functions state () =
  (state.pp_out_string, state.pp_out_flush,
   state.pp_out_newline, state.pp_out_spaces)
;;

(* Default function to output new lines. *)
soit display_newline state () = state.pp_out_string "\n" 0  1;;

(* Default function to output spaces. *)
soit blank_line = String.make 80 ' ';;
soit rec display_blanks state n =
  si n > 0 alors
  si n <= 80 alors state.pp_out_string blank_line 0 n sinon
  début
    state.pp_out_string blank_line 0 80;
    display_blanks state (n - 80)
  fin
;;

soit pp_set_formatter_out_channel state os =
  state.pp_out_string <- output os;
  state.pp_out_flush <- (fonc () -> flush os);
  state.pp_out_newline <- display_newline state;
  state.pp_out_spaces <- display_blanks state;
;;

(**************************************************************

  Creation of specific formatters

 **************************************************************)

soit default_pp_mark_open_tag s = "<" ^ s ^ ">";;
soit default_pp_mark_close_tag s = "</" ^ s ^ ">";;

soit default_pp_print_open_tag = ignore;;
soit default_pp_print_close_tag = ignore;;

soit pp_make_formatter f g h i =
  (* The initial state of the formatter contains a dummy box. *)
  soit pp_q = make_queue () dans
  soit sys_tok =
    make_queue_elem (size_of_int (-1)) (Pp_begin (0, Pp_hovbox)) 0 dans
  add_queue sys_tok pp_q;
  soit sys_scan_stack =
      (Scan_elem (1, sys_tok)) :: scan_stack_bottom dans
  {
   pp_scan_stack = sys_scan_stack;
   pp_format_stack = [];
   pp_tbox_stack = [];
   pp_tag_stack = [];
   pp_mark_stack = [];
   pp_margin = 78;
   pp_min_space_left = 10;
   pp_max_indent = 78 - 10;
   pp_space_left = 78;
   pp_current_indent = 0;
   pp_is_new_line = vrai;
   pp_left_total = 1;
   pp_right_total = 1;
   pp_curr_depth = 1;
   pp_max_boxes = max_int;
   pp_ellipsis = ".";
   pp_out_string = f;
   pp_out_flush = g;
   pp_out_newline = h;
   pp_out_spaces = i;
   pp_print_tags = faux;
   pp_mark_tags = faux;
   pp_mark_open_tag = default_pp_mark_open_tag;
   pp_mark_close_tag = default_pp_mark_close_tag;
   pp_print_open_tag = default_pp_print_open_tag;
   pp_print_close_tag = default_pp_print_close_tag;
   pp_queue = pp_q;
  }
;;

(* Make a formatter with default functions to output spaces and new lines. *)
soit make_formatter output flush =
  soit ppf = pp_make_formatter output flush ignore ignore dans
  ppf.pp_out_newline <- display_newline ppf;
  ppf.pp_out_spaces <- display_blanks ppf;
  ppf
;;

soit formatter_of_out_channel oc =
  make_formatter (output oc) (fonc () -> flush oc)
;;

soit formatter_of_buffer b =
  make_formatter (Buffer.add_substring b) ignore
;;

soit stdbuf = Buffer.create 512;;

(* Predefined formatters. *)
soit std_formatter = formatter_of_out_channel Pervasives.stdout
et err_formatter = formatter_of_out_channel Pervasives.stderr
et str_formatter = formatter_of_buffer stdbuf
;;

soit flush_str_formatter () =
  pp_flush_queue str_formatter faux;
  soit s = Buffer.contents stdbuf dans
  Buffer.reset stdbuf;
  s
;;

(**************************************************************

  Basic functions on the standard formatter

 **************************************************************)

soit open_hbox = pp_open_hbox std_formatter
et open_vbox = pp_open_vbox std_formatter
et open_hvbox = pp_open_hvbox std_formatter
et open_hovbox = pp_open_hovbox std_formatter
et open_box = pp_open_box std_formatter
et close_box = pp_close_box std_formatter
et open_tag = pp_open_tag std_formatter
et close_tag = pp_close_tag std_formatter
et print_as = pp_print_as std_formatter
et print_string = pp_print_string std_formatter
et print_int = pp_print_int std_formatter
et print_float = pp_print_float std_formatter
et print_char = pp_print_char std_formatter
et print_bool = pp_print_bool std_formatter
et print_break = pp_print_break std_formatter
et print_cut = pp_print_cut std_formatter
et print_space = pp_print_space std_formatter
et force_newline = pp_force_newline std_formatter
et print_flush = pp_print_flush std_formatter
et print_newline = pp_print_newline std_formatter
et print_if_newline = pp_print_if_newline std_formatter

et open_tbox = pp_open_tbox std_formatter
et close_tbox = pp_close_tbox std_formatter
et print_tbreak = pp_print_tbreak std_formatter

et set_tab = pp_set_tab std_formatter
et print_tab = pp_print_tab std_formatter

et set_margin = pp_set_margin std_formatter
et get_margin = pp_get_margin std_formatter

et set_max_indent = pp_set_max_indent std_formatter
et get_max_indent = pp_get_max_indent std_formatter

et set_max_boxes = pp_set_max_boxes std_formatter
et get_max_boxes = pp_get_max_boxes std_formatter
et over_max_boxes = pp_over_max_boxes std_formatter

et set_ellipsis_text = pp_set_ellipsis_text std_formatter
et get_ellipsis_text = pp_get_ellipsis_text std_formatter

et set_formatter_out_channel =
  pp_set_formatter_out_channel std_formatter

et set_formatter_out_functions =
  pp_set_formatter_out_functions std_formatter
et get_formatter_out_functions =
  pp_get_formatter_out_functions std_formatter

et set_formatter_output_functions =
  pp_set_formatter_output_functions std_formatter
et get_formatter_output_functions =
  pp_get_formatter_output_functions std_formatter

et set_all_formatter_output_functions =
  pp_set_all_formatter_output_functions std_formatter
et get_all_formatter_output_functions =
  pp_get_all_formatter_output_functions std_formatter

et set_formatter_tag_functions =
  pp_set_formatter_tag_functions std_formatter
et get_formatter_tag_functions =
  pp_get_formatter_tag_functions std_formatter
et set_print_tags =
  pp_set_print_tags std_formatter
et get_print_tags =
  pp_get_print_tags std_formatter
et set_mark_tags =
  pp_set_mark_tags std_formatter
et get_mark_tags =
  pp_get_mark_tags std_formatter
et set_tags =
  pp_set_tags std_formatter
;;


(**************************************************************

  Printf implementation.

 **************************************************************)

module Sformat = Printf.CamlinternalPr.Sformat;;
module Tformat = Printf.CamlinternalPr.Tformat;;

(* Error messages when processing formats. *)

(* Trailer: giving up at character number ... *)
soit giving_up mess fmt i =
  Printf.sprintf
    "Format.fprintf: %s \'%s\', giving up at character number %d%s"
    mess (Sformat.to_string fmt) i
    (si i < Sformat.length fmt
     alors Printf.sprintf " (%c)." (Sformat.get fmt i)
     sinon Printf.sprintf "%c" '.')
;;

(* When an invalid format deserves a special error explanation. *)
soit format_invalid_arg mess fmt i = invalid_arg (giving_up mess fmt i);;

(* Standard invalid format. *)
soit invalid_format fmt i = format_invalid_arg "bad format" fmt i;;

(* Cannot find a valid integer into that format. *)
soit invalid_integer fmt i =
  invalid_arg (giving_up "bad integer specification" fmt i);;

(* Finding an integer size out of a sub-string of the format. *)
soit format_int_of_string fmt i s =
  soit sz =
    essaie int_of_string s avec
    | Failure _ -> invalid_integer fmt i dans
  size_of_int sz
;;

(* Getting strings out of buffers. *)
soit get_buffer_out b =
  soit s = Buffer.contents b dans
  Buffer.reset b;
  s
;;

(* [ppf] is supposed to be a pretty-printer that outputs to buffer [b]:
   to extract the contents of [ppf] as a string we flush [ppf] and get the
   string out of [b]. *)
soit string_out b ppf =
  pp_flush_queue ppf faux;
  get_buffer_out b
;;

(* Applies [printer] to a formatter that outputs on a fresh buffer,
   then returns the resulting material. *)
soit exstring printer arg =
  soit b = Buffer.create 512 dans
  soit ppf = formatter_of_buffer b dans
  printer ppf arg;
  string_out b ppf
;;

(* To turn out a character accumulator into the proper string result. *)
soit implode_rev s0 = fonction
  | [] -> s0
  | l -> String.concat "" (List.rev (s0 :: l))
;;

(* [mkprintf] is the printf-like function generator: given the
   - [to_s] flag that tells if we are printing into a string,
   - the [get_out] function that has to be called to get a [ppf] function to
     output onto,
   it generates a [kprintf] function that takes as arguments a [k]
   continuation function to be called at the end of formatting,
   and a printing format string to print the rest of the arguments
   according to the format string.
   Regular [fprintf]-like functions of this module are obtained via partial
   applications of [mkprintf]. *)
soit mkprintf to_s get_out k fmt =

  (* [out] is global to this definition of [pr], and must be shared by all its
     recursive calls (if any). *)
  soit out = get_out fmt dans
  soit print_as = ref None dans
  soit outc c =
    filtre !print_as avec
    | None -> pp_print_char out c
    | Some size ->
      pp_print_as_size out size (String.make 1 c);
      print_as := None
  et outs s =
    filtre !print_as avec
    | None -> pp_print_string out s
    | Some size ->
      pp_print_as_size out size s;
      print_as := None
  et flush out = pp_print_flush out () dans

  soit rec pr k n fmt v =

    soit len = Sformat.length fmt dans

    soit rec doprn n i =
      si i >= len alors Obj.magic (k out) sinon
      filtre Sformat.get fmt i avec
      | '%' ->
        Tformat.scan_format fmt v n i cont_s cont_a cont_t cont_f cont_m
      | '@' ->
        soit i = succ i dans
        si i >= len alors invalid_format fmt i sinon
        début filtre Sformat.get fmt i avec
        | '[' ->
          do_pp_open_box out n (succ i)
        | ']' ->
          pp_close_box out ();
          doprn n (succ i)
        | '{' ->
          do_pp_open_tag out n (succ i)
        | '}' ->
          pp_close_tag out ();
          doprn n (succ i)
        | ' ' ->
          pp_print_space out ();
          doprn n (succ i)
        | ',' ->
          pp_print_cut out ();
          doprn n (succ i)
        | '?' ->
          pp_print_flush out ();
          doprn n (succ i)
        | '.' ->
          pp_print_newline out ();
          doprn n (succ i)
        | '\n' ->
          pp_force_newline out ();
          doprn n (succ i)
        | ';' ->
          do_pp_break out n (succ i)
        | '<' ->
          soit got_size size n i =
            print_as := Some size;
            doprn n (skip_gt i) dans
          get_int n (succ i) got_size
        | '@' ->
          outc '@';
          doprn n (succ i)
        | _ -> invalid_format fmt i
        fin
      | c -> outc c; doprn n (succ i)

    et cont_s n s i =
      outs s; doprn n i
    et cont_a n printer arg i =
      si to_s alors
        outs ((Obj.magic printer : unit -> _ -> string) () arg)
      sinon
        printer out arg;
      doprn n i
    et cont_t n printer i =
      si to_s alors
        outs ((Obj.magic printer : unit -> string) ())
      sinon
        printer out;
      doprn n i
    et cont_f n i =
      flush out; doprn n i
    et cont_m n xf i =
      soit m =
        Sformat.add_int_index
          (Tformat.count_printing_arguments_of_format xf) n dans
      pr (Obj.magic (fonc _ -> doprn m i)) n xf v

    et get_int n i c =
      si i >= len alors invalid_integer fmt i sinon
      filtre Sformat.get fmt i avec
      | ' ' -> get_int n (succ i) c
      | '%' ->
        soit cont_s n s i = c (format_int_of_string fmt i s) n i
        et cont_a _n _printer _arg i = invalid_integer fmt i
        et cont_t _n _printer i = invalid_integer fmt i
        et cont_f _n i = invalid_integer fmt i
        et cont_m _n _sfmt i = invalid_integer fmt i dans
        Tformat.scan_format fmt v n i cont_s cont_a cont_t cont_f cont_m
      | _ ->
        soit rec get j =
          si j >= len alors invalid_integer fmt j sinon
          filtre Sformat.get fmt j avec
          | '0' .. '9' | '-' -> get (succ j)
          | _ ->
            soit size =
              si j = i alors size_of_int 0 sinon
              soit s = Sformat.sub fmt (Sformat.index_of_int i) (j - i) dans
              format_int_of_string fmt j s dans
            c size n j dans
        get i

    et skip_gt i =
      si i >= len alors invalid_format fmt i sinon
      filtre Sformat.get fmt i avec
      | ' ' -> skip_gt (succ i)
      | '>' -> succ i
      | _ -> invalid_format fmt i

    et get_box_kind i =
      si i >= len alors Pp_box, i sinon
      filtre Sformat.get fmt i avec
      | 'h' ->
         soit i = succ i dans
         si i >= len alors Pp_hbox, i sinon
         début filtre Sformat.get fmt i avec
         | 'o' ->
           soit i = succ i dans
           si i >= len alors format_invalid_arg "bad box format" fmt i sinon
           début filtre Sformat.get fmt i avec
           | 'v' -> Pp_hovbox, succ i
           | c ->
             format_invalid_arg
               ("bad box name ho" ^ String.make 1 c) fmt i
           fin
         | 'v' -> Pp_hvbox, succ i
         | _ -> Pp_hbox, i
         fin
      | 'b' -> Pp_box, succ i
      | 'v' -> Pp_vbox, succ i
      | _ -> Pp_box, i

    et get_tag_name n i c =
      soit rec get accu n i j =
        si j >= len alors
          c (implode_rev
               (Sformat.sub fmt (Sformat.index_of_int i) (j - i))
               accu)
            n j sinon
        filtre Sformat.get fmt j avec
        | '>' ->
          c (implode_rev
               (Sformat.sub fmt (Sformat.index_of_int i) (j - i))
               accu)
            n j
        | '%' ->
          soit s0 = Sformat.sub fmt (Sformat.index_of_int i) (j - i) dans
          soit cont_s n s i = get (s :: s0 :: accu) n i i
          et cont_a n printer arg i =
            soit s =
              si to_s
              alors (Obj.magic printer : unit -> _ -> string) () arg
              sinon exstring printer arg dans
            get (s :: s0 :: accu) n i i
          et cont_t n printer i =
            soit s =
              si to_s
              alors (Obj.magic printer : unit -> string) ()
              sinon exstring (fonc ppf () -> printer ppf) () dans
            get (s :: s0 :: accu) n i i
          et cont_f _n i =
            format_invalid_arg "bad tag name specification" fmt i
          et cont_m _n _sfmt i =
            format_invalid_arg "bad tag name specification" fmt i dans
          Tformat.scan_format fmt v n j cont_s cont_a cont_t cont_f cont_m
        | _ -> get accu n i (succ j) dans
      get [] n i i

    et do_pp_break ppf n i =
      si i >= len alors début pp_print_space ppf (); doprn n i fin sinon
      filtre Sformat.get fmt i avec
      | '<' ->
        soit rec got_nspaces nspaces n i =
          get_int n i (got_offset nspaces)
        et got_offset nspaces offset n i =
          pp_print_break ppf (int_of_size nspaces) (int_of_size offset);
          doprn n (skip_gt i) dans
        get_int n (succ i) got_nspaces
      | _c -> pp_print_space ppf (); doprn n i

    et do_pp_open_box ppf n i =
      si i >= len alors début pp_open_box_gen ppf 0 Pp_box; doprn n i fin sinon
      filtre Sformat.get fmt i avec
      | '<' ->
        soit kind, i = get_box_kind (succ i) dans
        soit got_size size n i =
          pp_open_box_gen ppf (int_of_size size) kind;
          doprn n (skip_gt i) dans
        get_int n i got_size
      | _c -> pp_open_box_gen ppf 0 Pp_box; doprn n i

    et do_pp_open_tag ppf n i =
      si i >= len alors début pp_open_tag ppf ""; doprn n i fin sinon
      filtre Sformat.get fmt i avec
      | '<' ->
        soit got_name tag_name n i =
          pp_open_tag ppf tag_name;
          doprn n (skip_gt i) dans
        get_tag_name n (succ i) got_name
      | _c -> pp_open_tag ppf ""; doprn n i dans

    doprn n 0 dans

  soit kpr = pr k (Sformat.index_of_int 0) dans

  Tformat.kapr kpr fmt
;;

(**************************************************************

  Defining [fprintf] and various flavors of [fprintf].

 **************************************************************)

soit kfprintf k ppf = mkprintf faux (fonc _ -> ppf) k;;
soit ikfprintf k ppf = Tformat.kapr (fonc _ _ -> Obj.magic (k ppf));;

soit fprintf ppf = kfprintf ignore ppf;;
soit ifprintf ppf = ikfprintf ignore ppf;;
soit printf fmt = fprintf std_formatter fmt;;
soit eprintf fmt = fprintf err_formatter fmt;;

soit ksprintf k =
  soit b = Buffer.create 512 dans
  soit k ppf = k (string_out b ppf) dans
  soit ppf = formatter_of_buffer b dans
  soit get_out _ = ppf dans
  mkprintf vrai get_out k
;;

soit sprintf fmt = ksprintf (fonc s -> s) fmt;;

soit asprintf fmt =
  soit b = Buffer.create 512 dans
  soit k ppf = string_out b ppf dans
  soit ppf = formatter_of_buffer b dans
  soit get_out _ = ppf dans
  mkprintf faux get_out k fmt;;

(**************************************************************

  Deprecated stuff.

 **************************************************************)

soit kbprintf k b =
  mkprintf faux (fonc _ -> formatter_of_buffer b) k
;;

(* Deprecated error prone function bprintf. *)
soit bprintf b =
  soit k ppf = pp_flush_queue ppf faux dans
  kbprintf k b
;;

(* Deprecated alias for ksprintf. *)
soit kprintf = ksprintf;;

(* Output everything left in the pretty printer queue at end of execution. *)
at_exit print_flush
;;
