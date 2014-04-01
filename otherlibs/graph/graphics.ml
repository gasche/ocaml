(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

exception Graphic_failure de string

(* Initializations *)

soit _ =
  Callback.register_exception "Graphics.Graphic_failure" (Graphic_failure "")

dehors raw_open_graph: string -> unit = "caml_gr_open_graph"
dehors raw_close_graph: unit -> unit = "caml_gr_close_graph"
dehors sigio_signal: unit -> int = "caml_gr_sigio_signal"
dehors sigio_handler: int -> unit = "caml_gr_sigio_handler"

soit unix_open_graph arg =
  Sys.set_signal (sigio_signal()) (Sys.Signal_handle sigio_handler);
  raw_open_graph arg

soit unix_close_graph () =
  Sys.set_signal (sigio_signal()) Sys.Signal_ignore;
  raw_close_graph ()

soit (open_graph, close_graph) =
  filtre Sys.os_type avec
  | "Unix" | "Cygwin" -> (unix_open_graph, unix_close_graph)
  | "Win32" -> (raw_open_graph, raw_close_graph)
  | "MacOS" -> (raw_open_graph, raw_close_graph)
  | _ -> invalid_arg ("Graphics: unknown OS type: " ^ Sys.os_type)

dehors set_window_title : string -> unit = "caml_gr_set_window_title"
dehors resize_window : int -> int -> unit = "caml_gr_resize_window"
dehors clear_graph : unit -> unit = "caml_gr_clear_graph"
dehors size_x : unit -> int = "caml_gr_size_x"
dehors size_y : unit -> int = "caml_gr_size_y"

(* Double-buffering *)

dehors display_mode : bool -> unit = "caml_gr_display_mode"
dehors remember_mode : bool -> unit = "caml_gr_remember_mode"
dehors synchronize : unit -> unit = "caml_gr_synchronize"

soit auto_synchronize = fonction
  | vrai -> display_mode vrai; remember_mode vrai; synchronize ()
  | faux -> display_mode faux; remember_mode vrai
;;


(* Colors *)

type color = int

soit rgb r g b = (r dgl 16) + (g dgl 8) + b

dehors set_color : color -> unit = "caml_gr_set_color"

soit black   = 0x000000
et white   = 0xFFFFFF
et red     = 0xFF0000
et green   = 0x00FF00
et blue    = 0x0000FF
et yellow  = 0xFFFF00
et cyan    = 0x00FFFF
et magenta = 0xFF00FF

soit background = white
et foreground = black

(* Drawing *)

dehors plot : int -> int -> unit = "caml_gr_plot"
soit plots points =
  pour i = 0 à Array.length points - 1 faire
    soit (x, y) = points.(i) dans
    plot x y;
  fait
;;
dehors point_color : int -> int -> color = "caml_gr_point_color"
dehors moveto : int -> int -> unit = "caml_gr_moveto"
dehors current_x : unit -> int = "caml_gr_current_x"
dehors current_y : unit -> int = "caml_gr_current_y"
soit current_point () = current_x (), current_y ()
dehors lineto : int -> int -> unit = "caml_gr_lineto"
soit rlineto x y = lineto (current_x () + x) (current_y () + y)
soit rmoveto x y = moveto (current_x () + x) (current_y () + y)

dehors raw_draw_rect : int -> int -> int -> int -> unit = "caml_gr_draw_rect"
soit draw_rect x y w h =
  si w < 0 || h < 0 alors raise (Invalid_argument "draw_rect")
  sinon raw_draw_rect x y w h
;;

soit draw_poly, draw_poly_line =
  soit dodraw close_flag points =
    si Array.length points > 0 alors début
      soit (savex, savey) = current_point () dans
      moveto (fst points.(0)) (snd points.(0));
      pour i = 1 à Array.length points - 1 faire
        soit (x, y) = points.(i) dans
        lineto x y;
      fait;
      si close_flag alors lineto (fst points.(0)) (snd points.(0));
      moveto savex savey;
    fin;
  dans dodraw vrai, dodraw faux
;;
soit draw_segments segs =
  soit (savex, savey) = current_point () dans
  pour i = 0 à Array.length segs - 1 faire
    soit (x1, y1, x2, y2) = segs.(i) dans
    moveto x1 y1;
    lineto x2 y2;
  fait;
  moveto savex savey;
;;

dehors raw_draw_arc : int -> int -> int -> int -> int -> int -> unit
               = "caml_gr_draw_arc" "caml_gr_draw_arc_nat"
soit draw_arc x y rx ry a1 a2 =
  si rx < 0 || ry < 0 alors raise (Invalid_argument "draw_arc/ellipse/circle")
  sinon raw_draw_arc x y rx ry a1 a2
;;

soit draw_ellipse x y rx ry = draw_arc x y rx ry 0 360
soit draw_circle x y r = draw_arc x y r r 0 360

dehors raw_set_line_width : int -> unit = "caml_gr_set_line_width"
soit set_line_width w =
  si w < 0 alors raise (Invalid_argument "set_line_width")
  sinon raw_set_line_width w
;;

dehors raw_fill_rect : int -> int -> int -> int -> unit = "caml_gr_fill_rect"
soit fill_rect x y w h =
  si w < 0 || h < 0 alors raise (Invalid_argument "fill_rect")
  sinon raw_fill_rect x y w h
;;

dehors fill_poly : (int * int) array -> unit = "caml_gr_fill_poly"
dehors raw_fill_arc : int -> int -> int -> int -> int -> int -> unit
               = "caml_gr_fill_arc" "caml_gr_fill_arc_nat"
soit fill_arc x y rx ry a1 a2 =
  si rx < 0 || ry < 0 alors raise (Invalid_argument "fill_arc/ellipse/circle")
  sinon raw_fill_arc x y rx ry a1 a2
;;

soit fill_ellipse x y rx ry = fill_arc x y rx ry 0 360
soit fill_circle x y r = fill_arc x y r r 0 360

(* Text *)

dehors draw_char : char -> unit = "caml_gr_draw_char"
dehors draw_string : string -> unit = "caml_gr_draw_string"
dehors set_font : string -> unit = "caml_gr_set_font"
dehors set_text_size : int -> unit = "caml_gr_set_text_size"
dehors text_size : string -> int * int = "caml_gr_text_size"

(* Images *)

type image

soit transp = -1

dehors make_image : color array array -> image = "caml_gr_make_image"
dehors dump_image : image -> color array array = "caml_gr_dump_image"
dehors draw_image : image -> int -> int -> unit = "caml_gr_draw_image"
dehors create_image : int -> int -> image = "caml_gr_create_image"
dehors blit_image : image -> int -> int -> unit = "caml_gr_blit_image"

soit get_image x y w h =
  soit image = create_image w h dans
  blit_image image x y;
  image

(* Events *)

type status =
  { mouse_x : int;
    mouse_y : int;
    button : bool;
    keypressed : bool;
    key : char }

type event =
    Button_down
  | Button_up
  | Key_pressed
  | Mouse_motion
  | Poll

dehors wait_next_event : event list -> status = "caml_gr_wait_event"

soit mouse_pos () =
  soit e = wait_next_event [Poll] dans (e.mouse_x, e.mouse_y)

soit button_down () =
  soit e = wait_next_event [Poll] dans e.button

soit read_key () =
  soit e = wait_next_event [Key_pressed] dans e.key

soit key_pressed () =
  soit e = wait_next_event [Poll] dans e.keypressed

soit loop_at_exit events handler =
  soit events = List.filter (fonc e -> e <> Poll) events dans
  at_exit (fonc _ ->
    essaie
      pendant_que vrai faire
        soit e = wait_next_event events dans
        handler e
      fait
    avec Exit -> close_graph ()
       | e -> close_graph (); raise e
  )

(*** Sound *)

dehors sound : int -> int -> unit = "caml_gr_sound"

(* Splines *)
soit add (x1, y1) (x2, y2) = (x1 +. x2, y1 +. y2)
et sub (x1, y1) (x2, y2) = (x1 -. x2, y1 -. y2)
et middle (x1, y1) (x2, y2) = ((x1 +. x2) /. 2.0,  (y1 +. y2) /. 2.0)
et area (x1, y1) (x2, y2) = abs_float (x1 *. y2 -. x2 *. y1)
et norm (x1, y1) = sqrt (x1 *. x1 +. y1 *. y1);;

soit test a b c d =
 soit v = sub d a dans
 soit s = norm v dans
 area v (sub a b) <= s && area v (sub a c) <= s;;

soit spline a b c d =
  soit rec spl accu a b c d =
   si test a b c d alors d :: accu sinon
   soit a' = middle a b
   et o = middle b c dans
   soit b' = middle a' o
   et d' = middle c d dans
   soit c' = middle o d' dans
   soit i = middle b' c' dans
   spl  (spl accu a a' b' i) i c' d' d dans
  spl [a] a b c d;;

soit curveto b c (x, y tel d) =
 soit float_point (x, y) = (float_of_int x, float_of_int y) dans
 soit round f = int_of_float (f +. 0.5) dans
 soit int_point (x, y) = (round x, round y) dans
 soit points =
   spline
    (float_point (current_point ()))
    (float_point b) (float_point c) (float_point d) dans
 draw_poly_line
  (Array.of_list (List.map int_point points));
 moveto x y;;
