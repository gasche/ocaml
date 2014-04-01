(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* type 'a option = None | Some of 'a *)

(* Exceptions *)

dehors register_named_value : string -> 'a -> unit
                              = "caml_register_named_value"

soit () =
  (* for asmrun/fail.c *)
  register_named_value "Pervasives.array_bound_error"
    (Invalid_argument "index out of bounds")


dehors raise : exn -> 'a = "%raise"
dehors raise_notrace : exn -> 'a = "%raise_notrace"

soit failwith s = raise(Failure s)
soit invalid_arg s = raise(Invalid_argument s)

exception Exit

(* Composition operators *)

dehors ( |> ) : 'a -> ('a -> 'b) -> 'b = "%revapply"
dehors ( @@ ) : ('a -> 'b) -> 'a -> 'b = "%apply"

(* Comparisons *)

dehors ( = ) : 'a -> 'a -> bool = "%equal"
dehors ( <> ) : 'a -> 'a -> bool = "%notequal"
dehors ( < ) : 'a -> 'a -> bool = "%lessthan"
dehors ( > ) : 'a -> 'a -> bool = "%greaterthan"
dehors ( <= ) : 'a -> 'a -> bool = "%lessequal"
dehors ( >= ) : 'a -> 'a -> bool = "%greaterequal"
dehors compare : 'a -> 'a -> int = "%compare"

soit min x y = si x <= y alors x sinon y
soit max x y = si x >= y alors x sinon y

dehors ( == ) : 'a -> 'a -> bool = "%eq"
dehors ( != ) : 'a -> 'a -> bool = "%noteq"

(* Boolean operations *)

dehors not : bool -> bool = "%boolnot"
dehors ( & ) : bool -> bool -> bool = "%sequand"
dehors ( && ) : bool -> bool -> bool = "%sequand"
dehors ( ou ) : bool -> bool -> bool = "%sequor"
dehors ( || ) : bool -> bool -> bool = "%sequor"

(* Integer operations *)

dehors ( ~- ) : int -> int = "%negint"
dehors ( ~+ ) : int -> int = "%identity"
dehors succ : int -> int = "%succint"
dehors pred : int -> int = "%predint"
dehors ( + ) : int -> int -> int = "%addint"
dehors ( - ) : int -> int -> int = "%subint"
dehors ( *  ) : int -> int -> int = "%mulint"
dehors ( / ) : int -> int -> int = "%divint"
dehors ( mod ) : int -> int -> int = "%modint"

soit abs x = si x >= 0 alors x sinon -x

dehors ( etl ) : int -> int -> int = "%andint"
dehors ( oul ) : int -> int -> int = "%orint"
dehors ( ouxl ) : int -> int -> int = "%xorint"

soit lnot x = x ouxl (-1)

dehors ( dgl ) : int -> int -> int = "%lslint"
dehors ( ddl ) : int -> int -> int = "%lsrint"
dehors ( dda ) : int -> int -> int = "%asrint"

soit max_int = (-1) ddl 1
soit min_int = max_int + 1

(* Floating-point operations *)

dehors ( ~-. ) : float -> float = "%negfloat"
dehors ( ~+. ) : float -> float = "%identity"
dehors ( +. ) : float -> float -> float = "%addfloat"
dehors ( -. ) : float -> float -> float = "%subfloat"
dehors ( *. ) : float -> float -> float = "%mulfloat"
dehors ( /. ) : float -> float -> float = "%divfloat"
dehors ( ** ) : float -> float -> float = "caml_power_float" "pow" "float"
dehors exp : float -> float = "caml_exp_float" "exp" "float"
dehors expm1 : float -> float = "caml_expm1_float" "caml_expm1" "float"
dehors acos : float -> float = "caml_acos_float" "acos" "float"
dehors asin : float -> float = "caml_asin_float" "asin" "float"
dehors atan : float -> float = "caml_atan_float" "atan" "float"
dehors atan2 : float -> float -> float = "caml_atan2_float" "atan2" "float"
dehors hypot : float -> float -> float
               = "caml_hypot_float" "caml_hypot" "float"
dehors cos : float -> float = "caml_cos_float" "cos" "float"
dehors cosh : float -> float = "caml_cosh_float" "cosh" "float"
dehors log : float -> float = "caml_log_float" "log" "float"
dehors log10 : float -> float = "caml_log10_float" "log10" "float"
dehors log1p : float -> float = "caml_log1p_float" "caml_log1p" "float"
dehors sin : float -> float = "caml_sin_float" "sin" "float"
dehors sinh : float -> float = "caml_sinh_float" "sinh" "float"
dehors sqrt : float -> float = "caml_sqrt_float" "sqrt" "float"
dehors tan : float -> float = "caml_tan_float" "tan" "float"
dehors tanh : float -> float = "caml_tanh_float" "tanh" "float"
dehors ceil : float -> float = "caml_ceil_float" "ceil" "float"
dehors floor : float -> float = "caml_floor_float" "floor" "float"
dehors abs_float : float -> float = "%absfloat"
dehors copysign : float -> float -> float
                  = "caml_copysign_float" "caml_copysign" "float"
dehors mod_float : float -> float -> float = "caml_fmod_float" "fmod" "float"
dehors frexp : float -> float * int = "caml_frexp_float"
dehors ldexp : float -> int -> float = "caml_ldexp_float"
dehors modf : float -> float * float = "caml_modf_float"
dehors float : int -> float = "%floatofint"
dehors float_of_int : int -> float = "%floatofint"
dehors truncate : float -> int = "%intoffloat"
dehors int_of_float : float -> int = "%intoffloat"
dehors float_of_bits : int64 -> float = "caml_int64_float_of_bits"
soit infinity =
  float_of_bits 0x7F_F0_00_00_00_00_00_00L
soit neg_infinity =
  float_of_bits 0xFF_F0_00_00_00_00_00_00L
soit nan =
  float_of_bits 0x7F_F0_00_00_00_00_00_01L
soit max_float =
  float_of_bits 0x7F_EF_FF_FF_FF_FF_FF_FFL
soit min_float =
  float_of_bits 0x00_10_00_00_00_00_00_00L
soit epsilon_float =
  float_of_bits 0x3C_B0_00_00_00_00_00_00L

type fpclass =
    FP_normal
  | FP_subnormal
  | FP_zero
  | FP_infinite
  | FP_nan
dehors classify_float : float -> fpclass = "caml_classify_float"

(* String operations -- more in module String *)

dehors string_length : string -> int = "%string_length"
dehors string_create : int -> string = "caml_create_string"
dehors string_blit : string -> int -> string -> int -> int -> unit
                     = "caml_blit_string" "noalloc"

soit ( ^ ) s1 s2 =
  soit l1 = string_length s1 et l2 = string_length s2 dans
  soit s = string_create (l1 + l2) dans
  string_blit s1 0 s 0 l1;
  string_blit s2 0 s l1 l2;
  s

(* Character operations -- more in module Char *)

dehors int_of_char : char -> int = "%identity"
dehors unsafe_char_of_int : int -> char = "%identity"
soit char_of_int n =
  si n < 0 || n > 255 alors invalid_arg "char_of_int" sinon unsafe_char_of_int n

(* Unit operations *)

dehors ignore : 'a -> unit = "%ignore"

(* Pair operations *)

dehors fst : 'a * 'b -> 'a = "%field0"
dehors snd : 'a * 'b -> 'b = "%field1"

(* String conversion functions *)

dehors format_int : string -> int -> string = "caml_format_int"
dehors format_float : string -> float -> string = "caml_format_float"

soit string_of_bool b =
  si b alors "true" sinon "false"
soit bool_of_string = fonction
  | "true" -> vrai
  | "false" -> faux
  | _ -> invalid_arg "bool_of_string"

soit string_of_int n =
  format_int "%d" n

dehors int_of_string : string -> int = "caml_int_of_string"

module String = struct
  dehors get : string -> int -> char = "%string_safe_get"
fin

soit valid_float_lexem s =
  soit l = string_length s dans
  soit rec loop i =
    si i >= l alors s ^ "." sinon
    filtre s.[i] avec
    | '0' .. '9' | '-' -> loop (i + 1)
    | _ -> s
  dans
  loop 0
;;

soit string_of_float f = valid_float_lexem (format_float "%.12g" f);;

dehors float_of_string : string -> float = "caml_float_of_string"

(* List operations -- more in module List *)

soit rec ( @ ) l1 l2 =
  filtre l1 avec
    [] -> l2
  | hd :: tl -> hd :: (tl @ l2)

(* I/O operations *)

type in_channel
type out_channel

dehors open_descriptor_out : int -> out_channel
                             = "caml_ml_open_descriptor_out"
dehors open_descriptor_in : int -> in_channel = "caml_ml_open_descriptor_in"

soit stdin = open_descriptor_in 0
soit stdout = open_descriptor_out 1
soit stderr = open_descriptor_out 2

(* General output functions *)

type open_flag =
    Open_rdonly | Open_wronly | Open_append
  | Open_creat | Open_trunc | Open_excl
  | Open_binary | Open_text | Open_nonblock

dehors open_desc : string -> open_flag list -> int -> int = "caml_sys_open"

soit open_out_gen mode perm name =
  open_descriptor_out(open_desc name mode perm)

soit open_out name =
  open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_text] 0o666 name

soit open_out_bin name =
  open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_binary] 0o666 name

dehors flush : out_channel -> unit = "caml_ml_flush"

dehors out_channels_list : unit -> out_channel list
                           = "caml_ml_out_channels_list"

soit flush_all () =
  soit rec iter = fonction
      [] -> ()
    | a :: l -> (essaie flush a avec _ -> ()); iter l
  dans iter (out_channels_list ())

dehors unsafe_output : out_channel -> string -> int -> int -> unit
                       = "caml_ml_output"

dehors output_char : out_channel -> char -> unit = "caml_ml_output_char"

soit output_string oc s =
  unsafe_output oc s 0 (string_length s)

soit output oc s ofs len =
  si ofs < 0 || len < 0 || ofs > string_length s - len
  alors invalid_arg "output"
  sinon unsafe_output oc s ofs len

dehors output_byte : out_channel -> int -> unit = "caml_ml_output_char"
dehors output_binary_int : out_channel -> int -> unit = "caml_ml_output_int"

dehors marshal_to_channel : out_channel -> 'a -> unit list -> unit
     = "caml_output_value"
soit output_value chan v = marshal_to_channel chan v []

dehors seek_out : out_channel -> int -> unit = "caml_ml_seek_out"
dehors pos_out : out_channel -> int = "caml_ml_pos_out"
dehors out_channel_length : out_channel -> int = "caml_ml_channel_size"
dehors close_out_channel : out_channel -> unit = "caml_ml_close_channel"
soit close_out oc = flush oc; close_out_channel oc
soit close_out_noerr oc =
  (essaie flush oc avec _ -> ());
  (essaie close_out_channel oc avec _ -> ())
dehors set_binary_mode_out : out_channel -> bool -> unit
                             = "caml_ml_set_binary_mode"

(* General input functions *)

soit open_in_gen mode perm name =
  open_descriptor_in(open_desc name mode perm)

soit open_in name =
  open_in_gen [Open_rdonly; Open_text] 0 name

soit open_in_bin name =
  open_in_gen [Open_rdonly; Open_binary] 0 name

dehors input_char : in_channel -> char = "caml_ml_input_char"

dehors unsafe_input : in_channel -> string -> int -> int -> int
                      = "caml_ml_input"

soit input ic s ofs len =
  si ofs < 0 || len < 0 || ofs > string_length s - len
  alors invalid_arg "input"
  sinon unsafe_input ic s ofs len

soit rec unsafe_really_input ic s ofs len =
  si len <= 0 alors () sinon début
    soit r = unsafe_input ic s ofs len dans
    si r = 0
    alors raise End_of_file
    sinon unsafe_really_input ic s (ofs + r) (len - r)
  fin

soit really_input ic s ofs len =
  si ofs < 0 || len < 0 || ofs > string_length s - len
  alors invalid_arg "really_input"
  sinon unsafe_really_input ic s ofs len

dehors input_scan_line : in_channel -> int = "caml_ml_input_scan_line"

soit input_line chan =
  soit rec build_result buf pos = fonction
    [] -> buf
  | hd :: tl ->
      soit len = string_length hd dans
      string_blit hd 0 buf (pos - len) len;
      build_result buf (pos - len) tl dans
  soit rec scan accu len =
    soit n = input_scan_line chan dans
    si n = 0 alors début                   (* n = 0: we are at EOF *)
      filtre accu avec
        [] -> raise End_of_file
      | _  -> build_result (string_create len) len accu
    fin sinon si n > 0 alors début          (* n > 0: newline found in buffer *)
      soit res = string_create (n - 1) dans
      ignore (unsafe_input chan res 0 (n - 1));
      ignore (input_char chan);           (* skip the newline *)
      filtre accu avec
        [] -> res
      |  _ -> soit len = len + n - 1 dans
              build_result (string_create len) len (res :: accu)
    fin sinon début                        (* n < 0: newline not found *)
      soit beg = string_create (-n) dans
      ignore(unsafe_input chan beg 0 (-n));
      scan (beg :: accu) (len - n)
    fin
  dans scan [] 0

dehors input_byte : in_channel -> int = "caml_ml_input_char"
dehors input_binary_int : in_channel -> int = "caml_ml_input_int"
dehors input_value : in_channel -> 'a = "caml_input_value"
dehors seek_in : in_channel -> int -> unit = "caml_ml_seek_in"
dehors pos_in : in_channel -> int = "caml_ml_pos_in"
dehors in_channel_length : in_channel -> int = "caml_ml_channel_size"
dehors close_in : in_channel -> unit = "caml_ml_close_channel"
soit close_in_noerr ic = (essaie close_in ic avec _ -> ());;
dehors set_binary_mode_in : in_channel -> bool -> unit
                            = "caml_ml_set_binary_mode"

(* Output functions on standard output *)

soit print_char c = output_char stdout c
soit print_string s = output_string stdout s
soit print_int i = output_string stdout (string_of_int i)
soit print_float f = output_string stdout (string_of_float f)
soit print_endline s =
  output_string stdout s; output_char stdout '\n'; flush stdout
soit print_newline () = output_char stdout '\n'; flush stdout

(* Output functions on standard error *)

soit prerr_char c = output_char stderr c
soit prerr_string s = output_string stderr s
soit prerr_int i = output_string stderr (string_of_int i)
soit prerr_float f = output_string stderr (string_of_float f)
soit prerr_endline s =
  output_string stderr s; output_char stderr '\n'; flush stderr
soit prerr_newline () = output_char stderr '\n'; flush stderr

(* Input functions on standard input *)

soit read_line () = flush stdout; input_line stdin
soit read_int () = int_of_string(read_line())
soit read_float () = float_of_string(read_line())

(* Operations on large files *)

module LargeFile =
  struct
    dehors seek_out : out_channel -> int64 -> unit = "caml_ml_seek_out_64"
    dehors pos_out : out_channel -> int64 = "caml_ml_pos_out_64"
    dehors out_channel_length : out_channel -> int64
                                = "caml_ml_channel_size_64"
    dehors seek_in : in_channel -> int64 -> unit = "caml_ml_seek_in_64"
    dehors pos_in : in_channel -> int64 = "caml_ml_pos_in_64"
    dehors in_channel_length : in_channel -> int64 = "caml_ml_channel_size_64"
  fin

(* References *)

type 'a ref = { modifiable contents : 'a }
dehors ref : 'a -> 'a ref = "%makemutable"
dehors ( ! ) : 'a ref -> 'a = "%field0"
dehors ( := ) : 'a ref -> 'a -> unit = "%setfield0"
dehors incr : int ref -> unit = "%incr"
dehors decr : int ref -> unit = "%decr"

(* Formats *)
type ('a, 'b, 'c, 'd) format4 = ('a, 'b, 'c, 'c, 'c, 'd) format6

type ('a, 'b, 'c) format = ('a, 'b, 'c, 'c) format4

dehors format_of_string :
 ('a, 'b, 'c, 'd, 'e, 'f) format6 ->
 ('a, 'b, 'c, 'd, 'e, 'f) format6 = "%identity"

dehors format_to_string :
 ('a, 'b, 'c, 'd, 'e, 'f) format6 -> string = "%identity"
dehors string_to_format :
 string -> ('a, 'b, 'c, 'd, 'e, 'f) format6 = "%identity"

soit (( ^^ ) :
      ('a, 'b, 'c, 'd, 'e, 'f) format6 ->
      ('f, 'b, 'c, 'e, 'g, 'h) format6 ->
      ('a, 'b, 'c, 'd, 'g, 'h) format6) =
  fonc fmt1 fmt2 ->
    string_to_format (format_to_string fmt1 ^ "%," ^ format_to_string fmt2)
;;

soit string_of_format fmt =
  soit s = format_to_string fmt dans
  soit l = string_length s dans
  soit r = string_create l dans
  string_blit s 0 r 0 l;
  r

(* Miscellaneous *)

dehors sys_exit : int -> 'a = "caml_sys_exit"

soit exit_function = ref flush_all

soit at_exit f =
  soit g = !exit_function dans
  exit_function := (fonc () -> f(); g())

soit do_at_exit () = (!exit_function) ()

soit exit retcode =
  do_at_exit ();
  sys_exit retcode

soit _ = register_named_value "Pervasives.do_at_exit" do_at_exit
