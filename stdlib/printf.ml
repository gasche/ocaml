(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*  Xavier Leroy and Pierre Weis, projet Cristal, INRIA Rocquencourt   *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

dehors format_float: string -> float -> string
  = "caml_format_float"
dehors format_int: string -> int -> string
  = "caml_format_int"
dehors format_int32: string -> int32 -> string
  = "caml_int32_format"
dehors format_nativeint: string -> nativeint -> string
  = "caml_nativeint_format"
dehors format_int64: string -> int64 -> string
  = "caml_int64_format"

module Sformat = struct

  type index;;

  dehors unsafe_index_of_int : int -> index = "%identity"
  ;;
  soit index_of_int i =
    si i >= 0 alors unsafe_index_of_int i
    sinon failwith ("Sformat.index_of_int: argument négatif " ^ string_of_int i)
  ;;
  dehors int_of_index : index -> int = "%identity"
  ;;

  soit add_int_index i idx = index_of_int (i + int_of_index idx);;
  soit succ_index = add_int_index 1;;
  (* Literal position are one-based (hence pred p instead of p). *)
  soit index_of_literal_position p = index_of_int (pred p);;

  dehors length : ('a, 'b, 'c, 'd, 'e, 'f) format6 -> int
    = "%string_length"
  ;;
  dehors get : ('a, 'b, 'c, 'd, 'e, 'f) format6 -> int -> char
    = "%string_safe_get"
  ;;
  dehors unsafe_get : ('a, 'b, 'c, 'd, 'e, 'f) format6 -> int -> char
    = "%string_unsafe_get"
  ;;
  dehors unsafe_to_string : ('a, 'b, 'c, 'd, 'e, 'f) format6 -> string
    = "%identity"
  ;;
  soit sub fmt idx len =
    String.sub (unsafe_to_string fmt) (int_of_index idx) len
  ;;
  soit to_string fmt = sub fmt (unsafe_index_of_int 0) (length fmt)
  ;;

fin
;;

soit bad_conversion sfmt i c =
  invalid_arg
    ("Printf: conversion incorrecte %" ^ String.make 1 c ^ ", au caractère numéro " ^
     string_of_int i ^ " dans la chaîne de format \'" ^ sfmt ^ "\'")
;;

soit bad_conversion_format fmt i c =
  bad_conversion (Sformat.to_string fmt) i c
;;

soit incomplete_format fmt =
  invalid_arg
    ("Printf: fin de chaîne de format prématurée \'" ^
     Sformat.to_string fmt ^ "\'")
;;

(* Parses a string conversion to return the specified length and the
   padding direction. *)
soit parse_string_conversion sfmt =
  soit rec parse neg i =
    si i >= String.length sfmt alors (0, neg) sinon
    filtre String.unsafe_get sfmt i avec
    | '1'..'9' ->
      (int_of_string
         (String.sub sfmt i (String.length sfmt - i - 1)),
       neg)
    | '-' ->
      parse vrai (succ i)
    | _ ->
      parse neg (succ i) dans
  essaie parse faux 1 avec
  | Failure _ -> bad_conversion sfmt 0 's'
;;

(* Pad a (sub) string into a blank string of length [p],
   on the right if [neg] is true, on the left otherwise. *)
soit pad_string pad_char p neg s i len =
  si p = len && i = 0 alors s sinon
  si p <= len alors String.sub s i len sinon
  soit res = String.make p pad_char dans
  si neg
  alors String.blit s i res 0 len
  sinon String.blit s i res (p - len) len;
  res
;;

(* Format a string given a %s format, e.g. %40s or %-20s.
   To do ?: ignore other flags (#, +, etc). *)
soit format_string sfmt s =
  soit (p, neg) = parse_string_conversion sfmt dans
  pad_string ' ' p neg s 0 (String.length s)
;;

(* Extract a format string out of [fmt] between [start] and [stop] inclusive.
   ['*'] in the format are replaced by integers taken from the [widths] list.
   [extract_format] returns a string which is the string representation of
   the resulting format string. *)
soit extract_format fmt start stop widths =
  soit skip_positional_spec start =
    filtre Sformat.unsafe_get fmt start avec
    | '0'..'9' ->
      soit rec skip_int_literal i =
        filtre Sformat.unsafe_get fmt i avec
        | '0'..'9' -> skip_int_literal (succ i)
        | '$' -> succ i
        | _ -> start dans
      skip_int_literal (succ start)
    | _ -> start dans
  soit start = skip_positional_spec (succ start) dans
  soit b = Buffer.create (stop - start + 10) dans
  Buffer.add_char b '%';
  soit rec fill_format i widths =
    si i <= stop alors
      filtre (Sformat.unsafe_get fmt i, widths) avec
      | ('*', h :: t) ->
        Buffer.add_string b (string_of_int h);
        soit i = skip_positional_spec (succ i) dans
        fill_format i t
      | ('*', []) ->
        affirme faux (* Should not happen since this is ill-typed. *)
      | (c, _) ->
        Buffer.add_char b c;
        fill_format (succ i) widths dans
  fill_format start (List.rev widths);
  Buffer.contents b
;;

soit extract_format_int conv fmt start stop widths =
  soit sfmt = extract_format fmt start stop widths dans
  filtre conv avec
  | 'n' | 'N' ->
    sfmt.[String.length sfmt - 1] <- 'u';
    sfmt
  | _ -> sfmt
;;

soit extract_format_float conv fmt start stop widths =
  soit sfmt = extract_format fmt start stop widths dans
  filtre conv avec
  | 'F' ->
    sfmt.[String.length sfmt - 1] <- 'g';
    sfmt
  | _ -> sfmt
;;

(* Returns the position of the next character following the meta format
   string, starting from position [i], inside a given format [fmt].
   According to the character [conv], the meta format string is
   enclosed by the delimiters %{ and %} (when [conv = '{']) or %( and
   %) (when [conv = '(']). Hence, [sub_format] returns the index of
   the character following the [')'] or ['}'] that ends the meta format,
   according to the character [conv]. *)
soit sub_format incomplete_format bad_conversion_format conv fmt i =
  soit len = Sformat.length fmt dans
  soit rec sub_fmt c i =
    soit close = si c = '(' alors ')' sinon (* '{' *) '}' dans
    soit rec sub j =
       si j >= len alors incomplete_format fmt sinon
       filtre Sformat.get fmt j avec
       | '%' -> sub_sub (succ j)
       | _ -> sub (succ j)
    et sub_sub j =
       si j >= len alors incomplete_format fmt sinon
       filtre Sformat.get fmt j avec
       | '(' | '{' tel c ->
         soit j = sub_fmt c (succ j) dans
         sub (succ j)
       | '}' | ')' tel c ->
         si c = close alors succ j sinon bad_conversion_format fmt i c
       | _ -> sub (succ j) dans
    sub i dans
  sub_fmt conv i
;;

soit sub_format_for_printf conv =
  sub_format incomplete_format bad_conversion_format conv
;;

soit iter_on_format_args fmt add_conv add_char =

  soit lim = Sformat.length fmt - 1 dans

  soit rec scan_flags skip i =
    si i > lim alors incomplete_format fmt sinon
    filtre Sformat.unsafe_get fmt i avec
    | '*' -> scan_flags skip (add_conv skip i 'i')
 (* | '$' -> scan_flags skip (succ i) *** PR#4321 *)
    | '#' | '-' | ' ' | '+' -> scan_flags skip (succ i)
    | '_' -> scan_flags vrai (succ i)
    | '0'..'9'
    | '.' -> scan_flags skip (succ i)
    | _ -> scan_conv skip i
  et scan_conv skip i =
    si i > lim alors incomplete_format fmt sinon
    filtre Sformat.unsafe_get fmt i avec
    | '%' | '@' | '!' | ',' -> succ i
    | 's' | 'S' | '[' -> add_conv skip i 's'
    | 'c' | 'C' -> add_conv skip i 'c'
    | 'd' | 'i' |'o' | 'u' | 'x' | 'X' | 'N' -> add_conv skip i 'i'
    | 'f' | 'e' | 'E' | 'g' | 'G' | 'F' -> add_conv skip i 'f'
    | 'B' | 'b' -> add_conv skip i 'B'
    | 'a' | 'r' | 't' tel conv -> add_conv skip i conv
    | 'l' | 'n' | 'L' tel conv ->
      soit j = succ i dans
      si j > lim alors add_conv skip i 'i' sinon début
        filtre Sformat.get fmt j avec
        | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' ->
          add_char (add_conv skip i conv) 'i'
        | _ -> add_conv skip i 'i' fin
    | '{' tel conv ->
      (* Just get a regular argument, skipping the specification. *)
      soit i = add_conv skip i conv dans
      (* To go on, find the index of the next char after the meta format. *)
      soit j = sub_format_for_printf conv fmt i dans
      (* Add the meta specification to the summary anyway. *)
      soit rec loop i =
        si i < j - 2 alors loop (add_char i (Sformat.get fmt i)) dans
      loop i;
      (* Go on, starting at the closing brace to properly close the meta
         specification in the summary. *)
      scan_conv skip (j - 1)
    | '(' tel conv ->
      (* Use the static format argument specification instead of
         the runtime format argument value: they must have the same type
         anyway. *)
      scan_fmt (add_conv skip i conv)
    | '}' | ')' tel conv -> add_conv skip i conv
    | conv -> bad_conversion_format fmt i conv

  et scan_fmt i =
    si i < lim alors
     si Sformat.get fmt i = '%'
     alors scan_fmt (scan_flags faux (succ i))
     sinon scan_fmt (succ i)
    sinon i dans

  ignore (scan_fmt 0)
;;

(* Returns a string that summarizes the typing information that a given
   format string contains.
   For instance, [summarize_format_type "A number %d\n"] is "%i".
   It also checks the well-formedness of the format string. *)
soit summarize_format_type fmt =
  soit len = Sformat.length fmt dans
  soit b = Buffer.create len dans
  soit add_char i c = Buffer.add_char b c; succ i dans
  soit add_conv skip i c =
    si skip alors Buffer.add_string b "%_" sinon Buffer.add_char b '%';
    add_char i c dans
  iter_on_format_args fmt add_conv add_char;
  Buffer.contents b
;;

module Ac = struct
  type ac = {
    modifiable ac_rglr : int;
    modifiable ac_skip : int;
    modifiable ac_rdrs : int;
  }
fin
;;

ouvre Ac;;

(* Computes the number of arguments of a format (including the flag
   arguments if any). *)
soit ac_of_format fmt =
  soit ac = { ac_rglr = 0; ac_skip = 0; ac_rdrs = 0; } dans
  soit incr_ac skip c =
    soit inc = si c = 'a' alors 2 sinon 1 dans
    si c = 'r' alors ac.ac_rdrs <- ac.ac_rdrs + 1;
    si skip
    alors ac.ac_skip <- ac.ac_skip + inc
    sinon ac.ac_rglr <- ac.ac_rglr + inc dans
  soit add_conv skip i c =
    (* Just finishing a meta format: no additional argument to record. *)
    si c <> ')' && c <> '}' alors incr_ac skip c;
    succ i
  et add_char i _ = succ i dans

  iter_on_format_args fmt add_conv add_char;
  ac
;;

soit count_printing_arguments_of_format fmt =
  soit ac = ac_of_format fmt dans
  (* For printing, only the regular arguments have to be counted. *)
  ac.ac_rglr
;;

soit list_iter_i f l =
  soit rec loop i = fonction
  | [] -> ()
  | [x] -> f i x (* Tail calling [f] *)
  | x :: xs -> f i x; loop (succ i) xs dans
  loop 0 l
;;

(* 'Abstracting' version of kprintf: returns a (curried) function that
   will print when totally applied.
   Note: in the following, we are careful not to be badly caught
   by the compiler optimizations for the representation of arrays. *)
soit kapr kpr fmt =
  filtre count_printing_arguments_of_format fmt avec
  | 0 -> kpr fmt [||]
  | 1 -> Obj.magic (fonc x ->
      soit a = Array.make 1 (Obj.repr 0) dans
      a.(0) <- x;
      kpr fmt a)
  | 2 -> Obj.magic (fonc x y ->
      soit a = Array.make 2 (Obj.repr 0) dans
      a.(0) <- x; a.(1) <- y;
      kpr fmt a)
  | 3 -> Obj.magic (fonc x y z ->
      soit a = Array.make 3 (Obj.repr 0) dans
      a.(0) <- x; a.(1) <- y; a.(2) <- z;
      kpr fmt a)
  | 4 -> Obj.magic (fonc x y z t ->
      soit a = Array.make 4 (Obj.repr 0) dans
      a.(0) <- x; a.(1) <- y; a.(2) <- z;
      a.(3) <- t;
      kpr fmt a)
  | 5 -> Obj.magic (fonc x y z t u ->
      soit a = Array.make 5 (Obj.repr 0) dans
      a.(0) <- x; a.(1) <- y; a.(2) <- z;
      a.(3) <- t; a.(4) <- u;
      kpr fmt a)
  | 6 -> Obj.magic (fonc x y z t u v ->
      soit a = Array.make 6 (Obj.repr 0) dans
      a.(0) <- x; a.(1) <- y; a.(2) <- z;
      a.(3) <- t; a.(4) <- u; a.(5) <- v;
      kpr fmt a)
  | nargs ->
    soit rec loop i args =
      si i >= nargs alors
        soit a = Array.make nargs (Obj.repr 0) dans
        list_iter_i (fonc i arg -> a.(nargs - i - 1) <- arg) args;
        kpr fmt a
      sinon Obj.magic (fonc x -> loop (succ i) (x :: args)) dans
    loop 0 []
;;

type positional_specification =
   | Spec_none | Spec_index de Sformat.index
;;

(* To scan an optional positional parameter specification,
   i.e. an integer followed by a [$].

   Calling [got_spec] with appropriate arguments, we 'return' a positional
   specification and an index to go on scanning the [fmt] format at hand.

   Note that this is optimized for the regular case, i.e. no positional
   parameter, since in this case we juste 'return' the constant
   [Spec_none]; in case we have a positional parameter, we 'return' a
   [Spec_index] [positional_specification] which is a bit more costly.

   Note also that we do not support [*$] specifications, since this would
   lead to type checking problems: a [*$] positional specification means
   'take the next argument to [printf] (which must be an integer value)',
   name this integer value $n$; [*$] now designates parameter $n$.

   Unfortunately, the type of a parameter specified via a [*$] positional
   specification should be the type of the corresponding argument to
   [printf], hence this should be the type of the $n$-th argument to [printf]
   with $n$ being the {\em value} of the integer argument defining [*]; we
   clearly cannot statically guess the value of this parameter in the general
   case. Put it another way: this means type dependency, which is completely
   out of scope of the OCaml type algebra. *)

soit scan_positional_spec fmt got_spec i =
  filtre Sformat.unsafe_get fmt i avec
  | '0'..'9' tel d ->
    soit rec get_int_literal accu j =
      filtre Sformat.unsafe_get fmt j avec
      | '0'..'9' tel d ->
        get_int_literal (10 * accu + (int_of_char d - 48)) (succ j)
      | '$' ->
        si accu = 0 alors
          failwith "printf: spécification positionnelle incorrecte (0)." sinon
        got_spec (Spec_index (Sformat.index_of_literal_position accu)) (succ j)
      (* Not a positional specification: tell so the caller, and go back to
         scanning the format from the original [i] position we were called at
         first. *)
      | _ -> got_spec Spec_none i dans
    get_int_literal (int_of_char d - 48) (succ i)
  (* No positional specification: tell so the caller, and go back to scanning
     the format from the original [i] position. *)
  | _ -> got_spec Spec_none i
;;

(* Get the index of the next argument to printf, according to the given
   positional specification. *)
soit next_index spec n =
  filtre spec avec
  | Spec_none -> Sformat.succ_index n
  | Spec_index _ -> n
;;

(* Get the index of the actual argument to printf, according to its
   optional positional specification. *)
soit get_index spec n =
  filtre spec avec
  | Spec_none -> n
  | Spec_index p -> p
;;

(* Format a float argument as a valid OCaml lexeme. *)
soit format_float_lexeme =

  (* To be revised: this procedure should be a unique loop that performs the
     validity check and the string lexeme modification at the same time.
     Otherwise, it is too difficult to handle the strange padding facilities
     given by printf. Let alone handling the correct widths indication,
     knowing that we have sometime to add a '.' at the end of the result!
  *)

  soit make_valid_float_lexeme s =
    (* Check if s is already a valid lexeme:
       in this case do nothing,
       otherwise turn s into a valid OCaml lexeme. *)
    soit l = String.length s dans
    soit rec valid_float_loop i =
      si i >= l alors s ^ "." sinon
      filtre s.[i] avec
      (* Sure, this is already a valid float lexeme. *)
      | '.' | 'e' | 'E' -> s
      | _ -> valid_float_loop (i + 1) dans

    valid_float_loop 0 dans

  (fonc sfmt x ->
   filtre classify_float x avec
   | FP_normal | FP_subnormal | FP_zero ->
       make_valid_float_lexeme (format_float sfmt x)
   | FP_infinite ->
       si x < 0.0 alors "moins l'infini" sinon "l'infini"
   | FP_nan ->
       "pas un nombre")
;;

(* Decode a format string and act on it.
   [fmt] is the [printf] format string, and [pos] points to a [%] character in
   the format string.
   After consuming the appropriate number of arguments and formatting
   them, one of the following five continuations described below is called:

   - [cont_s] for outputting a string
     (arguments: arg num, string, next pos)
   - [cont_a] for performing a %a action
     (arguments: arg num, fn, arg, next pos)
   - [cont_t] for performing a %t action
     (arguments: arg num, fn, next pos)
   - [cont_f] for performing a flush action
     (arguments: arg num, next pos)
   - [cont_m] for performing a %( action
     (arguments: arg num, sfmt, next pos)

   "arg num" is the index in array [args] of the next argument to [printf].
   "next pos" is the position in [fmt] of the first character following
   the %conversion specification in [fmt]. *)

(* Note: here, rather than test explicitly against [Sformat.length fmt]
   to detect the end of the format, we use [Sformat.unsafe_get] and
   rely on the fact that we'll get a "null" character if we access
   one past the end of the string.  These "null" characters are then
   caught by the [_ -> bad_conversion] clauses below.
   Don't do this at home, kids. *)
soit scan_format fmt args n pos cont_s cont_a cont_t cont_f cont_m =

  soit get_arg spec n =
    Obj.magic (args.(Sformat.int_of_index (get_index spec n))) dans

  soit rec scan_positional n widths i =
    soit got_spec spec i = scan_flags spec n widths i dans
    scan_positional_spec fmt got_spec i

  et scan_flags spec n widths i =
    filtre Sformat.unsafe_get fmt i avec
    | '*' ->
      soit got_spec wspec i =
        soit (width : int) = get_arg wspec n dans
        scan_flags spec (next_index wspec n) (width :: widths) i dans
      scan_positional_spec fmt got_spec (succ i)
    | '0'..'9'
    | '.' | '#' | '-' | ' ' | '+' -> scan_flags spec n widths (succ i)
    | _ -> scan_conv spec n widths i

  et scan_conv spec n widths i =
    filtre Sformat.unsafe_get fmt i avec
    | '%' | '@' tel c ->
      cont_s n (String.make 1 c) (succ i)
    | '!' -> cont_f n (succ i)
    | ',' -> cont_s n "" (succ i)
    | 's' | 'S' tel conv ->
      soit (x : string) = get_arg spec n dans
      soit x = si conv = 's' alors x sinon "\"" ^ String.escaped x ^ "\"" dans
      soit s =
        (* Optimize for common case %s *)
        si i = succ pos alors x sinon
        format_string (extract_format fmt pos i widths) x dans
      cont_s (next_index spec n) s (succ i)
    | '[' tel conv ->
      bad_conversion_format fmt i conv
    | 'c' | 'C' tel conv ->
      soit (x : char) = get_arg spec n dans
      soit s =
        si conv = 'c' alors String.make 1 x sinon "'" ^ Char.escaped x ^ "'" dans
      cont_s (next_index spec n) s (succ i)
    | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' | 'N' tel conv ->
      soit (x : int) = get_arg spec n dans
      soit s =
        format_int (extract_format_int conv fmt pos i widths) x dans
      cont_s (next_index spec n) s (succ i)
    | 'f' | 'e' | 'E' | 'g' | 'G' ->
      soit (x : float) = get_arg spec n dans
      soit s = format_float (extract_format fmt pos i widths) x dans
      cont_s (next_index spec n) s (succ i)
    | 'F' tel conv ->
      soit (x : float) = get_arg spec n dans
      soit s =
        format_float_lexeme
          (si widths = []
           alors "%.12g"
           sinon extract_format_float conv fmt pos i widths)
          x dans
      cont_s (next_index spec n) s (succ i)
    | 'B' | 'b' ->
      soit (x : bool) = get_arg spec n dans
      cont_s (next_index spec n) (string_of_bool x) (succ i)
    | 'a' ->
      soit printer = get_arg spec n dans
      (* If the printer spec is Spec_none, go on as usual.
         If the printer spec is Spec_index p,
         printer's argument spec is Spec_index (succ_index p). *)
      soit n = Sformat.succ_index (get_index spec n) dans
      soit arg = get_arg Spec_none n dans
      cont_a (next_index spec n) printer arg (succ i)
    | 'r' tel conv ->
      bad_conversion_format fmt i conv
    | 't' ->
      soit printer = get_arg spec n dans
      cont_t (next_index spec n) printer (succ i)
    | 'l' | 'n' | 'L' tel conv ->
      début filtre Sformat.unsafe_get fmt (succ i) avec
      | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' ->
        soit i = succ i dans
        soit s =
          filtre conv avec
          | 'l' ->
            soit (x : int32) = get_arg spec n dans
            format_int32 (extract_format fmt pos i widths) x
          | 'n' ->
            soit (x : nativeint) = get_arg spec n dans
            format_nativeint (extract_format fmt pos i widths) x
          | _ ->
            soit (x : int64) = get_arg spec n dans
            format_int64 (extract_format fmt pos i widths) x dans
        cont_s (next_index spec n) s (succ i)
      | _ ->
        soit (x : int) = get_arg spec n dans
        soit s = format_int (extract_format_int 'n' fmt pos i widths) x dans
        cont_s (next_index spec n) s (succ i)
      fin
    | '{' | '(' tel conv (* ')' '}' *) ->
      soit (xf : ('a, 'b, 'c, 'd, 'e, 'f) format6) = get_arg spec n dans
      soit i = succ i dans
      soit i = sub_format_for_printf conv fmt i dans
      si conv = '{' (* '}' *) alors
        (* Just print the format argument as a specification. *)
        cont_s
          (next_index spec n)
          (summarize_format_type xf)
          i sinon
        (* Use the format argument instead of the format specification. *)
        cont_m (next_index spec n) xf i
    | (* '(' *) ')' ->
      cont_s n "" (succ i)
    | conv ->
      bad_conversion_format fmt i conv dans

  scan_positional n [] (succ pos)
;;

soit mkprintf to_s get_out outc outs flush k fmt =

  (* [out] is global to this definition of [pr], and must be shared by all its
     recursive calls (if any). *)
  soit out = get_out fmt dans
  soit outc c = outc out c dans
  soit outs s = outs out s dans

  soit rec pr k n fmt v =

    soit len = Sformat.length fmt dans

    soit rec doprn n i =
       si i >= len alors Obj.magic (k out) sinon
       filtre Sformat.unsafe_get fmt i avec
       | '%' -> scan_format fmt v n i cont_s cont_a cont_t cont_f cont_m
       |  c  -> outc c; doprn n (succ i)

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
          (count_printing_arguments_of_format xf) n dans
      pr (Obj.magic (fonc _ -> doprn m i)) n xf v dans

    doprn n 0 dans

  soit kpr = pr k (Sformat.index_of_int 0) dans

  kapr kpr fmt
;;

(**************************************************************

  Defining [fprintf] and various flavors of [fprintf].

 **************************************************************)

soit kfprintf k oc =
  mkprintf faux (fonc _ -> oc) output_char output_string flush k
;;
soit ikfprintf k oc = kapr (fonc _ _ -> Obj.magic (k oc));;

soit fprintf oc = kfprintf ignore oc;;
soit ifprintf oc = ikfprintf ignore oc;;
soit printf fmt = fprintf stdout fmt;;
soit eprintf fmt = fprintf stderr fmt;;

soit kbprintf k b =
  mkprintf faux (fonc _ -> b) Buffer.add_char Buffer.add_string ignore k
;;
soit bprintf b = kbprintf ignore b;;

soit get_buff fmt =
  soit len = 2 * Sformat.length fmt dans
  Buffer.create len
;;

soit get_contents b =
  soit s = Buffer.contents b dans
  Buffer.clear b;
  s
;;

soit get_cont k b = k (get_contents b);;

soit ksprintf k =
  mkprintf vrai get_buff Buffer.add_char Buffer.add_string ignore (get_cont k)
;;

soit sprintf fmt = ksprintf (fonc s -> s) fmt;;

(**************************************************************

  Deprecated stuff.

 **************************************************************)

soit kprintf = ksprintf;;

(* For OCaml system internal use only: needed to implement modules [Format]
  and [Scanf]. *)

module CamlinternalPr = struct

  module Sformat = Sformat;;

  module Tformat = struct

    type ac =
      Ac.ac = {
      modifiable ac_rglr : int;
      modifiable ac_skip : int;
      modifiable ac_rdrs : int;
    }
    ;;

    soit ac_of_format = ac_of_format;;

    soit count_printing_arguments_of_format =
      count_printing_arguments_of_format;;

    soit sub_format = sub_format;;

    soit summarize_format_type = summarize_format_type;;

    soit scan_format = scan_format;;

    soit kapr = kapr;;

  fin
  ;;

fin
;;
