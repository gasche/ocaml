(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Pierre Weis, projet Cristal, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* The run-time library for scanners. *)

(* Scanning buffers. *)
module type SCANNING = sig

  type in_channel;;

  type scanbuf = in_channel;;

  type file_name = string;;

  val stdin : in_channel;;
  (* The scanning buffer reading from [Pervasives.stdin].
      [stdib] is equivalent to [Scanning.from_channel Pervasives.stdin]. *)

  val stdib : in_channel;;
  (* An alias for [Scanf.stdin], the scanning buffer reading from
     [Pervasives.stdin]. *)

  val next_char : scanbuf -> char;;
  (* [Scanning.next_char ib] advance the scanning buffer for
      one character.
      If no more character can be read, sets a end of file condition and
      returns '\000'. *)

  val invalidate_current_char : scanbuf -> unit;;
  (* [Scanning.invalidate_current_char ib] mark the current_char as already
      scanned. *)

  val peek_char : scanbuf -> char;;
  (* [Scanning.peek_char ib] returns the current char available in
      the buffer or reads one if necessary (when the current character is
      already scanned).
      If no character can be read, sets an end of file condition and
      returns '\000'. *)

  val checked_peek_char : scanbuf -> char;;
  (* Same as above but always returns a valid char or fails:
      instead of returning a null char when the reading method of the
      input buffer has reached an end of file, the function raises exception
      [End_of_file]. *)

  val store_char : int -> scanbuf -> char -> int;;
  (* [Scanning.store_char lim ib c] adds [c] to the token buffer
      of the scanning buffer. It also advances the scanning buffer for one
      character and returns [lim - 1], indicating the new limit
      for the length of the current token. *)

  val skip_char : int -> scanbuf -> int;;
  (* [Scanning.skip_char lim ib] ignores the current character. *)

  val ignore_char : int -> scanbuf -> int;;
  (* [Scanning.ignore_char ib lim] ignores the current character and
     decrements the limit. *)

  val token : scanbuf -> string;;
  (* [Scanning.token ib] returns the string stored into the token
      buffer of the scanning buffer: it returns the token matched by the
      format. *)

  val reset_token : scanbuf -> unit;;
  (* [Scanning.reset_token ib] resets the token buffer of
      the given scanning buffer. *)

  val char_count : scanbuf -> int;;
  (* [Scanning.char_count ib] returns the number of characters
      read so far from the given buffer. *)

  val line_count : scanbuf -> int;;
  (* [Scanning.line_count ib] returns the number of new line
      characters read so far from the given buffer. *)

  val token_count : scanbuf -> int;;
  (* [Scanning.token_count ib] returns the number of tokens read
      so far from [ib]. *)

  val eof : scanbuf -> bool;;
  (* [Scanning.eof ib] returns the end of input condition
      of the given buffer. *)

  val end_of_input : scanbuf -> bool;;
  (* [Scanning.end_of_input ib] tests the end of input condition
      of the given buffer (if no char has ever been read, an attempt to
      read one is performed). *)

  val beginning_of_input : scanbuf -> bool;;
  (* [Scanning.beginning_of_input ib] tests the beginning of input
      condition of the given buffer. *)

  val name_of_input : scanbuf -> string;;
  (* [Scanning.name_of_input ib] returns the name of the character
      source for input buffer [ib]. *)

  val open_in : file_name -> in_channel;;
  val open_in_bin : file_name -> in_channel;;
  val from_file : file_name -> in_channel;;
  val from_file_bin : file_name -> in_channel;;
  val from_string : string -> in_channel;;
  val from_function : (unit -> char) -> in_channel;;
  val from_channel : Pervasives.in_channel -> in_channel;;

  val close_in : in_channel -> unit;;

fin
;;

module Scanning : SCANNING = struct

  (* The run-time library for scanf. *)
  type in_channel_name =
    | From_file de string * Pervasives.in_channel
    | From_string
    | From_function
    | From_channel de Pervasives.in_channel
  ;;

  type in_channel = {
    modifiable eof : bool;
    modifiable current_char : char;
    modifiable current_char_is_valid : bool;
    modifiable char_count : int;
    modifiable line_count : int;
    modifiable token_count : int;
    modifiable get_next_char : unit -> char;
    tokbuf : Buffer.t;
    input_name : in_channel_name;
  }
  ;;

  type scanbuf = in_channel;;

  type file_name = string;;

  soit null_char = '\000';;

  (* Reads a new character from input buffer.  Next_char never fails,
     even in case of end of input: it then simply sets the end of file
     condition. *)
  soit next_char ib =
    essaie
      soit c = ib.get_next_char () dans
      ib.current_char <- c;
      ib.current_char_is_valid <- vrai;
      ib.char_count <- succ ib.char_count;
      si c = '\n' alors ib.line_count <- succ ib.line_count;
      c avec
    | End_of_file ->
      soit c = null_char dans
      ib.current_char <- c;
      ib.current_char_is_valid <- faux;
      ib.eof <- vrai;
      c
  ;;

  soit peek_char ib =
    si ib.current_char_is_valid alors ib.current_char sinon next_char ib;;

  (* Returns a valid current char for the input buffer. In particular
     no irrelevant null character (as set by [next_char] in case of end
     of input) is returned, since [End_of_file] is raised when
     [next_char] sets the end of file condition while trying to read a
     new character. *)
  soit checked_peek_char ib =
    soit c = peek_char ib dans
    si ib.eof alors raise End_of_file;
    c
  ;;

  soit end_of_input ib =
    ignore (peek_char ib);
    ib.eof
  ;;

  soit eof ib = ib.eof;;

  soit beginning_of_input ib = ib.char_count = 0;;
  soit name_of_input ib =
    filtre ib.input_name avec
    | From_file (fname, _ic) -> fname
    | From_string -> "unnamed character string"
    | From_function -> "unnamed function"
    | From_channel _ic -> "unnamed pervasives input channel"
  ;;

  soit char_count ib =
    si ib.current_char_is_valid alors ib.char_count - 1 sinon ib.char_count
  ;;
  soit line_count ib = ib.line_count;;
  soit reset_token ib = Buffer.reset ib.tokbuf;;
  soit invalidate_current_char ib = ib.current_char_is_valid <- faux;;

  soit token ib =
    soit tokbuf = ib.tokbuf dans
    soit tok = Buffer.contents tokbuf dans
    Buffer.clear tokbuf;
    ib.token_count <- succ ib.token_count;
    tok
  ;;

  soit token_count ib = ib.token_count;;

  soit skip_char width ib =
    invalidate_current_char ib;
    width
  ;;

  soit ignore_char width ib = skip_char (width - 1) ib;;

  soit store_char width ib c =
    Buffer.add_char ib.tokbuf c;
    ignore_char width ib
  ;;

  soit default_token_buffer_size = 1024;;

  soit create iname next = {
    eof = faux;
    current_char = null_char;
    current_char_is_valid = faux;
    char_count = 0;
    line_count = 0;
    token_count = 0;
    get_next_char = next;
    tokbuf = Buffer.create default_token_buffer_size;
    input_name = iname;
  }
  ;;

  soit from_string s =
    soit i = ref 0 dans
    soit len = String.length s dans
    soit next () =
      si !i >= len alors raise End_of_file sinon
      soit c = s.[!i] dans
      incr i;
      c dans
    create From_string next
  ;;

  soit from_function = create From_function;;

  (* Scanning from an input channel. *)

  (* Position of the problem:

     We cannot prevent the scanning mechanism to use one lookahead character,
     if needed by the semantics of the format string specifications (e.g. a
     trailing 'skip space' specification in the format string); in this case,
     the mandatory lookahead character is indeed read from the input and not
     used to return the token read. It is thus mandatory to be able to store
     an unused lookahead character somewhere to get it as the first character
     of the next scan.

     To circumvent this problem, all the scanning functions get a low level
     input buffer argument where they store the lookahead character when
     needed; additionally, the input buffer is the only source of character of
     a scanner. The [scanbuf] input buffers are defined in module {!Scanning}.

     Now we understand that it is extremely important that related successive
     calls to scanners indeed read from the same input buffer. In effect, if a
     scanner [scan1] is reading from [ib1] and stores an unused lookahead
     character [c1] into its input buffer [ib1], then another scanner [scan2]
     not reading from the same buffer [ib1] will miss the character [c],
     seemingly vanished in the air from the point of view of [scan2].

     This mechanism works perfectly to read from strings, from files, and from
     functions, since in those cases, allocating two buffers reading from the
     same source is unnatural.

     Still, there is a difficulty in the case of scanning from an input
     channel. In effect, when scanning from an input channel [ic], this channel
     may not have been allocated from within this library. Hence, it may be
     shared (two functions of the user's program may successively read from
     [ic]). This is highly error prone since, one of the function may seek the
     input channel, while the other function has still an unused lookahead
     character in its input buffer. In conclusion, you should never mix direct
     low level reading and high level scanning from the same input channel.

     This phenomenon of reading mess is even worse when one defines more than
     one scanning buffer reading from the same input channel
     [ic]. Unfortunately, we have no simple way to get rid of this problem
     (unless the basic input channel API is modified to offer a 'consider this
     char as unread' procedure to keep back the unused lookahead character as
     available in the input channel for further reading).

     To prevent some of the confusion the scanning buffer allocation function
     is a memo function that never allocates two different scanning buffers for
     the same input channel. This way, the user can naively perform successive
     call to [fscanf] below, without allocating a new scanning buffer at each
     invocation and hence preserving the expected semantics.

     As mentioned above, a more ambitious fix could be to change the input
     channel API to allow arbitrary mixing of direct and formatted reading from
     input channels. *)

  (* Perform bufferized input to improve efficiency. *)
  soit file_buffer_size = ref 1024;;

  (* The scanner closes the input channel at end of input. *)
  soit scan_close_at_end ic = close_in ic; raise End_of_file;;

  (* The scanner does not close the input channel at end of input:
     it just raises [End_of_file]. *)
  soit scan_raise_at_end _ic = raise End_of_file;;

  soit from_ic scan_close_ic iname ic =
    soit len = !file_buffer_size dans
    soit buf = String.create len dans
    soit i = ref 0 dans
    soit lim = ref 0 dans
    soit eof = ref faux dans
    soit next () =
      si !i < !lim alors début soit c = buf.[!i] dans incr i; c fin sinon
      si !eof alors raise End_of_file sinon début
        lim := input ic buf 0 len;
        si !lim = 0 alors début eof := vrai; scan_close_ic ic fin sinon début
          i := 1;
          buf.[0]
        fin
      fin dans
    create iname next
  ;;

  soit from_ic_close_at_end = from_ic scan_close_at_end;;

  (* The scanning buffer reading from [Pervasives.stdin].
     One could try to define [stdib] as a scanning buffer reading a character
     at a time (no bufferization at all), but unfortunately the top-level
     interaction would be wrong. This is due to some kind of
     'race condition' when reading from [Pervasives.stdin],
     since the interactive compiler and [scanf] will simultaneously read the
     material they need from [Pervasives.stdin]; then, confusion will result
     from what should be read by the top-level and what should be read
     by [scanf].
     This is even more complicated by the one character lookahead that [scanf]
     is sometimes obliged to maintain: the lookahead character will be
     available for the next ([scanf]) entry, seemingly coming from nowhere.
     Also no [End_of_file] is raised when reading from stdin: if not enough
     characters have been read, we simply ask to read more. *)
  soit stdin =
    from_ic scan_raise_at_end
      (From_file ("-", Pervasives.stdin)) Pervasives.stdin
  ;;

  soit stdib = stdin;;

  soit open_in fname =
    filtre fname avec
    | "-" -> stdin
    | fname ->
      soit ic = open_in fname dans
      from_ic_close_at_end (From_file (fname, ic)) ic
  ;;

  soit open_in_bin fname =
    filtre fname avec
    | "-" -> stdin
    | fname ->
      soit ic = open_in_bin fname dans
      from_ic_close_at_end (From_file (fname, ic)) ic
  ;;

  soit from_file = open_in;;
  soit from_file_bin = open_in_bin;;

  soit memo_from_ic =
    soit memo = ref [] dans
    (fonc scan_close_ic ic ->
     essaie List.assq ic !memo avec
     | Not_found ->
       soit ib = from_ic scan_close_ic (From_channel ic) ic dans
       memo := (ic, ib) :: !memo;
       ib)
  ;;

  soit from_channel = memo_from_ic scan_raise_at_end;;

  soit close_in ib =
    filtre ib.input_name avec
    | From_file (_fname, ic) -> Pervasives.close_in ic
    | From_string | From_function -> ()
    | From_channel ic -> Pervasives.close_in ic
  ;;

fin
;;

(* Formatted input functions. *)

type ('a, 'b, 'c, 'd) scanner =
     ('a, Scanning.in_channel, 'b, 'c, 'a -> 'd, 'd) format6 -> 'c
;;

dehors string_to_format :
 string -> ('a, 'b, 'c, 'd, 'e, 'f) format6 = "%identity"
;;

(* Reporting errors. *)
exception Scan_failure de string;;

soit bad_input s = raise (Scan_failure s);;

soit bad_input_escape c =
  bad_input (Printf.sprintf "illegal escape character %C" c)
;;

soit bad_token_length message =
  bad_input
    (Printf.sprintf
       "scanning of %s failed: \
        the specified length was too short for token" message)
;;

soit bad_end_of_input message =
  bad_input
    (Printf.sprintf
       "scanning of %s failed: \
        premature end of file occurred before end of token" message)
;;

soit int_of_width_opt = fonction
  | None -> max_int
  | Some width -> width
;;

soit int_of_prec_opt = fonction
  | None -> max_int
  | Some prec -> prec
;;

module Sformat = Printf.CamlinternalPr.Sformat;;
module Tformat = Printf.CamlinternalPr.Tformat;;

soit bad_conversion fmt i c =
  invalid_arg
    (Printf.sprintf
       "scanf: bad conversion %%%C, at char number %i \
        in format string \'%s\'" c i (Sformat.to_string fmt))
;;

soit incomplete_format fmt =
  invalid_arg
    (Printf.sprintf "scanf: premature end of format string \'%s\'"
       (Sformat.to_string fmt))
;;

soit bad_float () =
  bad_input "no dot or exponent part found in float token"
;;

soit character_mismatch_err c ci =
  Printf.sprintf "looking for %C, found %C" c ci
;;

soit character_mismatch c ci =
  bad_input (character_mismatch_err c ci)
;;

soit format_mismatch_err fmt1 fmt2 =
  Printf.sprintf
    "format read \'%s\' does not match specification \'%s\'" fmt1 fmt2
;;

soit format_mismatch fmt1 fmt2 = bad_input (format_mismatch_err fmt1 fmt2);;

(* Checking that 2 format strings are type compatible. *)
soit compatible_format_type fmt1 fmt2 =
  Tformat.summarize_format_type (string_to_format fmt1) =
  Tformat.summarize_format_type (string_to_format fmt2);;

(* Checking that [c] is indeed in the input, then skips it.
   In this case, the character [c] has been explicitly specified in the
   format as being mandatory in the input; hence we should fail with
   End_of_file in case of end_of_input. (Remember that Scan_failure is raised
   only when (we can prove by evidence) that the input does not match the
   format string given. We must thus differentiate End_of_file as an error
   due to lack of input, and Scan_failure which is due to provably wrong
   input. I am not sure this is worth the burden: it is complex and somehow
   subliminal; should be clearer to fail with Scan_failure "Not enough input
   to complete scanning"!)

   That's why, waiting for a better solution, we use checked_peek_char here.
   We are also careful to treat "\r\n" in the input as an end of line marker:
   it always matches a '\n' specification in the input format string. *)
soit rec check_char ib c =
  soit ci = Scanning.checked_peek_char ib dans
  si ci = c alors Scanning.invalidate_current_char ib sinon début
    filtre ci avec
    | '\r' quand c = '\n' ->
      Scanning.invalidate_current_char ib; check_char ib '\n'
    | _ -> character_mismatch c ci
  fin
;;

(* Checks that the current char is indeed one of the stopper characters,
   then skips it.
   Be careful that if ib has no more character this procedure should
   just do nothing (since %s@c defaults to the entire rest of the
   buffer, when no character c can be found in the input). *)
soit ignore_stoppers stps ib =
  si stps <> [] && not (Scanning.eof ib) alors
  soit ci = Scanning.peek_char ib dans
  si List.memq ci stps alors Scanning.invalidate_current_char ib sinon
  soit sr = String.concat "" (List.map (String.make 1) stps) dans
  bad_input
    (Printf.sprintf "looking for one of range %S, found %C" sr ci)
;;

(* Extracting tokens from the output token buffer. *)

soit token_char ib = (Scanning.token ib).[0];;

soit token_string = Scanning.token;;

soit token_bool ib =
  filtre Scanning.token ib avec
  | "true" -> vrai
  | "false" -> faux
  | s -> bad_input (Printf.sprintf "invalid boolean %S" s)
;;

(* Extract an integer literal token.
   Since the functions Pervasives.*int*_of_string do not accept a leading +,
   we skip it if necessary. *)
soit token_int_literal conv ib =
  soit tok =
    filtre conv avec
    | 'd' | 'i' | 'u' -> Scanning.token ib
    | 'o' -> "0o" ^ Scanning.token ib
    | 'x' | 'X' -> "0x" ^ Scanning.token ib
    | 'b' -> "0b" ^ Scanning.token ib
    | _ -> affirme faux dans
  soit l = String.length tok dans
  si l = 0 || tok.[0] <> '+' alors tok sinon String.sub tok 1 (l - 1)
;;

(* All the functions that convert a string to a number raise the exception
   Failure when the conversion is not possible.
   This exception is then trapped in [kscanf]. *)
soit token_int conv ib = int_of_string (token_int_literal conv ib);;

soit token_float ib = float_of_string (Scanning.token ib);;

(* To scan native ints, int32 and int64 integers.
   We cannot access to conversions to/from strings for those types,
   Nativeint.of_string, Int32.of_string, and Int64.of_string,
   since those modules are not available to [Scanf].
   However, we can bind and use the corresponding primitives that are
   available in the runtime. *)
dehors nativeint_of_string : string -> nativeint
  = "caml_nativeint_of_string"
;;
dehors int32_of_string : string -> int32
  = "caml_int32_of_string"
;;
dehors int64_of_string : string -> int64
  = "caml_int64_of_string"
;;

soit token_nativeint conv ib = nativeint_of_string (token_int_literal conv ib);;
soit token_int32 conv ib = int32_of_string (token_int_literal conv ib);;
soit token_int64 conv ib = int64_of_string (token_int_literal conv ib);;

(* Scanning numbers. *)

(* Digits scanning functions suppose that one character has been checked and
   is available, since they return at end of file with the currently found
   token selected.

   Put it in another way, the digits scanning functions scan for a possibly
   empty sequence of digits, (hence, a successful scanning from one of those
   functions does not imply that the token is a well-formed number: to get a
   true number, it is mandatory to check that at least one valid digit is
   available before calling one of the digit scanning functions). *)

(* The decimal case is treated especially for optimization purposes. *)
soit rec scan_decimal_digits width ib =
  si width = 0 alors width sinon
  soit c = Scanning.peek_char ib dans
  si Scanning.eof ib alors width sinon
  filtre c avec
  | '0' .. '9' tel c ->
    soit width = Scanning.store_char width ib c dans
    scan_decimal_digits width ib
  | '_' ->
    soit width = Scanning.ignore_char width ib dans
    scan_decimal_digits width ib
  | _ -> width
;;

soit scan_decimal_digits_plus width ib =
  si width = 0 alors bad_token_length "decimal digits" sinon
  soit c = Scanning.checked_peek_char ib dans
  filtre c avec
  | '0' .. '9' ->
    soit width = Scanning.store_char width ib c dans
    scan_decimal_digits width ib
  | c ->
    bad_input (Printf.sprintf "character %C is not a decimal digit" c)
;;

soit scan_digits_plus basis digitp width ib =
  (* To scan numbers from other bases, we use a predicate argument to
     scan_digits. *)
  soit rec scan_digits width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    filtre c avec
    | c quand digitp c ->
      soit width = Scanning.store_char width ib c dans
      scan_digits width
    | '_' ->
      soit width = Scanning.ignore_char width ib dans
      scan_digits width
    | _ -> width dans

  (* Ensure we have got enough width left,
     and read at list one digit. *)
  si width = 0 alors bad_token_length "digits" sinon
  soit c = Scanning.checked_peek_char ib dans

  si digitp c alors
    soit width = Scanning.store_char width ib c dans
    scan_digits width
  sinon
    bad_input (Printf.sprintf "character %C is not a valid %s digit" c basis)
;;

soit is_binary_digit = fonction
  | '0' .. '1' -> vrai
  | _ -> faux
;;

soit scan_binary_int = scan_digits_plus "binary" is_binary_digit;;

soit is_octal_digit = fonction
  | '0' .. '7' -> vrai
  | _ -> faux
;;

soit scan_octal_int = scan_digits_plus "octal" is_octal_digit;;

soit is_hexa_digit = fonction
  | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> vrai
  | _ -> faux
;;

soit scan_hexadecimal_int = scan_digits_plus "hexadecimal" is_hexa_digit;;

(* Scan a decimal integer. *)
soit scan_unsigned_decimal_int = scan_decimal_digits_plus;;

soit scan_sign width ib =
  soit c = Scanning.checked_peek_char ib dans
  filtre c avec
  | '+' -> Scanning.store_char width ib c
  | '-' -> Scanning.store_char width ib c
  | _ -> width
;;

soit scan_optionally_signed_decimal_int width ib =
  soit width = scan_sign width ib dans
  scan_unsigned_decimal_int width ib
;;

(* Scan an unsigned integer that could be given in any (common) basis.
   If digits are prefixed by one of 0x, 0X, 0o, or 0b, the number is
   assumed to be written respectively in hexadecimal, hexadecimal,
   octal, or binary. *)
soit scan_unsigned_int width ib =
  filtre Scanning.checked_peek_char ib avec
  | '0' tel c ->
    soit width = Scanning.store_char width ib c dans
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    début filtre c avec
    | 'x' | 'X' -> scan_hexadecimal_int (Scanning.store_char width ib c) ib
    | 'o' -> scan_octal_int (Scanning.store_char width ib c) ib
    | 'b' -> scan_binary_int (Scanning.store_char width ib c) ib
    | _ -> scan_decimal_digits width ib fin
  | _ -> scan_unsigned_decimal_int width ib
;;

soit scan_optionally_signed_int width ib =
  soit width = scan_sign width ib dans
  scan_unsigned_int width ib
;;

soit scan_int_conv conv width _prec ib =
  filtre conv avec
  | 'b' -> scan_binary_int width ib
  | 'd' -> scan_optionally_signed_decimal_int width ib
  | 'i' -> scan_optionally_signed_int width ib
  | 'o' -> scan_octal_int width ib
  | 'u' -> scan_unsigned_decimal_int width ib
  | 'x' | 'X' -> scan_hexadecimal_int width ib
  | _ -> affirme faux
;;

(* Scanning floating point numbers. *)
(* Fractional part is optional and can be reduced to 0 digits. *)
soit scan_frac_part width ib =
  si width = 0 alors width sinon
  soit c = Scanning.peek_char ib dans
  si Scanning.eof ib alors width sinon
  filtre c avec
  | '0' .. '9' tel c ->
    scan_decimal_digits (Scanning.store_char width ib c) ib
  | _ -> width
;;

(* Exp part is optional and can be reduced to 0 digits. *)
soit scan_exp_part width ib =
  si width = 0 alors width sinon
  soit c = Scanning.peek_char ib dans
  si Scanning.eof ib alors width sinon
  filtre c avec
  | 'e' | 'E' tel c ->
    scan_optionally_signed_decimal_int (Scanning.store_char width ib c) ib
  | _ -> width
;;

(* Scan the integer part of a floating point number, (not using the
   OCaml lexical convention since the integer part can be empty):
   an optional sign, followed by a possibly empty sequence of decimal
   digits (e.g. -.1). *)
soit scan_int_part width ib =
  soit width = scan_sign width ib dans
  scan_decimal_digits width ib
;;

(*
   For the time being we have (as found in scanf.mli):
   The field width is composed of an optional integer literal
   indicating the maximal width of the token to read.
   Unfortunately, the type-checker let the user write an optional precision,
   since this is valid for printf format strings.

   Thus, the next step for Scanf is to support a full width and precision
   indication, more or less similar to the one for printf, possibly extended
   to the specification of a [max, min] range for the width of the token read
   for strings. Something like the following spec for scanf.mli:

   The optional [width] is an integer indicating the maximal
   width of the token read. For instance, [%6d] reads an integer,
   having at most 6 characters.

   The optional [precision] is a dot [.] followed by an integer:

   - in the floating point number conversions ([%f], [%e], [%g], [%F], [%E],
   and [%F] conversions, the [precision] indicates the maximum number of
   digits that may follow the decimal point. For instance, [%.4f] reads a
   [float] with at most 4 fractional digits,

   - in the string conversions ([%s], [%S], [%\[ range \]]), and in the
   integer number conversions ([%i], [%d], [%u], [%x], [%o], and their
   [int32], [int64], and [native_int] correspondent), the [precision]
   indicates the required minimum width of the token read,

   - on all other conversions, the width and precision are meaningless and
   ignored (FIXME: lead to a runtime error ? type checking error ?).
*)

soit scan_float width precision ib =
  soit width = scan_int_part width ib dans
  si width = 0 alors width, precision sinon
  soit c = Scanning.peek_char ib dans
  si Scanning.eof ib alors width, precision sinon
  filtre c avec
  | '.' ->
    soit width = Scanning.store_char width ib c dans
    soit precision = min width precision dans
    soit width = width - (precision - scan_frac_part precision ib) dans
    scan_exp_part width ib, precision
  | _ ->
    scan_exp_part width ib, precision
;;

soit scan_Float width precision ib =
  soit width = scan_optionally_signed_decimal_int width ib dans
  si width = 0 alors bad_float () sinon
  soit c = Scanning.peek_char ib dans
  si Scanning.eof ib alors bad_float () sinon
  filtre c avec
  | '.' ->
    soit width = Scanning.store_char width ib c dans
    soit precision = min width precision dans
    soit width = width - (precision - scan_frac_part precision ib) dans
    scan_exp_part width ib
  | 'e' | 'E' ->
    scan_exp_part width ib
  | _ -> bad_float ()
;;

(* Scan a regular string:
   stops when encountering a space, if no scanning indication has been given;
   otherwise, stops when encountering one of the characters in the scanning
   indication list [stp].
   It also stops at end of file or when the maximum number of characters has
   been read.*)
soit scan_string stp width ib =
  soit rec loop width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si stp = [] alors
      filtre c avec
      | ' ' | '\t' | '\n' | '\r' -> width
      | c -> loop (Scanning.store_char width ib c) sinon
    si List.memq c stp alors Scanning.skip_char width ib sinon
    loop (Scanning.store_char width ib c) dans
  loop width
;;

(* Scan a char: peek strictly one character in the input, whatsoever. *)
soit scan_char width ib =
  (* The case width = 0 could not happen here, since it is tested before
     calling scan_char, in the main scanning function.
    if width = 0 then bad_token_length "a character" else *)
  Scanning.store_char width ib (Scanning.checked_peek_char ib)
;;

soit char_for_backslash = fonction
  | 'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c -> c
;;

(* The integer value corresponding to the facial value of a valid
   decimal digit character. *)
soit decimal_value_of_char c = int_of_char c - int_of_char '0';;

soit char_for_decimal_code c0 c1 c2 =
  soit c =
    100 * decimal_value_of_char c0 +
     10 * decimal_value_of_char c1 +
          decimal_value_of_char c2 dans
  si c < 0 || c > 255 alors
    bad_input
      (Printf.sprintf
         "bad character decimal encoding \\%c%c%c" c0 c1 c2) sinon
  char_of_int c
;;

(* The integer value corresponding to the facial value of a valid
   hexadecimal digit character. *)
soit hexadecimal_value_of_char c =
  soit d = int_of_char c dans
  (* Could also be:
    if d <= int_of_char '9' then d - int_of_char '0' else
    if d <= int_of_char 'F' then 10 + d - int_of_char 'A' else
    if d <= int_of_char 'f' then 10 + d - int_of_char 'a' else assert false
  *)
  si d >= int_of_char 'a' alors
    d - 87 (* 10 + int_of_char c - int_of_char 'a' *) sinon
  si d >= int_of_char 'A' alors
    d - 55  (* 10 + int_of_char c - int_of_char 'A' *) sinon
    d - int_of_char '0'
;;

soit char_for_hexadecimal_code c1 c2 =
  soit c =
    16 * hexadecimal_value_of_char c1 +
         hexadecimal_value_of_char c2 dans
  si c < 0 || c > 255 alors
    bad_input
      (Printf.sprintf "bad character hexadecimal encoding \\%c%c" c1 c2) sinon
  char_of_int c
;;

(* Called in particular when encountering '\\' as starter of a char.
   Stops before the corresponding '\''. *)
soit check_next_char message width ib =
  si width = 0 alors bad_token_length message sinon
  soit c = Scanning.peek_char ib dans
  si Scanning.eof ib alors bad_end_of_input message sinon
  c
;;

soit check_next_char_for_char = check_next_char "a Char";;
soit check_next_char_for_string = check_next_char "a String";;

soit scan_backslash_char width ib =
  filtre check_next_char_for_char width ib avec
  | '\\' | '\'' | '\"' | 'n' | 't' | 'b' | 'r' tel c ->
    Scanning.store_char width ib (char_for_backslash c)
  | '0' .. '9' tel c ->
    soit get_digit () =
      soit c = Scanning.next_char ib dans
      filtre c avec
      | '0' .. '9' tel c -> c
      | c -> bad_input_escape c dans
    soit c0 = c dans
    soit c1 = get_digit () dans
    soit c2 = get_digit () dans
    Scanning.store_char (width - 2) ib (char_for_decimal_code c0 c1 c2)
  | 'x' ->
    soit get_digit () =
      soit c = Scanning.next_char ib dans
      filtre c avec
      | '0' .. '9' | 'A' .. 'F' | 'a' .. 'f' tel c -> c
      | c -> bad_input_escape c dans
    soit c1 = get_digit () dans
    soit c2 = get_digit () dans
    Scanning.store_char (width - 2) ib (char_for_hexadecimal_code c1 c2)
  | c ->
    bad_input_escape c
;;

(* Scan a character (an OCaml token). *)
soit scan_Char width ib =

  soit rec find_start width =
    filtre Scanning.checked_peek_char ib avec
    | '\'' -> find_char (Scanning.ignore_char width ib)
    | c -> character_mismatch '\'' c

  et find_char width =
    filtre check_next_char_for_char width ib avec
    | '\\' ->
      find_stop (scan_backslash_char (Scanning.ignore_char width ib) ib)
    | c ->
      find_stop (Scanning.store_char width ib c)

  et find_stop width =
    filtre check_next_char_for_char width ib avec
    | '\'' -> Scanning.ignore_char width ib
    | c -> character_mismatch '\'' c dans

  find_start width
;;

(* Scan a delimited string (an OCaml token). *)
soit scan_String width ib =

  soit rec find_start width =
    filtre Scanning.checked_peek_char ib avec
    | '\"' -> find_stop (Scanning.ignore_char width ib)
    | c -> character_mismatch '\"' c

  et find_stop width =
    filtre check_next_char_for_string width ib avec
    | '\"' -> Scanning.ignore_char width ib
    | '\\' -> scan_backslash (Scanning.ignore_char width ib)
    | c -> find_stop (Scanning.store_char width ib c)

  et scan_backslash width =
    filtre check_next_char_for_string width ib avec
    | '\r' -> skip_newline (Scanning.ignore_char width ib)
    | '\n' -> skip_spaces (Scanning.ignore_char width ib)
    | _ -> find_stop (scan_backslash_char width ib)

  et skip_newline width =
    filtre check_next_char_for_string width ib avec
    | '\n' -> skip_spaces (Scanning.ignore_char width ib)
    | _ -> find_stop (Scanning.store_char width ib '\r')

  et skip_spaces width =
    filtre check_next_char_for_string width ib avec
    | ' ' -> skip_spaces (Scanning.ignore_char width ib)
    | _ -> find_stop width dans

  find_start width
;;

(* Scan a boolean (an OCaml token). *)
soit scan_bool width ib =
  si width < 4 alors bad_token_length "a boolean" sinon
  soit c = Scanning.checked_peek_char ib dans
  soit m =
    filtre c avec
    | 't' -> 4
    | 'f' -> 5
    | c ->
      bad_input
        (Printf.sprintf "the character %C cannot start a boolean" c) dans
  scan_string [] (min width m) ib
;;

(* Reading char sets in %[...] conversions. *)
type char_set =
   | Pos_set de string (* Positive (regular) set. *)
   | Neg_set de string (* Negative (complementary) set. *)
;;


(* Char sets are read as sub-strings in the format string. *)
soit scan_range fmt j =

  soit len = Sformat.length fmt dans

  soit buffer = Buffer.create len dans

  soit rec scan_closing j =
    si j >= len alors incomplete_format fmt sinon
    filtre Sformat.get fmt j avec
    | ']' -> j, Buffer.contents buffer
    | '%' ->
      soit j = j + 1 dans
      si j >= len alors incomplete_format fmt sinon
      début filtre Sformat.get fmt j avec
      | '%' | '@' tel c ->
        Buffer.add_char buffer c;
        scan_closing (j + 1)
      | c -> bad_conversion fmt j c
      fin
    | c ->
      Buffer.add_char buffer c;
      scan_closing (j + 1) dans

  soit scan_first_pos j =
    si j >= len alors incomplete_format fmt sinon
    filtre Sformat.get fmt j avec
    | ']' tel c ->
      Buffer.add_char buffer c;
      scan_closing (j + 1)
    | _ -> scan_closing j dans

  soit scan_first_neg j =
    si j >= len alors incomplete_format fmt sinon
    filtre Sformat.get fmt j avec
    | '^' ->
      soit j = j + 1 dans
      soit k, char_set = scan_first_pos j dans
      k, Neg_set char_set
    | _ ->
      soit k, char_set = scan_first_pos j dans
      k, Pos_set char_set dans

  scan_first_neg j
;;

(* Char sets are now represented as bit vectors that are represented as
   byte strings. *)

(* Bit manipulations into bytes. *)
soit set_bit_of_byte byte idx b =
  (b dgl idx) oul (byte etl (* mask idx *) (lnot (1 dgl idx)))
;;

soit get_bit_of_byte byte idx = (byte ddl idx) etl 1;;

(* Bit manipulations in vectors of bytes represented as strings. *)
soit set_bit_of_range r c b =
  soit idx = c etl 0x7 dans
  soit ydx = c ddl 3 dans
  soit byte = r.[ydx] dans
  r.[ydx] <- char_of_int (set_bit_of_byte (int_of_char byte) idx b)
;;

soit get_bit_of_range r c =
  soit idx = c etl 0x7 dans
  soit ydx = c ddl 3 dans
  soit byte = r.[ydx] dans
  get_bit_of_byte (int_of_char byte) idx
;;

(* Char sets represented as bit vectors represented as fixed length byte
   strings. *)
(* Create a full or empty set of chars. *)
soit make_range bit =
  soit c = char_of_int (si bit = 0 alors 0 sinon 0xFF) dans
  String.make 32 c
;;

(* Test if a char belongs to a set of chars. *)
soit get_char_in_range r c = get_bit_of_range r (int_of_char c);;

soit bit_not b = (lnot b) etl 1;;

(* Build the bit vector corresponding to the set of characters
   that belongs to the string argument [set].
   (In the [Scanf] module [set] is always a sub-string of the format.) *)
soit make_char_bit_vect bit set =
  soit r = make_range (bit_not bit) dans
  soit lim = String.length set - 1 dans
  soit rec loop bit rp i =
    si i <= lim alors
    filtre set.[i] avec
    | '-' quand rp ->
      (* if i = 0 then rp is false (since the initial call is
         loop bit false 0). Hence i >= 1 and the following is safe. *)
      soit c1 = set.[i - 1] dans
      soit i = succ i dans
      si i > lim alors loop bit faux (i - 1) sinon
      soit c2 = set.[i] dans
      pour j = int_of_char c1 à int_of_char c2 faire
        set_bit_of_range r j bit fait;
      loop bit faux (succ i)
    | _ ->
      set_bit_of_range r (int_of_char set.[i]) bit;
      loop bit vrai (succ i) dans
  loop bit faux 0;
  r
;;

(* Compute the predicate on chars corresponding to a char set. *)
soit make_predicate bit set stp =
  soit r = make_char_bit_vect bit set dans
  List.iter
    (fonc c -> set_bit_of_range r (int_of_char c) (bit_not bit)) stp;
  (fonc c -> get_char_in_range r c)
;;

soit make_setp stp char_set =
  filtre char_set avec
  | Pos_set set ->
    début filtre String.length set avec
    | 0 -> (fonc _ -> 0)
    | 1 ->
      soit p = set.[0] dans
      (fonc c -> si c == p alors 1 sinon 0)
    | 2 ->
      soit p1 = set.[0] et p2 = set.[1] dans
      (fonc c -> si c == p1 || c == p2 alors 1 sinon 0)
    | 3 ->
      soit p1 = set.[0] et p2 = set.[1] et p3 = set.[2] dans
      si p2 = '-' alors make_predicate 1 set stp sinon
      (fonc c -> si c == p1 || c == p2 || c == p3 alors 1 sinon 0)
    | _ -> make_predicate 1 set stp
    fin
  | Neg_set set ->
    début filtre String.length set avec
    | 0 -> (fonc _ -> 1)
    | 1 ->
      soit p = set.[0] dans
      (fonc c -> si c != p alors 1 sinon 0)
    | 2 ->
      soit p1 = set.[0] et p2 = set.[1] dans
      (fonc c -> si c != p1 && c != p2 alors 1 sinon 0)
    | 3 ->
      soit p1 = set.[0] et p2 = set.[1] et p3 = set.[2] dans
      si p2 = '-' alors make_predicate 0 set stp sinon
      (fonc c -> si c != p1 && c != p2 && c != p3 alors 1 sinon 0)
    | _ -> make_predicate 0 set stp
    fin
;;

soit setp_table = Hashtbl.create 7;;

soit add_setp stp char_set setp =
  soit char_set_tbl =
    essaie Hashtbl.find setp_table char_set avec
    | Not_found ->
      soit char_set_tbl = Hashtbl.create 3 dans
      Hashtbl.add setp_table char_set char_set_tbl;
      char_set_tbl dans
  Hashtbl.add char_set_tbl stp setp
;;

soit find_setp stp char_set =
  essaie Hashtbl.find (Hashtbl.find setp_table char_set) stp avec
  | Not_found ->
    soit setp = make_setp stp char_set dans
    add_setp stp char_set setp;
    setp
;;

soit scan_chars_in_char_set stp char_set width ib =
  soit rec loop_pos1 cp1 width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si c == cp1
    alors loop_pos1 cp1 (Scanning.store_char width ib c)
    sinon width
  et loop_pos2 cp1 cp2 width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si c == cp1 || c == cp2
    alors loop_pos2 cp1 cp2 (Scanning.store_char width ib c)
    sinon width
  et loop_pos3 cp1 cp2 cp3 width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si c == cp1 || c == cp2 || c == cp3
    alors loop_pos3 cp1 cp2 cp3 (Scanning.store_char width ib c)
    sinon width
  et loop_neg1 cp1 width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si c != cp1
    alors loop_neg1 cp1 (Scanning.store_char width ib c)
    sinon width
  et loop_neg2 cp1 cp2 width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si c != cp1 && c != cp2
    alors loop_neg2 cp1 cp2 (Scanning.store_char width ib c)
    sinon width
  et loop_neg3 cp1 cp2 cp3 width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si c != cp1 && c != cp2 && c != cp3
    alors loop_neg3 cp1 cp2 cp3 (Scanning.store_char width ib c)
    sinon width
  et loop setp width =
    si width = 0 alors width sinon
    soit c = Scanning.peek_char ib dans
    si Scanning.eof ib alors width sinon
    si setp c == 1
    alors loop setp (Scanning.store_char width ib c)
    sinon width dans

  soit width =
    filtre char_set avec
    | Pos_set set ->
      début filtre String.length set avec
      | 0 -> loop (fonc _ -> 0) width
      | 1 -> loop_pos1 set.[0] width
      | 2 -> loop_pos2 set.[0] set.[1] width
      | 3 quand set.[1] != '-' -> loop_pos3 set.[0] set.[1] set.[2] width
      | _ -> loop (find_setp stp char_set) width fin
    | Neg_set set ->
      début filtre String.length set avec
      | 0 -> loop (fonc _ -> 1) width
      | 1 -> loop_neg1 set.[0] width
      | 2 -> loop_neg2 set.[0] set.[1] width
      | 3 quand set.[1] != '-' -> loop_neg3 set.[0] set.[1] set.[2] width
      | _ -> loop (find_setp stp char_set) width fin dans
  ignore_stoppers stp ib;
  width
;;

soit get_count t ib =
  filtre t avec
  | 'l' -> Scanning.line_count ib
  | 'n' -> Scanning.char_count ib
  | _ -> Scanning.token_count ib
;;

soit rec skip_whites ib =
  soit c = Scanning.peek_char ib dans
  si not (Scanning.eof ib) alors début
    filtre c avec
    | ' ' | '\t' | '\n' | '\r' ->
      Scanning.invalidate_current_char ib; skip_whites ib
    | _ -> ()
  fin
;;

(* The global error report function for [Scanf]. *)
soit scanf_bad_input ib = fonction
  | Scan_failure s | Failure s ->
    soit i = Scanning.char_count ib dans
    bad_input (Printf.sprintf "scanf: bad input at char number %i: \'%s\'" i s)
  | x -> raise x
;;

soit list_iter_i f l =
  soit rec loop i = fonction
  | [] -> ()
  | [x] -> f i x (* Tail calling [f] *)
  | x :: xs -> f i x; loop (succ i) xs dans
  loop 0 l
;;

soit ascanf sc fmt =
  soit ac = Tformat.ac_of_format fmt dans
  filtre ac.Tformat.ac_rdrs avec
  | 0 ->
    Obj.magic (fonc f -> sc fmt [||] f)
  | 1 ->
    Obj.magic (fonc x f -> sc fmt [| Obj.repr x |] f)
  | 2 ->
    Obj.magic (fonc x y f -> sc fmt [| Obj.repr x; Obj.repr y; |] f)
  | 3 ->
    Obj.magic
      (fonc x y z f -> sc fmt [| Obj.repr x; Obj.repr y; Obj.repr z; |] f)
  | nargs ->
    soit rec loop i args =
      si i >= nargs alors
        soit a = Array.make nargs (Obj.repr 0) dans
        list_iter_i (fonc i arg -> a.(nargs - i - 1) <- arg) args;
        Obj.magic (fonc f -> sc fmt a f)
      sinon Obj.magic (fonc x -> loop (succ i) (x :: args)) dans
    loop 0 []
;;

(* The [scan_format] main scanning function.
   It takes as arguments:
     - an input buffer [ib] from which to read characters,
     - an error handling function [ef],
     - a format [fmt] that specifies what to read in the input,
     - a vector of user's defined readers [rv],
     - and a function [f] to pass the tokens read to.

   Then [scan_format] scans the format and the input buffer in parallel to
   find out tokens as specified by the format; when it finds one token, it
   converts it as specified, remembers the converted value as a future
   argument to the function [f], and continues scanning.

   If the entire scanning succeeds (i.e. the format string has been
   exhausted and the buffer has provided tokens according to the
   format string), [f] is applied to the tokens read.

   If the scanning or some conversion fails, the main scanning function
   aborts and applies the scanning buffer and a string that explains
   the error to the error handling function [ef] (the error continuation). *)

soit scan_format ib ef fmt rv f =

  soit limr = Array.length rv - 1 dans

  soit return v = Obj.magic v () dans
  soit delay f x () = f x dans
  soit stack f = delay (return f) dans
  soit no_stack f _x = f dans

  soit rec scan fmt =

    soit lim = Sformat.length fmt - 1 dans

    soit rec scan_fmt ir f i =
      si i > lim alors ir, f sinon
      filtre Sformat.unsafe_get fmt i avec
      | '%' -> scan_skip ir f (succ i)
      | ' ' -> skip_whites ib; scan_fmt ir f (succ i)
      | c -> check_char ib c; scan_fmt ir f (succ i)

    et scan_skip ir f i =
      si i > lim alors ir, f sinon
      filtre Sformat.get fmt i avec
      | '_' -> scan_limits vrai ir f (succ i)
      | _ -> scan_limits faux ir f i

    et scan_limits skip ir f i =

      soit rec scan_width i =
        si i > lim alors incomplete_format fmt sinon
        filtre Sformat.get fmt i avec
        | '0' .. '9' tel conv ->
          soit width, i =
            read_int_literal (decimal_value_of_char conv) (succ i) dans
          Some width, i
        | _ -> None, i

      et scan_precision i =
        début
          filtre Sformat.get fmt i avec
          | '.' ->
            soit precision, i = read_int_literal 0 (succ i) dans
            (Some precision, i)
          | _ -> None, i
        fin

      et read_int_literal accu i =
        si i > lim alors accu, i sinon
        filtre Sformat.unsafe_get fmt i avec
        | '0' .. '9' tel c ->
          soit accu = 10 * accu + decimal_value_of_char c dans
          read_int_literal accu (succ i)
        | _ -> accu, i dans

      si i > lim alors ir, f sinon
      soit width_opt, i = scan_width i dans
      soit prec_opt, i = scan_precision i dans
      scan_conversion skip width_opt prec_opt ir f i

    et scan_conversion skip width_opt prec_opt ir f i =
      soit stack = si skip alors no_stack sinon stack dans
      soit width = int_of_width_opt width_opt dans
      soit prec = int_of_prec_opt prec_opt dans
      filtre Sformat.get fmt i avec
      | '%' | '@' tel c ->
        check_char ib c;
        scan_fmt ir f (succ i)
      | '!' ->
        si not (Scanning.end_of_input ib)
        alors bad_input "end of input not found" sinon
        scan_fmt ir f (succ i)
      | ',' ->
        scan_fmt ir f (succ i)
      | 's' ->
        soit i, stp = scan_indication (succ i) dans
        soit _x = scan_string stp width ib dans
        scan_fmt ir (stack f (token_string ib)) (succ i)
      | 'S' ->
        soit _x = scan_String width ib dans
        scan_fmt ir (stack f (token_string ib)) (succ i)
      | '[' (* ']' *) ->
        soit i, char_set = scan_range fmt (succ i) dans
        soit i, stp = scan_indication (succ i) dans
        soit _x = scan_chars_in_char_set stp char_set width ib dans
        scan_fmt ir (stack f (token_string ib)) (succ i)
      | ('c' | 'C') quand width = 0 ->
        soit c = Scanning.checked_peek_char ib dans
        scan_fmt ir (stack f c) (succ i)
      | 'c' ->
        soit _x = scan_char width ib dans
        scan_fmt ir (stack f (token_char ib)) (succ i)
      | 'C' ->
        soit _x = scan_Char width ib dans
        scan_fmt ir (stack f (token_char ib)) (succ i)
      | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' tel conv ->
        soit _x = scan_int_conv conv width prec ib dans
        scan_fmt ir (stack f (token_int conv ib)) (succ i)
      | 'N' tel conv ->
        scan_fmt ir (stack f (get_count conv ib)) (succ i)
      | 'f' | 'e' | 'E' | 'g' | 'G' ->
        soit _x = scan_float width prec ib dans
        scan_fmt ir (stack f (token_float ib)) (succ i)
      | 'F' ->
        soit _x = scan_Float width prec ib dans
        scan_fmt ir (stack f (token_float ib)) (succ i)
(*      | 'B' | 'b' when width = Some 0 ->
        let _x = scan_bool width ib in
        scan_fmt ir (stack f (token_int ib)) (succ i) *)
      | 'B' | 'b' ->
        soit _x = scan_bool width ib dans
        scan_fmt ir (stack f (token_bool ib)) (succ i)
      | 'r' ->
        si ir > limr alors affirme faux sinon
        soit token = Obj.magic rv.(ir) ib dans
        scan_fmt (succ ir) (stack f token) (succ i)
      | 'l' | 'n' | 'L' tel conv0 ->
        soit i = succ i dans
        si i > lim alors scan_fmt ir (stack f (get_count conv0 ib)) i sinon début
        filtre Sformat.get fmt i avec
        (* This is in fact an integer conversion (e.g. %ld, %ni, or %Lo). *)
        | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' tel conv1 ->
          soit _x = scan_int_conv conv1 width prec ib dans
          (* Look back to the character that triggered the integer conversion
             (this character is either 'l', 'n' or 'L') to find the
             conversion to apply to the integer token read. *)
          début filtre conv0 avec
          | 'l' -> scan_fmt ir (stack f (token_int32 conv1 ib)) (succ i)
          | 'n' -> scan_fmt ir (stack f (token_nativeint conv1 ib)) (succ i)
          | _ -> scan_fmt ir (stack f (token_int64 conv1 ib)) (succ i) fin
        (* This is not an integer conversion, but a regular %l, %n or %L. *)
        | _ -> scan_fmt ir (stack f (get_count conv0 ib)) i fin
      | '(' | '{' tel conv (* ')' '}' *) ->
        soit i = succ i dans
        (* Find [mf], the static specification for the format to read. *)
        soit j =
          Tformat.sub_format
            incomplete_format bad_conversion conv fmt i dans
        soit mf = Sformat.sub fmt (Sformat.index_of_int i) (j - 2 - i) dans
        (* Read [rf], the specified format string in the input buffer,
           and check its correctness w.r.t. [mf]. *)
        soit _x = scan_String width ib dans
        soit rf = token_string ib dans
        si not (compatible_format_type rf mf) alors format_mismatch rf mf sinon
        (* Proceed according to the kind of metaformat found:
           - %{ mf %} simply returns [rf] as the token read,
           - %( mf %) returns [rf] as the first token read, then
             returns a second token obtained by scanning the input with
             format string [rf].
           Behaviour for %( mf %) is mandatory for sake of format string
           typechecking specification. To get pure format string
           substitution behaviour, you should use %_( mf %) that skips the
           first (format string) token and hence properly substitutes [mf] by
           [rf] in the format string argument.
        *)
        (* For conversion %{%}, just return this format string as the token
           read and go on with the rest of the format string argument. *)
        si conv = '{' (* '}' *) alors scan_fmt ir (stack f rf) j sinon
        (* Or else, return this format string as the first token read;
           then continue scanning using this format string to get
           the following token read;
           finally go on with the rest of the format string argument. *)
        soit ir, nf = scan (string_to_format rf) ir (stack f rf) 0 dans
        (* Return the format string read and the value just read,
           then go on with the rest of the format. *)
        scan_fmt ir nf j

      | c -> bad_conversion fmt i c

    et scan_indication j =
      si j > lim alors j - 1, [] sinon
      filtre Sformat.get fmt j avec
      | '@' ->
        soit k = j + 1 dans
        si k > lim alors j - 1, [] sinon
        début filtre Sformat.get fmt k avec
        | '%' ->
          soit k = k + 1 dans
          si k > lim alors j - 1, [] sinon
          début filtre Sformat.get fmt k avec
          | '%' | '@' tel c  -> k, [ c ]
          | _c -> j - 1, []
          fin
        | c -> k, [ c ]
        fin
      | _c -> j - 1, [] dans

    scan_fmt dans


  Scanning.reset_token ib;

  soit v =
    essaie snd (scan fmt 0 (fonc () -> f) 0) avec
    | (Scan_failure _ | Failure _ | End_of_file) tel exc ->
      stack (delay ef ib) exc dans
  return v
;;

soit mkscanf ib ef fmt =
  soit sc = scan_format ib ef dans
  ascanf sc fmt
;;

soit kscanf ib ef fmt = mkscanf ib ef fmt;;

soit bscanf ib = kscanf ib scanf_bad_input;;

soit fscanf ic = bscanf (Scanning.from_channel ic);;

soit sscanf : string -> ('a, 'b, 'c, 'd) scanner
  = fonc s -> bscanf (Scanning.from_string s);;

soit scanf fmt = bscanf Scanning.stdib fmt;;

soit bscanf_format ib fmt f =
  soit fmt = Sformat.unsafe_to_string fmt dans
  soit fmt1 =
    ignore (scan_String max_int ib);
    token_string ib dans
  si not (compatible_format_type fmt1 fmt) alors
    format_mismatch fmt1 fmt sinon
  f (string_to_format fmt1)
;;

soit sscanf_format s fmt = bscanf_format (Scanning.from_string s) fmt;;

soit string_to_String s =
  soit l = String.length s dans
  soit b = Buffer.create (l + 2) dans
  Buffer.add_char b '\"';
  pour i = 0 à l - 1 faire
    soit c = s.[i] dans
    si c = '\"' alors Buffer.add_char b '\\';
    Buffer.add_char b c;
  fait;
  Buffer.add_char b '\"';
  Buffer.contents b
;;

soit format_from_string s fmt =
  sscanf_format (string_to_String s) fmt (fonc x -> x)
;;

soit unescaped s =
  sscanf ("\"" ^ s ^ "\"") "%S%!" (fonc x -> x)
;;

(*
 Local Variables:
  compile-command: "cd ..; make world"
  End:
*)
