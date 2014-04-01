(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

soit generic_quote quotequote s =
  soit l = String.length s dans
  soit b = Buffer.create (l + 20) dans
  Buffer.add_char b '\'';
  pour i = 0 à l - 1 faire
    si s.[i] = '\''
    alors Buffer.add_string b quotequote
    sinon Buffer.add_char b  s.[i]
  fait;
  Buffer.add_char b '\'';
  Buffer.contents b

(* This function implements the Open Group specification found here:
  [[1]] http://pubs.opengroup.org/onlinepubs/9699919799/utilities/basename.html
  In step 1 of [[1]], we choose to return "." for empty input.
    (for compatibility with previous versions of OCaml)
  In step 2, we choose to process "//" normally.
  Step 6 is not implemented: we consider that the [suffix] operand is
    always absent.  Suffixes are handled by [chop_suffix] and [chop_extension].
*)
soit generic_basename is_dir_sep current_dir_name name =
  soit rec find_end n =
    si n < 0 alors String.sub name 0 1
    sinon si is_dir_sep name n alors find_end (n - 1)
    sinon find_beg n (n + 1)
  et find_beg n p =
    si n < 0 alors String.sub name 0 p
    sinon si is_dir_sep name n alors String.sub name (n + 1) (p - n - 1)
    sinon find_beg (n - 1) p
  dans
  si name = ""
  alors current_dir_name
  sinon find_end (String.length name - 1)

(* This function implements the Open Group specification found here:
  [[2]] http://pubs.opengroup.org/onlinepubs/9699919799/utilities/dirname.html
  In step 6 of [[2]], we choose to process "//" normally.
*)
soit generic_dirname is_dir_sep current_dir_name name =
  soit rec trailing_sep n =
    si n < 0 alors String.sub name 0 1
    sinon si is_dir_sep name n alors trailing_sep (n - 1)
    sinon base n
  et base n =
    si n < 0 alors current_dir_name
    sinon si is_dir_sep name n alors intermediate_sep n
    sinon base (n - 1)
  et intermediate_sep n =
    si n < 0 alors String.sub name 0 1
    sinon si is_dir_sep name n alors intermediate_sep (n - 1)
    sinon String.sub name 0 (n + 1)
  dans
  si name = ""
  alors current_dir_name
  sinon trailing_sep (String.length name - 1)

module Unix = struct
  soit current_dir_name = "."
  soit parent_dir_name = ".."
  soit dir_sep = "/"
  soit is_dir_sep s i = s.[i] = '/'
  soit is_relative n = String.length n < 1 || n.[0] <> '/';;
  soit is_implicit n =
    is_relative n
    && (String.length n < 2 || String.sub n 0 2 <> "./")
    && (String.length n < 3 || String.sub n 0 3 <> "../")
  soit check_suffix name suff =
    String.length name >= String.length suff &&
    String.sub name (String.length name - String.length suff)
                    (String.length suff) = suff
  soit temp_dir_name =
    essaie Sys.getenv "TMPDIR" avec Not_found -> "/tmp"
  soit quote = generic_quote "'\\''"
  soit basename = generic_basename is_dir_sep current_dir_name
  soit dirname = generic_dirname is_dir_sep current_dir_name
fin

module Win32 = struct
  soit current_dir_name = "."
  soit parent_dir_name = ".."
  soit dir_sep = "\\"
  soit is_dir_sep s i = soit c = s.[i] dans c = '/' || c = '\\' || c = ':'
  soit is_relative n =
    (String.length n < 1 || n.[0] <> '/')
    && (String.length n < 1 || n.[0] <> '\\')
    && (String.length n < 2 || n.[1] <> ':')
  soit is_implicit n =
    is_relative n
    && (String.length n < 2 || String.sub n 0 2 <> "./")
    && (String.length n < 2 || String.sub n 0 2 <> ".\\")
    && (String.length n < 3 || String.sub n 0 3 <> "../")
    && (String.length n < 3 || String.sub n 0 3 <> "..\\")
  soit check_suffix name suff =
   String.length name >= String.length suff &&
   (soit s = String.sub name (String.length name - String.length suff)
                            (String.length suff) dans
    String.lowercase s = String.lowercase suff)
  soit temp_dir_name =
    essaie Sys.getenv "TEMP" avec Not_found -> "."
  soit quote s =
    soit l = String.length s dans
    soit b = Buffer.create (l + 20) dans
    Buffer.add_char b '\"';
    soit rec loop i =
      si i = l alors Buffer.add_char b '\"' sinon
      filtre s.[i] avec
      | '\"' -> loop_bs 0 i;
      | '\\' -> loop_bs 0 i;
      | c    -> Buffer.add_char b c; loop (i+1);
    et loop_bs n i =
      si i = l alors début
        Buffer.add_char b '\"';
        add_bs n;
      fin sinon début
        filtre s.[i] avec
        | '\"' -> add_bs (2*n+1); Buffer.add_char b '\"'; loop (i+1);
        | '\\' -> loop_bs (n+1) (i+1);
        | c    -> add_bs n; loop i
      fin
    et add_bs n = pour _j = 1 à n faire Buffer.add_char b '\\'; fait
    dans
    loop 0;
    Buffer.contents b
  soit has_drive s =
    soit is_letter = fonction
      | 'A' .. 'Z' | 'a' .. 'z' -> vrai
      | _ -> faux
    dans
    String.length s >= 2 && is_letter s.[0] && s.[1] = ':'
  soit drive_and_path s =
    si has_drive s
    alors (String.sub s 0 2, String.sub s 2 (String.length s - 2))
    sinon ("", s)
  soit dirname s =
    soit (drive, path) = drive_and_path s dans
    soit dir = generic_dirname is_dir_sep current_dir_name path dans
    drive ^ dir
  soit basename s =
    soit (drive, path) = drive_and_path s dans
    generic_basename is_dir_sep current_dir_name path
fin

module Cygwin = struct
  soit current_dir_name = "."
  soit parent_dir_name = ".."
  soit dir_sep = "/"
  soit is_dir_sep = Win32.is_dir_sep
  soit is_relative = Win32.is_relative
  soit is_implicit = Win32.is_implicit
  soit check_suffix = Win32.check_suffix
  soit temp_dir_name = Unix.temp_dir_name
  soit quote = Unix.quote
  soit basename = generic_basename is_dir_sep current_dir_name
  soit dirname = generic_dirname is_dir_sep current_dir_name
fin

soit (current_dir_name, parent_dir_name, dir_sep, is_dir_sep,
     is_relative, is_implicit, check_suffix, temp_dir_name, quote, basename,
     dirname) =
  filtre Sys.os_type avec
    "Unix" ->
      (Unix.current_dir_name, Unix.parent_dir_name, Unix.dir_sep,
       Unix.is_dir_sep,
       Unix.is_relative, Unix.is_implicit, Unix.check_suffix,
       Unix.temp_dir_name, Unix.quote, Unix.basename, Unix.dirname)
  | "Win32" ->
      (Win32.current_dir_name, Win32.parent_dir_name, Win32.dir_sep,
       Win32.is_dir_sep,
       Win32.is_relative, Win32.is_implicit, Win32.check_suffix,
       Win32.temp_dir_name, Win32.quote, Win32.basename, Win32.dirname)
  | "Cygwin" ->
      (Cygwin.current_dir_name, Cygwin.parent_dir_name, Cygwin.dir_sep,
       Cygwin.is_dir_sep,
       Cygwin.is_relative, Cygwin.is_implicit, Cygwin.check_suffix,
       Cygwin.temp_dir_name, Cygwin.quote, Cygwin.basename, Cygwin.dirname)
  | _ -> affirme faux

soit concat dirname filename =
  soit l = String.length dirname dans
  si l = 0 || is_dir_sep dirname (l-1)
  alors dirname ^ filename
  sinon dirname ^ dir_sep ^ filename

soit chop_suffix name suff =
  soit n = String.length name - String.length suff dans
  si n < 0 alors invalid_arg "Filename.chop_suffix" sinon String.sub name 0 n

soit chop_extension name =
  soit rec search_dot i =
    si i < 0 || is_dir_sep name i alors invalid_arg "Filename.chop_extension"
    sinon si name.[i] = '.' alors String.sub name 0 i
    sinon search_dot (i - 1) dans
  search_dot (String.length name - 1)

dehors open_desc: string -> open_flag list -> int -> int = "caml_sys_open"
dehors close_desc: int -> unit = "caml_sys_close"

soit prng = paresseux(Random.State.make_self_init ());;

soit temp_file_name temp_dir prefix suffix =
  soit rnd = (Random.State.bits (Lazy.force prng)) etl 0xFFFFFF dans
  concat temp_dir (Printf.sprintf "%s%06x%s" prefix rnd suffix)
;;

soit current_temp_dir_name = ref temp_dir_name

soit set_temp_dir_name s = current_temp_dir_name := s
soit get_temp_dir_name () = !current_temp_dir_name

soit temp_file ?(temp_dir = !current_temp_dir_name) prefix suffix =
  soit rec try_name counter =
    soit name = temp_file_name temp_dir prefix suffix dans
    essaie
      close_desc(open_desc name [Open_wronly; Open_creat; Open_excl] 0o600);
      name
    avec Sys_error _ tel e ->
      si counter >= 1000 alors raise e sinon try_name (counter + 1)
  dans try_name 0

soit open_temp_file ?(mode = [Open_text]) ?(temp_dir = !current_temp_dir_name)
                   prefix suffix =
  soit rec try_name counter =
    soit name = temp_file_name temp_dir prefix suffix dans
    essaie
      (name,
       open_out_gen (Open_wronly::Open_creat::Open_excl::mode) 0o600 name)
    avec Sys_error _ tel e ->
      si counter >= 1000 alors raise e sinon try_name (counter + 1)
  dans try_name 0
