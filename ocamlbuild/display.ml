(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Berke Durak *)
(* Display *)
ouvre My_std;;

ouvre My_unix;;

soit fp = Printf.fprintf;;

(*** ANSI *)
module ANSI =
  struct
    soit up oc n = fp oc "\027[%dA" n;;
    soit clear_to_eol oc () = fp oc "\027[K";;
    soit bol oc () = fp oc "\r";;
    soit get_columns () =
      si Sys.os_type = "Unix" alors
        essaie
          int_of_string (String.chomp (My_unix.run_and_read "tput cols"))
        avec
        | Failure _ -> 80
      sinon 80
  fin
;;
(* ***)
(*** tagline_description *)
type tagline_description = (string * char) list;;
(* ***)
(*** sophisticated_display *)
type sophisticated_display = {
          ds_channel         : out_channel;            (** Channel for writing *)
          ds_start_time      : float;                  (** When was compilation started *)
  modifiable ds_last_update     : float;                  (** When was the display last updated *)
  modifiable ds_last_target     : string;                 (** Last target built *)
  modifiable ds_last_cached     : bool;                   (** Was the last target cached or really built ? *)
  modifiable ds_last_tags       : Tags.t;                 (** Tags of the last command *)
  modifiable ds_changed         : bool;                   (** Does the tag line need recomputing ? *)
          ds_update_interval : float;                  (** Minimum interval between updates *)
          ds_columns         : int;                    (** Number of columns in dssplay *)
  modifiable ds_jobs            : int;                    (** Number of jobs launched or cached *)
  modifiable ds_jobs_cached     : int;                    (** Number of jobs cached *)
          ds_tagline         : string;                 (** Current tagline *)
  modifiable ds_seen_tags       : Tags.t;                 (** Tags that we have encountered *)
          ds_pathname_length : int;                    (** How much space for displaying pathnames ? *)
          ds_tld             : tagline_description;    (** Description for the tagline *)
};;
(* ***)
(*** display_line, display *)
type display_line =
| Classic
| Sophisticated de sophisticated_display

type display = {
          di_log_level    : int;
  modifiable di_log_channel  : (Format.formatter * out_channel) option;
          di_channel      : out_channel;
          di_formatter    : Format.formatter;
          di_display_line : display_line;
  modifiable di_finished     : bool;
}
;;
(* ***)
(*** various defaults *)
soit default_update_interval = 0.05;;
soit default_tagline_description = [
  "ocaml",     'O';
  "native",    'N';
  "byte",      'B';
  "program",   'P';
  "pp",        'R';
  "debug",     'D';
  "interf",    'I';
  "link",      'L';
];;

(* NOT including spaces *)
soit countdown_chars = 8;;
soit jobs_chars = 3;;
soit jobs_cached_chars = 5;;
soit dots = "...";;
soit start_target = "STARTING";;
soit finish_target = "FINISHED";;
soit ticker_chars = 3;;
soit ticker_period = 0.25;;
soit ticker_animation = [|
  "\\";
  "|";
  "/";
  "-";
|];;
soit cached = "*";;
soit uncached = " ";;
soit cache_chars = 1;;
(* ***)
(*** create_tagline *)
soit create_tagline description = String.make (List.length description) '-';;
(* ***)
(*** create *)
soit create
  ?(channel=stdout)
  ?(mode:[`Classic|`Sophisticated] = `Sophisticated)
  ?columns:(_columns=75)
  ?(description = default_tagline_description)
  ?log_file
  ?(log_level=1)
  ()
  =
  soit log_channel =
    filtre log_file avec
    | None -> None
    | Some fn ->
        soit oc = open_out_gen [Open_text; Open_wronly; Open_creat; Open_trunc] 0o666 fn dans
        soit f = Format.formatter_of_out_channel oc dans
        Format.fprintf f "### Starting build.\n";
        Some (f, oc)
  dans

  soit display_line =
    filtre mode avec
    | `Classic -> Classic
    | `Sophisticated ->
      (* We assume Unix is not degraded. *)
      soit n = ANSI.get_columns () dans
      soit tag_chars = List.length description dans
      Sophisticated
        { ds_channel         = stdout;
          ds_start_time      = gettimeofday ();
          ds_last_update     = 0.0;
          ds_last_target     = start_target;
          ds_last_tags       = Tags.empty;
          ds_last_cached     = faux;
          ds_changed         = faux;
          ds_update_interval = default_update_interval;
          ds_columns         = n;
          ds_jobs            = 0;
          ds_jobs_cached     = 0;
          ds_tagline         = create_tagline description;
          ds_seen_tags       = Tags.empty;
          ds_pathname_length = n -
                                 (countdown_chars + 1 + jobs_chars + 1 + jobs_cached_chars + 1 +
                                  cache_chars + 1 + tag_chars + 1 + ticker_chars + 2);
          ds_tld             = description }
  dans
  { di_log_level    = log_level;
    di_log_channel  = log_channel;
    di_channel      = channel;
    di_formatter    = Format.formatter_of_out_channel channel;
    di_display_line = display_line;
    di_finished     = faux }
;;
(* ***)
(*** print_time *)
soit print_time oc t =
  soit t = int_of_float t dans
  soit s = t mod 60 dans
  soit m = (t / 60) mod 60 dans
  soit h = t / 3600 dans
  fp oc "%02d:%02d:%02d" h m s
;;
(* ***)
(*** print_shortened_pathname *)
soit print_shortened_pathname length oc u =
  affirme(length >= 3);
  soit m = String.length u dans
  si m <= length alors
    début
      output_string oc u;
      fp oc "%*s" (length - m) ""
    fin
  sinon
    début
      soit n = String.length dots dans
      soit k = length - n dans
      output_string oc dots;
      output oc u (m - k) k;
    fin
(* ***)
(*** Layout

00000000001111111111222222222233333333334444444444555555555566666666667777777777
01234567890123456789012345678901234567890123456789012345678901234567890123456789
HH MM SS XXXX        PATHNAME
00:12:31   32 (  26) ...lp4Filters/Camlp4LocationStripper.cmo * OBn-------------
|          |  |      |                                        | \ tags
|          |  |      \ last target built                      \ cached ?
|          |  |
|          |  \ number of jobs cached
|          \ number of jobs
\ elapsed time
cmo mllib
***)
(*** redraw_sophisticated *)
soit redraw_sophisticated ds =
  soit t = gettimeofday () dans
  soit oc = ds.ds_channel dans
  soit dt = t -. ds.ds_start_time dans
  ds.ds_last_update <- t;
  fp oc "%a" ANSI.bol ();
  soit ticker_phase = (abs (int_of_float (ceil (dt /. ticker_period)))) mod (Array.length ticker_animation) dans
  soit ticker = ticker_animation.(ticker_phase) dans
  fp oc "%a %-4d (%-4d) %a %s %s %s"
    print_time dt
    ds.ds_jobs
    ds.ds_jobs_cached
    (print_shortened_pathname ds.ds_pathname_length) ds.ds_last_target
    (si ds.ds_last_cached alors cached sinon uncached)
    ds.ds_tagline
    ticker;
  fp oc "%a%!" ANSI.clear_to_eol ()
;;
(* ***)
(*** redraw *)
soit redraw = fonction
  | Classic -> ()
  | Sophisticated ds -> redraw_sophisticated ds
;;
(* ***)
(*** finish_sophisticated *)
soit finish_sophisticated ?(how=`Success) ds =
  soit t = gettimeofday () dans
  soit oc = ds.ds_channel dans
  soit dt = t -. ds.ds_start_time dans
  filtre how avec
  | `Success|`Error ->
    fp oc "%a" ANSI.bol ();
    fp oc "%s %d target%s (%d cached) in %a."
      (si how = `Error alors
        "Compilation unsuccessful after building"
       sinon
         "Finished,")
      ds.ds_jobs
      (si ds.ds_jobs = 1 alors "" sinon "s")
      ds.ds_jobs_cached
      print_time dt;
    fp oc "%a\n%!" ANSI.clear_to_eol ()
  | `Quiet ->
    fp oc "%a%a%!" ANSI.bol () ANSI.clear_to_eol ();
;;
(* ***)
(*** sophisticated_display *)
soit sophisticated_display ds f =
  fp ds.ds_channel "%a%a%!" ANSI.bol () ANSI.clear_to_eol ();
  f ds.ds_channel
;;
(* ***)
(*** call_if *)
soit call_if log_channel f =
  filtre log_channel avec
  | None -> ()
  | Some x -> f x
;;
(* ***)
(*** display *)
soit display di f =
  call_if di.di_log_channel (fonc (_, oc) -> f oc);
  filtre di.di_display_line avec
  | Classic -> f di.di_channel
  | Sophisticated ds -> sophisticated_display ds f
;;
(* ***)
(*** finish *)
soit finish ?(how=`Success) di =
  si not di.di_finished alors début
    di.di_finished <- vrai;
    call_if di.di_log_channel
      début fonc (fmt, oc) ->
        Format.fprintf fmt "# Compilation %ssuccessful.@." (si how = `Error alors "un" sinon "");
        close_out oc;
        di.di_log_channel <- None
      fin;
    filtre di.di_display_line avec
    | Classic -> ()
    | Sophisticated ds -> finish_sophisticated ~how ds
  fin
;;
(* ***)
(*** update_tagline_from_tags *)
soit update_tagline_from_tags ds =
  soit tagline = ds.ds_tagline dans
  soit tags = ds.ds_last_tags dans
  soit rec loop i = fonction
    | [] ->
        pour j = i à String.length tagline - 1 faire
          tagline.[j] <- '-'
        fait
    | (tag, c) :: rest ->
        si Tags.mem tag tags alors
          tagline.[i] <- Char.uppercase c
        sinon
          si Tags.mem tag ds.ds_seen_tags alors
            tagline.[i] <- Char.lowercase c
          sinon
            tagline.[i] <- '-';
        loop (i + 1) rest
  dans
  loop 0 ds.ds_tld;
;;
(* ***)
(*** update_sophisticated *)
soit update_sophisticated ds =
  soit t = gettimeofday () dans
  soit dt = t -. ds.ds_last_update dans
  si dt > ds.ds_update_interval alors
    début
      si ds.ds_changed alors
        début
          update_tagline_from_tags ds;
          ds.ds_changed <- faux
        fin;
      redraw_sophisticated ds
    fin
  sinon
    ()
;;
(* ***)
(*** set_target_sophisticated *)
soit set_target_sophisticated ds target tags cached =
  ds.ds_changed <- vrai;
  ds.ds_last_target <- target;
  ds.ds_last_tags <- tags;
  ds.ds_jobs <- 1 + ds.ds_jobs;
  si cached alors ds.ds_jobs_cached <- 1 + ds.ds_jobs_cached;
  ds.ds_last_cached <- cached;
  ds.ds_seen_tags <- Tags.union ds.ds_seen_tags ds.ds_last_tags;
  update_sophisticated ds
;;

soit print_tags f tags =
  soit first = ref vrai dans
  Tags.iter début fonc tag ->
    si !first alors début
      first := faux;
      Format.fprintf f "%s" tag
    fin sinon Format.fprintf f ", %s" tag
  fin tags
;;
(* ***)
(*** update *)
soit update di =
  filtre di.di_display_line avec
  | Classic -> ()
  | Sophisticated ds -> update_sophisticated ds
;;
(* ***)
(*** event *)
soit event di ?(pretend=faux) command target tags =
  call_if di.di_log_channel
    (fonc (fmt, _) ->
      Format.fprintf fmt "# Target: %s, tags: { %a }\n" target print_tags tags;
      Format.fprintf fmt "%s%s@." command (si pretend alors " # cached" sinon ""));
  filtre di.di_display_line avec
  | Classic ->
      si pretend alors
        début
          (* This should work, even on Windows *)
          soit command = Filename.basename command dans
          si di.di_log_level >= 2 alors Format.fprintf di.di_formatter "[cache hit] %s\n%!" command
        fin
      sinon
        (si di.di_log_level >= 1 alors Format.fprintf di.di_formatter "%s\n%!" command)
  | Sophisticated ds ->
      set_target_sophisticated ds target tags pretend;
      update_sophisticated ds
;;
(* ***)
(*** dprintf *)
soit dprintf ?(log_level=1) di fmt =
  si log_level > di.di_log_level alors Discard_printf.discard_printf fmt sinon
  filtre di.di_display_line avec
  | Classic -> Format.fprintf di.di_formatter fmt
  | Sophisticated _ ->
      si log_level < 0 alors
        début
          display di ignore;
          Format.fprintf di.di_formatter fmt
        fin
      sinon
        filtre di.di_log_channel avec
        | Some (f, _) -> Format.fprintf f fmt
        | None -> Discard_printf.discard_printf fmt
(* ***)
