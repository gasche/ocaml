(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(************************ Reading and executing commands ***************)

ouvre Int64ops
ouvre Format
ouvre Misc
ouvre Instruct
ouvre Unix
ouvre Debugger_config
ouvre Types
ouvre Primitives
ouvre Unix_tools
ouvre Parser
ouvre Parser_aux
ouvre Lexer
ouvre Input_handling
ouvre Question
ouvre Debugcom
ouvre Program_loading
ouvre Program_management
ouvre Lexing
ouvre Parameters
ouvre Show_source
ouvre Show_information
ouvre Time_travel
ouvre Events
ouvre Symbols
ouvre Source
ouvre Breakpoints
ouvre Checkpoints
ouvre Frames
ouvre Printval

(** Instructions, variables and infos lists. **)
type dbg_instruction =
  { instr_name: string;                 (* Name of command *)
    instr_prio: bool;                   (* Has priority *)
    instr_action: formatter -> lexbuf -> unit;
                                        (* What to do *)
    instr_repeat: bool;                 (* Can be repeated *)
    instr_help: string }                (* Help message *)

soit instruction_list = ref ([] : dbg_instruction list)

type dbg_variable =
  { var_name: string;                   (* Name of variable *)
    var_action: (lexbuf -> unit) * (formatter -> unit);
                                        (* Reading, writing fns *)
    var_help: string }                  (* Help message *)

soit variable_list = ref ([] : dbg_variable list)

type dbg_info =
  { info_name: string;                  (* Name of info *)
    info_action: lexbuf -> unit;        (* What to do *)
    info_help: string }                 (* Help message *)

soit info_list = ref ([] : dbg_info list)

(** Utilities. **)
soit error text =
  eprintf "%s@." text;
  raise Toplevel

soit check_not_windows feature =
  filtre Sys.os_type avec
  | "Win32" ->
      error ("'"^feature^"' feature not supported on Windows")
  | _ ->
      ()

soit eol =
  end_of_line Lexer.lexeme

soit matching_elements list name instr =
  List.filter (fonction a -> isprefix instr (name a)) !list

soit all_matching_instructions =
  matching_elements instruction_list (fonc i -> i.instr_name)

(* itz 04-21-96 don't do priority completion in emacs mode *)
(* XL 25-02-97 why? I find it very confusing. *)

soit matching_instructions instr =
  soit all = all_matching_instructions instr dans
  soit prio = List.filter (fonc i -> i.instr_prio) all dans
  si prio = [] alors all sinon prio

soit matching_variables =
  matching_elements variable_list (fonc v -> v.var_name)

soit matching_infos =
  matching_elements info_list (fonc i -> i.info_name)

soit find_ident name matcher action alternative ppf lexbuf =
  filtre identifier_or_eol Lexer.lexeme lexbuf avec
  | None -> alternative ppf
  | Some ident ->
      filtre matcher ident avec
      | [] -> error ("Unknown " ^ name ^ ".")
      | [a] -> action a ppf lexbuf
      | _ -> error ("Ambiguous " ^ name ^ ".")

soit find_variable action alternative ppf lexbuf =
  find_ident "variable name" matching_variables action alternative ppf lexbuf

soit find_info action alternative ppf lexbuf =
  find_ident "info command" matching_infos action alternative ppf lexbuf

soit add_breakpoint_at_pc pc =
  essaie
    new_breakpoint (any_event_at_pc pc)
  avec
  | Not_found ->
    eprintf "Can't add breakpoint at pc %i: no event there.@." pc;
    raise Toplevel

soit add_breakpoint_after_pc pc =
  soit rec try_add n =
    si n < 3 alors début
      essaie
        new_breakpoint (any_event_at_pc (pc + n * 4))
      avec
      | Not_found ->
        try_add (n+1)
    fin sinon début
      error
        "Can't add breakpoint at beginning of function: no event there"
    fin
  dans try_add 0

soit module_of_longident id =
  filtre id avec
  | Some x -> Some (String.concat "." (Longident.flatten x))
  | None -> None

soit convert_module mdle =
  filtre mdle avec
  | Some m ->
      (* Strip .ml extension if any, and capitalize *)
      String.capitalize(si Filename.check_suffix m ".ml"
                        alors Filename.chop_suffix m ".ml"
                        sinon m)
  | None ->
      essaie
        (get_current_event ()).ev_module
      avec
      | Not_found ->
          error "Not in a module."

(** Toplevel. **)
soit current_line = ref ""

soit interprete_line ppf line =
  current_line := line;
  soit lexbuf = Lexing.from_string line dans
    essaie
      filtre identifier_or_eol Lexer.lexeme lexbuf avec
      | Some x ->
          début filtre matching_instructions x avec
          | [] ->
              error "Unknown command."
          | [i] ->
              i.instr_action ppf lexbuf;
              resume_user_input ();
              i.instr_repeat
          | l ->
              error "Ambiguous command."
          fin
      | None ->
          resume_user_input ();
          faux
    avec
    | Parsing.Parse_error ->
        error "Syntax error."
    | Failure "int_of_string" ->
      error "Integer overflow"

soit line_loop ppf line_buffer =
  resume_user_input ();
  soit previous_line = ref "" dans
    essaie
      pendant_que vrai faire
        si !loaded alors
          History.add_current_time ();
        soit new_line = string_trim (line line_buffer) dans
          soit line =
            si new_line <> "" alors
              new_line
            sinon
              !previous_line
          dans
            previous_line := "";
            si interprete_line ppf line alors
              previous_line := line
      fait
    avec
    | Exit ->
        stop_user_input ()
(*    | Sys_error s ->
        error ("System error: " ^ s) *)

(** Instructions. **)
soit instr_cd ppf lexbuf =
  soit dir = argument_eol argument lexbuf dans
    si ask_kill_program () alors
      essaie
        Sys.chdir (expand_path dir)
      avec
      | Sys_error s ->
          error s

soit instr_shell ppf lexbuf =
  soit cmdarg = argument_list_eol argument lexbuf dans
  soit cmd = String.concat " " cmdarg dans
  (* perhaps we should use $SHELL -c ? *)
  soit err = Sys.command cmd dans
  si (err != 0) alors
    eprintf "Shell command %S failed with exit code %d\n%!" cmd err

soit instr_env ppf lexbuf =
  soit cmdarg = argument_list_eol argument lexbuf dans
  soit cmdarg = string_trim (String.concat " " cmdarg) dans
  si cmdarg <> "" alors
    si ask_kill_program () alors début
      essaie
        soit eqpos = String.index cmdarg '=' dans
        si eqpos = 0 alors raise Not_found;
        soit name = String.sub cmdarg 0 eqpos dans
        soit value =
          String.sub cmdarg (eqpos + 1) (String.length cmdarg - eqpos - 1)
        dans
        Debugger_config.environment :=
          (name, value) :: List.remove_assoc name !Debugger_config.environment
      avec Not_found ->
        eprintf "Environment variable must be in name=value format\n%!"
    fin
  sinon
    List.iter
      (fonc (vvar, vval) -> printf "%s=%s\n%!" vvar vval)
      (List.rev !Debugger_config.environment)

soit instr_pwd ppf lexbuf =
  eol lexbuf;
  fprintf ppf "%s@." (Sys.getcwd ())

soit instr_dir ppf lexbuf =
  soit new_directory = argument_list_eol argument lexbuf dans
    si new_directory = [] alors début
      si yes_or_no "Reinitialize directory list" alors début
        Config.load_path := !default_load_path;
        Envaux.reset_cache ();
        Hashtbl.clear Debugger_config.load_path_for;
        flush_buffer_list ()
        fin
      fin
    sinon début
      soit new_directory' = List.rev new_directory dans
      filtre new_directory' avec
      | mdl :: for_keyw :: tl
        quand (String.lowercase for_keyw) = "for" && (List.length tl) > 0 ->
          List.iter (fonction x -> add_path_for mdl (expand_path x)) tl
      | _ ->
          List.iter (fonction x -> add_path (expand_path x)) new_directory'
    fin;
    soit print_dirs ppf l = List.iter (fonction x -> fprintf ppf "@ %s" x) l dans
    fprintf ppf "@[<2>Directories: %a@]@." print_dirs !Config.load_path;
    Hashtbl.iter
      (fonc mdl dirs ->
         fprintf ppf "@[<2>Source directories for %s: %a@]@." mdl print_dirs
                 dirs)
      Debugger_config.load_path_for

soit instr_kill ppf lexbuf =
  eol lexbuf;
  si not !loaded alors error "The program is not being run.";
  si (yes_or_no "Kill the program being debugged") alors début
    kill_program ();
    show_no_point()
  fin

soit instr_run ppf lexbuf =
  eol lexbuf;
  ensure_loaded ();
  reset_named_values ();
  run ();
  show_current_event ppf;;

soit instr_reverse ppf lexbuf =
  eol lexbuf;
  check_not_windows "reverse";
  ensure_loaded ();
  reset_named_values();
  back_run ();
  show_current_event ppf

soit instr_step ppf lexbuf =
  soit step_count =
    filtre opt_signed_int64_eol Lexer.lexeme lexbuf avec
    | None -> _1
    | Some x -> x
  dans
    ensure_loaded ();
    reset_named_values();
    step step_count;
    show_current_event ppf

soit instr_back ppf lexbuf =
  soit step_count =
    filtre opt_signed_int64_eol Lexer.lexeme lexbuf avec
    | None -> _1
    | Some x -> x
  dans
    check_not_windows "backstep";
    ensure_loaded ();
    reset_named_values();
    step (_0 -- step_count);
    show_current_event ppf

soit instr_finish ppf lexbuf =
  eol lexbuf;
  ensure_loaded ();
  reset_named_values();
  finish ();
  show_current_event ppf

soit instr_next ppf lexbuf =
  soit step_count =
    filtre opt_integer_eol Lexer.lexeme lexbuf avec
    | None -> 1
    | Some x -> x
  dans
    ensure_loaded ();
    reset_named_values();
    next step_count;
    show_current_event ppf

soit instr_start ppf lexbuf =
  eol lexbuf;
  check_not_windows "start";
  ensure_loaded ();
  reset_named_values();
  start ();
  show_current_event ppf

soit instr_previous ppf lexbuf =
  soit step_count =
    filtre opt_integer_eol Lexer.lexeme lexbuf avec
    | None -> 1
    | Some x -> x
  dans
    check_not_windows "previous";
    ensure_loaded ();
    reset_named_values();
    previous step_count;
    show_current_event ppf

soit instr_goto ppf lexbuf =
  soit time = int64_eol Lexer.lexeme lexbuf dans
    ensure_loaded ();
    reset_named_values();
    go_to time;
    show_current_event ppf

soit instr_quit _ =
  raise Exit

soit print_variable_list ppf =
  soit pr_vars ppf = List.iter (fonc v -> fprintf ppf "%s@ " v.var_name) dans
  fprintf ppf "List of variables: %a@." pr_vars !variable_list

soit print_info_list ppf =
  soit pr_infos ppf = List.iter (fonc i -> fprintf ppf "%s@ " i.info_name)  dans
  fprintf ppf "List of info commands: %a@." pr_infos !info_list

soit instr_complete ppf lexbuf =
  soit ppf = Format.err_formatter dans
  soit rec print_list l =
    essaie
      eol lexbuf;
      List.iter (fonction i -> fprintf ppf "%s@." i) l
    avec _ ->
      remove_file !user_channel
  et match_list lexbuf =
    filtre identifier_or_eol Lexer.lexeme lexbuf avec
    | None ->
        List.map (fonc i -> i.instr_name) !instruction_list
    | Some x ->
        filtre matching_instructions x avec
        | [ {instr_name = ("set" | "show" tel i_full)} ] ->
            si x = i_full alors début
              filtre identifier_or_eol Lexer.lexeme lexbuf avec
              | Some ident ->
                  début filtre matching_variables ident avec
                  | [v] -> si v.var_name = ident alors [] sinon [v.var_name]
                  | l   -> List.map (fonc v -> v.var_name) l
                  fin
              | None ->
                  List.map (fonc v -> v.var_name) !variable_list
            fin
            sinon [i_full]
        | [ {instr_name = "info"} ] ->
            si x = "info" alors début
              filtre identifier_or_eol Lexer.lexeme lexbuf avec
              | Some ident ->
                  début filtre matching_infos ident avec
                  | [i] -> si i.info_name = ident alors [] sinon [i.info_name]
                  | l   -> List.map (fonc i -> i.info_name) l
                  fin
              | None ->
                  List.map (fonc i -> i.info_name) !info_list
            fin
            sinon ["info"]
        | [ {instr_name = "help"} ] ->
            si x = "help" alors match_list lexbuf sinon ["help"]
        | [ i ] ->
            si x = i.instr_name alors [] sinon [i.instr_name]
        | l ->
            List.map (fonc i -> i.instr_name) l
  dans
    print_list(match_list lexbuf)

soit instr_help ppf lexbuf =
  soit pr_instrs ppf =
      List.iter (fonc i -> fprintf ppf "%s@ " i.instr_name) dans
  filtre identifier_or_eol Lexer.lexeme lexbuf avec
  | Some x ->
      soit print_help nm hlp =
        eol lexbuf;
        fprintf ppf "%s: %s@." nm hlp dans
      début filtre matching_instructions x avec
      | [] ->
          eol lexbuf;
          fprintf ppf "No matching command.@."
      | [ {instr_name = "set"} ] ->
          find_variable
            (fonc v _ _ ->
               print_help ("set " ^ v.var_name) ("set " ^ v.var_help))
            (fonc ppf ->
               print_help "set" "set debugger variable.";
               print_variable_list ppf)
            ppf
            lexbuf
      | [ {instr_name = "show"} ] ->
          find_variable
            (fonc v _ _ ->
               print_help ("show " ^ v.var_name) ("show " ^ v.var_help))
            (fonc v ->
               print_help "show" "display debugger variable.";
               print_variable_list ppf)
            ppf
            lexbuf
      | [ {instr_name = "info"} ] ->
          find_info
            (fonc i _ _ -> print_help ("info " ^ i.info_name) i.info_help)
            (fonc ppf ->
               print_help "info"
                 "display infos about the program being debugged.";
               print_info_list ppf)
            ppf
            lexbuf
      | [i] ->
          print_help i.instr_name i.instr_help
      | l ->
          eol lexbuf;
          fprintf ppf "Ambiguous command \"%s\": %a@." x pr_instrs l
      fin
  | None ->
      fprintf ppf "List of commands: %a@." pr_instrs !instruction_list

(* Printing values *)

soit print_expr depth ev env ppf expr =
  essaie
    soit (v, ty) = Eval.expression ev env expr dans
    print_named_value depth expr env v ppf ty
  avec
  | Eval.Error msg ->
    Eval.report_error ppf msg;
    raise Toplevel

soit env_of_event =
  fonction
    None    -> Env.empty
  | Some ev ->
      Envaux.env_from_summary ev.Instruct.ev_typenv ev.Instruct.ev_typsubst

soit print_command depth ppf lexbuf =
  soit exprs = expression_list_eol Lexer.lexeme lexbuf dans
  ensure_loaded ();
  soit env =
    essaie
      env_of_event !selected_event
    avec
    | Envaux.Error msg ->
        Envaux.report_error ppf msg;
        raise Toplevel
  dans
  List.iter (print_expr depth !selected_event env ppf) exprs

soit instr_print ppf lexbuf = print_command !max_printer_depth ppf lexbuf

soit instr_display ppf lexbuf = print_command 1 ppf lexbuf

(* Loading of command files *)

soit extract_filename arg =
  (* Allow enclosing filename in quotes *)
  soit l = String.length arg dans
  soit pos1 = si l > 0 && arg.[0] = '"' alors 1 sinon 0 dans
  soit pos2 = si l > 0 && arg.[l-1] = '"' alors l-1 sinon l dans
  String.sub arg pos1 (pos2 - pos1)

soit instr_source ppf lexbuf =
  soit file = extract_filename(argument_eol argument lexbuf)
  et old_state = !interactif
  et old_channel = !user_channel dans
    soit io_chan =
      essaie
        io_channel_of_descr
          (openfile (find_in_path !Config.load_path (expand_path file))
             [O_RDONLY] 0)
      avec
      | Not_found -> error "Source file not found."
      | (Unix_error _) tel x  -> Unix_tools.report_error x; raise Toplevel
    dans
      essaie
        interactif := faux;
        user_channel := io_chan;
        line_loop ppf (Lexing.from_function read_user_input);
        close_io io_chan;
        interactif := old_state;
        user_channel := old_channel
      avec
      | x ->
          stop_user_input ();
          close_io io_chan;
          interactif := old_state;
          user_channel := old_channel;
          raise x

soit instr_set =
  find_variable
    (fonc {var_action = (funct, _)} ppf lexbuf -> funct lexbuf)
    (fonction ppf -> error "Argument required.")

soit instr_show =
  find_variable
    (fonc {var_action = (_, funct)} ppf lexbuf -> eol lexbuf; funct ppf)
    (fonction ppf ->
       List.iter
         (fonction {var_name = nm; var_action = (_, funct)} ->
              fprintf ppf "%s: " nm;
              funct ppf)
         !variable_list)

soit instr_info =
  find_info
    (fonc i ppf lexbuf -> i.info_action lexbuf)
    (fonction ppf ->
       error "\"info\" must be followed by the name of an info command.")

soit instr_break ppf lexbuf =
  soit argument = break_argument_eol Lexer.lexeme lexbuf dans
    ensure_loaded ();
    filtre argument avec
    |  BA_none ->                                (* break *)
        (filtre !selected_event avec
         | Some ev ->
             new_breakpoint ev
         | None ->
             error "Can't add breakpoint at this point.")
    | BA_pc pc ->                               (* break PC *)
        add_breakpoint_at_pc pc
    | BA_function expr ->                       (* break FUNCTION *)
        soit env =
          essaie
            env_of_event !selected_event
          avec
          | Envaux.Error msg ->
              Envaux.report_error ppf msg;
              raise Toplevel
        dans
        début essaie
          soit (v, ty) = Eval.expression !selected_event env expr dans
          filtre (Ctype.repr ty).desc avec
          | Tarrow _ ->
              add_breakpoint_after_pc (Remote_value.closure_code v)
          | _ ->
              eprintf "Not a function.@.";
              raise Toplevel
        avec
        | Eval.Error msg ->
            Eval.report_error ppf msg;
            raise Toplevel
        fin
    | BA_pos1 (mdle, line, column) ->         (* break @ [MODULE] LINE [COL] *)
        soit module_name = convert_module (module_of_longident mdle) dans
        new_breakpoint
          (essaie
             soit buffer =
               essaie get_buffer Lexing.dummy_pos module_name avec
               | Not_found ->
                  eprintf "No source file for %s.@." module_name;
                  raise Toplevel
             dans
             filtre column avec
             | None ->
                 event_at_pos module_name (fst (pos_of_line buffer line))
             | Some col ->
                 event_near_pos module_name (point_of_coord buffer line col)
           avec
           | Not_found -> (* event_at_pos / event_near pos *)
               eprintf "Can't find any event there.@.";
               raise Toplevel
           | Out_of_range -> (* pos_of_line / point_of_coord *)
               eprintf "Position out of range.@.";
               raise Toplevel)
    | BA_pos2 (mdle, position) ->             (* break @ [MODULE] # POSITION *)
        essaie
          new_breakpoint
            (event_near_pos (convert_module (module_of_longident mdle))
                            position)
        avec
        | Not_found ->
            eprintf "Can't find any event there.@."

soit instr_delete ppf lexbuf =
  filtre integer_list_eol Lexer.lexeme lexbuf avec
  | [] ->
      si breakpoints_count () <> 0 && yes_or_no "Delete all breakpoints"
      alors remove_all_breakpoints ()
  | breakpoints ->
      List.iter
        (fonction x -> essaie remove_breakpoint x avec | Not_found -> ())
        breakpoints

soit instr_frame ppf lexbuf =
  soit frame_number =
    filtre opt_integer_eol Lexer.lexeme lexbuf avec
    | None -> !current_frame
    | Some x -> x
  dans
    ensure_loaded ();
    essaie
      select_frame frame_number;
      show_current_frame ppf vrai
    avec
    | Not_found ->
        error ("No frame number " ^ string_of_int frame_number ^ ".")

soit instr_backtrace ppf lexbuf =
  soit number =
    filtre opt_signed_integer_eol Lexer.lexeme lexbuf avec
    | None -> 0
    | Some x -> x dans
  ensure_loaded ();
  filtre current_report() avec
  | None | Some {rep_type = Exited | Uncaught_exc} -> ()
  | Some _ ->
      soit frame_counter = ref 0 dans
      soit print_frame first_frame last_frame = fonction
      | None ->
          fprintf ppf
           "(Encountered a function with no debugging information)@.";
          faux
      | Some event ->
          si !frame_counter >= first_frame alors
            show_one_frame !frame_counter ppf event;
          incr frame_counter;
          si !frame_counter >= last_frame alors début
            fprintf ppf "(More frames follow)@."
          fin;
          !frame_counter < last_frame dans
      fprintf ppf "Backtrace:@.";
      si number = 0 alors
        do_backtrace (print_frame 0 max_int)
      sinon si number > 0 alors
        do_backtrace (print_frame 0 number)
      sinon début
        soit num_frames = stack_depth() dans
        si num_frames < 0 alors
          fprintf ppf
            "(Encountered a function with no debugging information)@."
        sinon
          do_backtrace (print_frame (num_frames + number) max_int)
      fin

soit instr_up ppf lexbuf =
  soit offset =
    filtre opt_signed_integer_eol Lexer.lexeme lexbuf avec
    | None -> 1
    | Some x -> x
  dans
    ensure_loaded ();
    essaie
      select_frame (!current_frame + offset);
      show_current_frame ppf vrai
    avec
    | Not_found -> error "No such frame."

soit instr_down ppf lexbuf =
  soit offset =
    filtre opt_signed_integer_eol Lexer.lexeme lexbuf avec
    | None -> 1
    | Some x -> x
  dans
    ensure_loaded ();
    essaie
      select_frame (!current_frame - offset);
      show_current_frame ppf vrai
    avec
    | Not_found -> error "No such frame."

soit instr_last ppf lexbuf =
  soit count =
    filtre opt_signed_int64_eol Lexer.lexeme lexbuf avec
    | None -> _1
    | Some x -> x
  dans
    check_not_windows "last";
    reset_named_values();
    go_to (History.previous_time count);
    show_current_event ppf

soit instr_list ppf lexbuf =
  soit (mo, beg, e) = list_arguments_eol Lexer.lexeme lexbuf dans
    soit (curr_mod, line, column) =
      essaie
        selected_point ()
      avec
      | Not_found ->
          ("", -1, -1)
    dans
      soit mdle = convert_module (module_of_longident mo) dans
      soit pos = Lexing.dummy_pos dans
      soit buffer =
        essaie get_buffer pos mdle avec
        | Not_found -> error ("No source file for " ^ mdle ^ ".") dans
      soit point =
        si column <> -1 alors
          (point_of_coord buffer line 1) + column
        sinon
          -1 dans
        soit beginning =
          filtre beg avec
          | None quand (mo <> None) || (line = -1) ->
              1
          | None ->
              début essaie
                max 1 (line - 10)
              avec Out_of_range ->
                1
              fin
          | Some x -> x
        dans
          soit en =
            filtre e avec
            | None -> beginning + 20
            | Some x -> x
          dans
            si mdle = curr_mod alors
              show_listing pos mdle beginning en point
                (current_event_is_before ())
            sinon
              show_listing pos mdle beginning en (-1) vrai

(** Variables. **)
soit raw_variable kill name =
  (fonction lexbuf ->
     soit argument = argument_eol argument lexbuf dans
       si (not kill) || ask_kill_program () alors name := argument),
  fonction ppf -> fprintf ppf "%s@." !name

soit raw_line_variable kill name =
  (fonction lexbuf ->
     soit argument = argument_eol line_argument lexbuf dans
       si (not kill) || ask_kill_program () alors name := argument),
  fonction ppf -> fprintf ppf "%s@." !name

soit integer_variable kill min msg name =
  (fonction lexbuf ->
     soit argument = integer_eol Lexer.lexeme lexbuf dans
       si argument < min alors print_endline msg
       sinon si (not kill) || ask_kill_program () alors name := argument),
  fonction ppf -> fprintf ppf "%i@." !name

soit int64_variable kill min msg name =
  (fonction lexbuf ->
     soit argument = int64_eol Lexer.lexeme lexbuf dans
       si argument < min alors print_endline msg
       sinon si (not kill) || ask_kill_program () alors name := argument),
  fonction ppf -> fprintf ppf "%Li@." !name

soit boolean_variable kill name =
  (fonction lexbuf ->
     soit argument =
       filtre identifier_eol Lexer.lexeme lexbuf avec
       | "on" -> vrai
       | "of" | "off" -> faux
       | _ -> error "Syntax error."
     dans
       si (not kill) || ask_kill_program () alors name := argument),
  fonction ppf -> fprintf ppf "%s@." (si !name alors "on" sinon "off")

soit path_variable kill name =
  (fonction lexbuf ->
       soit argument = argument_eol argument lexbuf dans
         si (not kill) || ask_kill_program () alors
           name := make_absolute (expand_path argument)),
  fonction ppf -> fprintf ppf "%s@." !name

soit loading_mode_variable ppf =
  (find_ident
     "loading mode"
     (matching_elements (ref loading_modes) fst)
     (fonc (_, mode) ppf lexbuf ->
        eol lexbuf; set_launching_function mode)
     (fonction ppf -> error "Syntax error.")
     ppf),
  fonction ppf ->
    soit rec find = fonction
      | [] -> ()
      | (name, funct) :: l ->
          si funct == !launching_func alors fprintf ppf "%s" name sinon find l
    dans
      find loading_modes;
      fprintf ppf "@."

soit follow_fork_variable =
  (fonction lexbuf ->
     soit mode =
       filtre identifier_eol Lexer.lexeme lexbuf avec
       | "child" -> Fork_child
       | "parent" -> Fork_parent
       | _ -> error "Syntax error."
     dans
       fork_mode := mode;
       si !loaded alors update_follow_fork_mode ()),
  fonction ppf ->
    fprintf ppf "%s@."
      (filtre !fork_mode avec
         Fork_child -> "child"
       | Fork_parent -> "parent")

(** Infos. **)

soit pr_modules ppf mods =
 soit pr_mods ppf = List.iter (fonction x -> fprintf ppf "%s@ " x) dans
 fprintf ppf "Used modules: @.%a@?" pr_mods mods

soit info_modules ppf lexbuf =
  eol lexbuf;
  ensure_loaded ();
  pr_modules ppf !modules
(********
  print_endline "Opened modules: ";
  if !opened_modules_names = [] then
    print_endline "(no module opened)."
  else
    (List.iter (function x -> print_string x;print_space) !opened_modules_names;
     print_newline ())
*********)

soit info_checkpoints ppf lexbuf =
  eol lexbuf;
  si !checkpoints = [] alors fprintf ppf "No checkpoint.@."
  sinon
    (si !debug_breakpoints alors
       (prerr_endline "               Time   Pid Version";
        List.iter
          (fonction
             {c_time = time; c_pid = pid; c_breakpoint_version = version} ->
               Printf.printf "%19Ld %5d %d\n" time pid version)
          !checkpoints)
     sinon
       (print_endline "               Time   Pid";
        List.iter
          (fonction
             {c_time = time; c_pid = pid} ->
               Printf.printf "%19Ld %5d\n" time pid)
          !checkpoints))

soit info_one_breakpoint ppf (num, ev) =
  fprintf ppf "%3d %10d  %s@." num ev.ev_pos (Pos.get_desc ev);
;;

soit info_breakpoints ppf lexbuf =
  eol lexbuf;
  si !breakpoints = [] alors fprintf ppf "No breakpoints.@."
  sinon début
    fprintf ppf "Num    Address  Where@.";
    List.iter (info_one_breakpoint ppf) (List.rev !breakpoints);
  fin
;;

soit info_events ppf lexbuf =
  ensure_loaded ();
  soit mdle =
    convert_module (module_of_longident (opt_longident_eol Lexer.lexeme lexbuf))
  dans
    print_endline ("Module: " ^ mdle);
    print_endline "   Address  Characters        Kind      Repr.";
    List.iter
      (fonction ev ->
        soit start_char, end_char =
          essaie
            soit buffer = get_buffer (Events.get_pos ev) ev.ev_module dans
            (snd (start_and_cnum buffer ev.ev_loc.Location.loc_start)),
            (snd (start_and_cnum buffer ev.ev_loc.Location.loc_end))
          avec _ ->
            ev.ev_loc.Location.loc_start.Lexing.pos_cnum,
            ev.ev_loc.Location.loc_end.Lexing.pos_cnum dans
        Printf.printf
           "%10d %6d-%-6d  %10s %10s\n"
           ev.ev_pos
           start_char
           end_char
           ((filtre ev.ev_kind avec
               Event_before   -> "before"
             | Event_after _  -> "after"
             | Event_pseudo   -> "pseudo")
            ^
            (filtre ev.ev_info avec
               Event_function -> "/fun"
             | Event_return _ -> "/ret"
             | Event_other    -> ""))
           (filtre ev.ev_repr avec
              Event_none        -> ""
            | Event_parent _    -> "(repr)"
            | Event_child repr  -> string_of_int !repr))
      (events_in_module mdle)

(** User-defined printers **)

soit instr_load_printer ppf lexbuf =
  soit filename = extract_filename(argument_eol argument lexbuf) dans
  essaie
    Loadprinter.loadfile ppf filename
  avec Loadprinter.Error e ->
    Loadprinter.report_error ppf e; raise Toplevel

soit instr_install_printer ppf lexbuf =
  soit lid = longident_eol Lexer.lexeme lexbuf dans
  essaie
    Loadprinter.install_printer ppf lid
  avec Loadprinter.Error e ->
    Loadprinter.report_error ppf e; raise Toplevel

soit instr_remove_printer ppf lexbuf =
  soit lid = longident_eol Lexer.lexeme lexbuf dans
  essaie
    Loadprinter.remove_printer lid
  avec Loadprinter.Error e ->
    Loadprinter.report_error ppf e; raise Toplevel

(** Initialization. **)
soit init ppf =
  instruction_list := [
     { instr_name = "cd"; instr_prio = faux;
       instr_action = instr_cd; instr_repeat = vrai; instr_help =
"set working directory to DIR for debugger and program being debugged." };
     { instr_name = "complete"; instr_prio = faux;
       instr_action = instr_complete; instr_repeat = faux; instr_help =
"complete word at cursor according to context. Useful for Emacs." };
     { instr_name = "pwd"; instr_prio = faux;
       instr_action = instr_pwd; instr_repeat = vrai; instr_help =
"print working directory." };
     { instr_name = "directory"; instr_prio = faux;
       instr_action = instr_dir; instr_repeat = faux; instr_help =
"add directory DIR to beginning of search path for source and\n\
interface files.\n\
Forget cached info on source file locations and line positions.\n\
With no argument, reset the search path." };
     { instr_name = "kill"; instr_prio = faux;
       instr_action = instr_kill; instr_repeat = vrai; instr_help =
"kill the program being debugged." };
     { instr_name = "help"; instr_prio = faux;
       instr_action = instr_help; instr_repeat = vrai; instr_help =
"print list of commands." };
     { instr_name = "quit"; instr_prio = faux;
       instr_action = instr_quit; instr_repeat = faux; instr_help =
"exit the debugger." };
     { instr_name = "shell"; instr_prio = faux;
       instr_action = instr_shell; instr_repeat = vrai; instr_help =
"Execute a given COMMAND thru the system shell." };
     { instr_name = "environment"; instr_prio = faux;
       instr_action = instr_env; instr_repeat = faux; instr_help =
"environment variable to give to program being debugged when it is started." };
      (* Displacements *)
     { instr_name = "run"; instr_prio = vrai;
       instr_action = instr_run; instr_repeat = vrai; instr_help =
"run the program from current position." };
     { instr_name = "reverse"; instr_prio = faux;
       instr_action = instr_reverse; instr_repeat = vrai; instr_help =
"run the program backward from current position." };
     { instr_name = "step"; instr_prio = vrai;
       instr_action = instr_step; instr_repeat = vrai; instr_help =
"step program until it reaches the next event.\n\
Argument N means do this N times (or till program stops for another reason)." };
     { instr_name = "backstep"; instr_prio = vrai;
       instr_action = instr_back; instr_repeat = vrai; instr_help =
"step program backward until it reaches the previous event.\n\
Argument N means do this N times (or till program stops for another reason)." };
     { instr_name = "goto"; instr_prio = faux;
       instr_action = instr_goto; instr_repeat = vrai; instr_help =
"go to the given time." };
     { instr_name = "finish"; instr_prio = vrai;
       instr_action = instr_finish; instr_repeat = vrai; instr_help =
"execute until topmost stack frame returns." };
     { instr_name = "next"; instr_prio = vrai;
       instr_action = instr_next; instr_repeat = vrai; instr_help =
"step program until it reaches the next event.\n\
Skip over function calls.\n\
Argument N means do this N times (or till program stops for another reason)." };
     { instr_name = "start"; instr_prio = faux;
       instr_action = instr_start; instr_repeat = vrai; instr_help =
"execute backward until the current function is exited." };
     { instr_name = "previous"; instr_prio = faux;
       instr_action = instr_previous; instr_repeat = vrai; instr_help =
"step program until it reaches the previous event.\n\
Skip over function calls.\n\
Argument N means do this N times (or till program stops for another reason)." };
     { instr_name = "print"; instr_prio = vrai;
       instr_action = instr_print; instr_repeat = vrai; instr_help =
"print value of expressions (deep printing)." };
     { instr_name = "display"; instr_prio = vrai;
       instr_action = instr_display; instr_repeat = vrai; instr_help =
"print value of expressions (shallow printing)." };
     { instr_name = "source"; instr_prio = faux;
       instr_action = instr_source; instr_repeat = vrai; instr_help =
"read command from file FILE." };
     (* Breakpoints *)
     { instr_name = "break"; instr_prio = faux;
       instr_action = instr_break; instr_repeat = faux; instr_help =
"Set breakpoint at specified line or function.\
\nSyntax: break function-name\
\n        break @ [module] linenum\
\n        break @ [module] # characternum" };
     { instr_name = "delete"; instr_prio = faux;
       instr_action = instr_delete; instr_repeat = faux; instr_help =
"delete some breakpoints.\n\
Arguments are breakpoint numbers with spaces in between.\n\
To delete all breakpoints, give no argument." };
     { instr_name = "set"; instr_prio = faux;
       instr_action = instr_set; instr_repeat = faux; instr_help =
"--unused--" };
     { instr_name = "show"; instr_prio = faux;
       instr_action = instr_show; instr_repeat = vrai; instr_help =
"--unused--" };
     { instr_name = "info"; instr_prio = faux;
       instr_action = instr_info; instr_repeat = vrai; instr_help =
"--unused--" };
     (* Frames *)
     { instr_name = "frame"; instr_prio = faux;
       instr_action = instr_frame; instr_repeat = vrai; instr_help =
"select and print a stack frame.\n\
With no argument, print the selected stack frame.\n\
An argument specifies the frame to select." };
     { instr_name = "backtrace"; instr_prio = faux;
       instr_action = instr_backtrace; instr_repeat = vrai; instr_help =
"print backtrace of all stack frames, or innermost COUNT frames.\n\
With a negative argument, print outermost -COUNT frames." };
     { instr_name = "bt"; instr_prio = faux;
       instr_action = instr_backtrace; instr_repeat = vrai; instr_help =
"print backtrace of all stack frames, or innermost COUNT frames.\n\
With a negative argument, print outermost -COUNT frames." };
     { instr_name = "up"; instr_prio = faux;
       instr_action = instr_up; instr_repeat = vrai; instr_help =
"select and print stack frame that called this one.\n\
An argument says how many frames up to go." };
     { instr_name = "down"; instr_prio = faux;
       instr_action = instr_down; instr_repeat = vrai; instr_help =
"select and print stack frame called by this one.\n\
An argument says how many frames down to go." };
     { instr_name = "last"; instr_prio = vrai;
       instr_action = instr_last; instr_repeat = vrai; instr_help =
"go back to previous time." };
     { instr_name = "list"; instr_prio = faux;
       instr_action = instr_list; instr_repeat = vrai; instr_help =
"list the source code." };
     (* User-defined printers *)
     { instr_name = "load_printer"; instr_prio = faux;
       instr_action = instr_load_printer; instr_repeat = faux; instr_help =
"load in the debugger a .cmo or .cma file containing printing functions." };
     { instr_name = "install_printer"; instr_prio = faux;
       instr_action = instr_install_printer; instr_repeat = faux; instr_help =
"use the given function for printing values of its input type.\n\
The code for the function must have previously been loaded in the debugger\n\
using \"load_printer\"." };
     { instr_name = "remove_printer"; instr_prio = faux;
       instr_action = instr_remove_printer; instr_repeat = faux; instr_help =
"stop using the given function for printing values of its input type." }
];
  variable_list := [
    (* variable name, (writing, reading), help reading, help writing *)
     { var_name = "arguments";
       var_action = raw_line_variable vrai arguments;
       var_help =
"arguments to give program being debugged when it is started." };
     { var_name = "program";
       var_action = path_variable vrai program_name;
       var_help =
"name of program to be debugged." };
     { var_name = "loadingmode";
       var_action = loading_mode_variable ppf;
       var_help =
"mode of loading.\n\
It can be either:\n\
  direct: the program is directly called by the debugger.\n\
  runtime: the debugger execute `ocamlrun programname arguments'.\n\
  manual: the program is not launched by the debugger,\n\
    but manually by the user." };
     { var_name = "processcount";
       var_action = integer_variable faux 1 "Must be >= 1."
                                     checkpoint_max_count;
       var_help =
"maximum number of process to keep." };
     { var_name = "checkpoints";
       var_action = boolean_variable faux make_checkpoints;
       var_help =
"whether to make checkpoints or not." };
     { var_name = "bigstep";
       var_action = int64_variable faux _1 "Must be >= 1."
                                     checkpoint_big_step;
       var_help =
"step between checkpoints during long displacements." };
     { var_name = "smallstep";
       var_action = int64_variable faux _1 "Must be >= 1."
                                     checkpoint_small_step;
       var_help =
"step between checkpoints during small displacements." };
     { var_name = "socket";
       var_action = raw_variable vrai socket_name;
       var_help =
"name of the socket used by communications debugger-runtime." };
     { var_name = "history";
       var_action = integer_variable faux 0 "" history_size;
       var_help =
"history size." };
     { var_name = "print_depth";
       var_action = integer_variable faux 1 "Must be at least 1"
                                     max_printer_depth;
       var_help =
"maximal depth for printing of values." };
     { var_name = "print_length";
       var_action = integer_variable faux 1 "Must be at least 1"
                                     max_printer_steps;
       var_help =
"maximal number of value nodes printed." };
     { var_name = "follow_fork_mode";
       var_action = follow_fork_variable;
       var_help =
"process to follow after forking.\n\
It can be either :
  child: the newly created process.\n\
  parent: the process that called fork.\n" }];

  info_list :=
    (* info name, function, help *)
    [{ info_name = "modules";
       info_action = info_modules ppf;
       info_help = "list opened modules." };
     { info_name = "checkpoints";
       info_action = info_checkpoints ppf;
       info_help = "list checkpoints." };
     { info_name = "breakpoints";
       info_action = info_breakpoints ppf;
       info_help = "list breakpoints." };
     { info_name = "events";
       info_action = info_events ppf;
       info_help = "list events in MODULE (default is current module)." }]

soit _ = init std_formatter
