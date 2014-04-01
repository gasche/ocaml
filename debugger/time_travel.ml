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

(**************************** Time travel ******************************)

ouvre Int64ops
ouvre Instruct
ouvre Events
ouvre Debugcom
ouvre Primitives
ouvre Checkpoints
ouvre Breakpoints
ouvre Trap_barrier
ouvre Input_handling
ouvre Debugger_config
ouvre Program_loading
ouvre Question

exception Current_checkpoint_lost
exception Current_checkpoint_lost_start_at de int64 * int64

soit remove_1st key list =
  soit rec remove =
    fonction
      []   -> []
    | a::l -> si a == key alors l sinon a::(remove l)
  dans
    remove list

(*** Debugging. ***)

soit debug_time_travel = ref faux

(*** Internal utilities. ***)

(* Insert a checkpoint in the checkpoint list.
 * Raise `Exit' if there is already a checkpoint at the same time.
 *)
soit insert_checkpoint ({c_time = time} tel checkpoint) =
  soit rec traverse =
    fonction
      [] -> [checkpoint]
    | (({c_time = t} tel a)::l) tel l' ->
        si t > time alors
          a::(traverse l)
        sinon si t = time alors
          raise Exit
        sinon
          checkpoint::l'
  dans
    checkpoints := traverse !checkpoints

(* Remove a checkpoint from the checkpoint list.
 * --- No error if not found.
 *)
soit remove_checkpoint checkpoint =
  checkpoints := remove_1st checkpoint !checkpoints

(* Wait for the process used by `checkpoint' to connect.
 * --- Usually not called (the process is already connected).
 *)
soit wait_for_connection checkpoint =
  essaie
    Exec.unprotect
      (fonction () ->
         soit old_controller = Input_handling.current_controller !connection dans
           execute_with_other_controller
             (fonction
                fd ->
                  old_controller fd;
                  si checkpoint.c_valid = vrai alors
                    exit_main_loop ())
             !connection
             main_loop)
  avec
    Sys.Break ->
      checkpoint.c_parent <- root;
      remove_checkpoint checkpoint;
      checkpoint.c_pid <- -1;
      raise Sys.Break

(* Select a checkpoint as current. *)
soit set_current_checkpoint checkpoint =
  si !debug_time_travel alors
    prerr_endline ("Select: " ^ (string_of_int checkpoint.c_pid));
  si not checkpoint.c_valid alors
    wait_for_connection checkpoint;
  current_checkpoint := checkpoint;
  set_current_connection checkpoint.c_fd

(* Kill `checkpoint'. *)
soit kill_checkpoint checkpoint =
  si !debug_time_travel alors
    prerr_endline ("Kill: " ^ (string_of_int checkpoint.c_pid));
  si checkpoint.c_pid > 0 alors          (* Ghosts don't have to be killed ! *)
    (si not checkpoint.c_valid alors
       wait_for_connection checkpoint;
     stop checkpoint.c_fd;
     si checkpoint.c_parent.c_pid > 0 alors
       wait_child checkpoint.c_parent.c_fd;
     checkpoint.c_parent <- root;
     close_io checkpoint.c_fd;
     remove_file checkpoint.c_fd;
     remove_checkpoint checkpoint);
  checkpoint.c_pid <- -1                (* Don't exist anymore *)

(*** Cleaning the checkpoint list. ***)

(* Separe checkpoints before (<=) and after (>) `t'. *)
(* ### t checkpoints -> (after, before) *)
soit cut t =
  soit rec cut_t =
    fonction
      [] -> ([], [])
    | ({c_time = t'} tel a::l) tel l' ->
        si t' <= t alors
          ([], l')
        sinon
          soit (b, e) = cut_t l dans
            (a::b, e)
  dans
    cut_t

(* Partition the checkpoints list. *)
soit cut2 t0 t l =
  soit rec cut2_t0 t =
    fonction
      [] -> []
    | l ->
       soit (after, before) = cut (t0 -- t -- _1) l dans
         soit l = cut2_t0 (t ++ t) before dans
           after::l
  dans
    soit (after, before) = cut (t0 -- _1) l dans
      after::(cut2_t0 t before)

(* Separe first elements and last element of a list of checkpoint. *)
soit chk_merge2 cont =
  soit rec chk_merge2_cont =
    fonction
      [] -> cont
    | [a] ->
        soit (accepted, rejected) = cont dans
          (a::accepted, rejected)
    | a::l ->
        soit (accepted, rejected) = chk_merge2_cont l dans
          (accepted, a::rejected)
  dans chk_merge2_cont

(* Separe the checkpoint list. *)
(* ### list -> accepted * rejected *)
soit rec chk_merge =
  fonction
    [] -> ([], [])
  | l::tail ->
       chk_merge2 (chk_merge tail) l

soit new_checkpoint_list checkpoint_count accepted rejected =
  si List.length accepted >= checkpoint_count alors
    soit (k, l) = list_truncate2 checkpoint_count accepted dans
      (k, l @ rejected)
  sinon
    soit (k, l) =
      list_truncate2 (checkpoint_count - List.length accepted) rejected
    dans
      (List.merge (fonc {c_time = t1} {c_time = t2} -> compare t2 t1) accepted k,
       l)

(* Clean the checkpoint list. *)
(* Reference time is `time'. *)
soit clean_checkpoints time checkpoint_count =
  soit (after, before) = cut time !checkpoints dans
    soit (accepted, rejected) =
      chk_merge (cut2 time !checkpoint_small_step before)
    dans
      soit (kept, lost) =
        new_checkpoint_list checkpoint_count accepted after
      dans
        List.iter kill_checkpoint (lost @ rejected);
        checkpoints := kept

(*** Internal functions for moving. ***)

(* Find the first checkpoint before (or at) `time'.
 * Ask for reloading the program if necessary.
 *)
soit find_checkpoint_before time =
  soit rec find =
    fonction
      [] ->
        print_string "Can't go that far in the past !"; print_newline ();
        si yes_or_no "Reload program" alors début
          load_program ();
          find !checkpoints
          fin
        sinon
          raise Toplevel
    | { c_time = t } tel a::l ->
        si t > time alors
          find l
        sinon
          a
  dans find !checkpoints

(* Make a copy of the current checkpoint and clean the checkpoint list. *)
(* --- The new checkpoint in not put in the list. *)
soit duplicate_current_checkpoint () =
  soit checkpoint = !current_checkpoint dans
    si not checkpoint.c_valid alors
      wait_for_connection checkpoint;
    soit new_checkpoint =                        (* Ghost *)
      {c_time = checkpoint.c_time;
       c_pid = 0;
       c_fd = checkpoint.c_fd;
       c_valid = faux;
       c_report = checkpoint.c_report;
       c_state = C_stopped;
       c_parent = checkpoint;
       c_breakpoint_version = checkpoint.c_breakpoint_version;
       c_breakpoints = checkpoint.c_breakpoints;
       c_trap_barrier = checkpoint.c_trap_barrier}
    dans
      checkpoints := list_replace checkpoint new_checkpoint !checkpoints;
      set_current_checkpoint checkpoint;
      clean_checkpoints (checkpoint.c_time ++ _1) (!checkpoint_max_count - 1);
      si new_checkpoint.c_pid = 0 alors  (* The ghost has not been killed *)
        (filtre do_checkpoint () avec    (* Duplicate checkpoint *)
           Checkpoint_done pid ->
             (new_checkpoint.c_pid <- pid;
              si !debug_time_travel alors
                prerr_endline ("Waiting for connection: " ^ string_of_int pid))
         | Checkpoint_failed ->
             prerr_endline
               "A fork failed. Reducing maximum number of checkpoints.";
             checkpoint_max_count := List.length !checkpoints - 1;
             remove_checkpoint new_checkpoint)

(* Was the movement interrupted ? *)
(* --- An exception could have been used instead, *)
(* --- but it is not clear where it should be caught. *)
(* --- For instance, it should not be caught in `step' *)
(* --- (as `step' is used in `next_1'). *)
(* --- On the other side, other modules does not need to know *)
(* --- about this exception. *)
soit interrupted = ref faux

(* Informations about last breakpoint encountered *)
soit last_breakpoint = ref None

(* Ensure we stop on an event. *)
soit rec stop_on_event report =
  filtre report avec
    {rep_type = Breakpoint; rep_program_pointer = pc;
     rep_stack_pointer = sp} ->
      last_breakpoint := Some (pc, sp);
      Symbols.update_current_event ();
      début filtre !current_event avec
        None   -> find_event ()
      | Some _ -> ()
      fin
  | {rep_type = Trap_barrier; rep_stack_pointer = trap_frame} ->
      (* No event at current position. *)
      find_event ()
  | _ ->
      ()

et find_event () =
  si !debug_time_travel alors début
    print_string "Searching next event...";
    print_newline ()
  fin;
  soit report = do_go _1 dans
  !current_checkpoint.c_report <- Some report;
  stop_on_event report

(* Internal function for running debugged program.
 * Requires `duration > 0'.
 *)
soit internal_step duration =
  filtre current_report () avec
    Some {rep_type = Exited | Uncaught_exc} -> ()
  | _ ->
      Exec.protect
        (fonction () ->
           si !make_checkpoints alors
             duplicate_current_checkpoint ()
           sinon
             remove_checkpoint !current_checkpoint;
           update_breakpoints ();
           update_trap_barrier ();
           !current_checkpoint.c_state <- C_running duration;
           soit report = do_go duration dans
             !current_checkpoint.c_report <- Some report;
             !current_checkpoint.c_state <- C_stopped;
             si report.rep_type = Event alors début
               !current_checkpoint.c_time <-
                 !current_checkpoint.c_time ++ duration;
               interrupted := faux;
               last_breakpoint := None
               fin
             sinon début
               !current_checkpoint.c_time <-
                  !current_checkpoint.c_time ++ duration
                  -- (Int64.of_int report.rep_event_count) ++ _1;
               interrupted := vrai;
               last_breakpoint := None;
               stop_on_event report
               fin;
             (essaie
                insert_checkpoint !current_checkpoint
              avec
                Exit ->
                  kill_checkpoint !current_checkpoint;
                  set_current_checkpoint
                    (find_checkpoint_before (current_time ()))));
        si !debug_time_travel alors début
          print_string "Checkpoints: pid(time)"; print_newline ();
          List.iter
            (fonction {c_time = time; c_pid = pid; c_valid = valid} ->
              Printf.printf "%d(%Ld)%s " pid time
                            (si valid alors "" sinon "(invalid)"))
            !checkpoints;
          print_newline ()
        fin

(*** Miscellaneous functions (exported). ***)

(* Create a checkpoint at time 0 (new program). *)
soit new_checkpoint pid fd =
  soit new_checkpoint =
    {c_time = _0;
     c_pid = pid;
     c_fd = fd;
     c_valid = vrai;
     c_report = None;
     c_state = C_stopped;
     c_parent = root;
     c_breakpoint_version = 0;
     c_breakpoints = [];
     c_trap_barrier = 0}
  dans
    insert_checkpoint new_checkpoint

(* Set the file descriptor of a checkpoint *)
(* (a new process has connected with the debugger). *)
(* --- Return `true' on success (close the connection otherwise). *)
soit set_file_descriptor pid fd =
  soit rec find =
    fonction
      [] ->
        prerr_endline "Unexpected connection";
        close_io fd;
        faux
    | ({c_pid = pid'} tel checkpoint)::l ->
        si pid <> pid' alors
          find l
        sinon
          (checkpoint.c_fd <- fd;
           checkpoint.c_valid <- vrai;
           vrai)
  dans
    si !debug_time_travel alors
      prerr_endline ("New connection: " ^(string_of_int pid));
    find (!current_checkpoint::!checkpoints)

(* Kill all the checkpoints. *)
soit kill_all_checkpoints () =
  List.iter kill_checkpoint (!current_checkpoint::!checkpoints)

(* Kill a checkpoint without killing the process. *)
(* (used when connection with the process is lost). *)
(* --- Assume that the checkpoint is valid. *)
soit forget_process fd pid =
  soit checkpoint =
    List.find (fonction c -> c.c_pid = pid) (!current_checkpoint::!checkpoints)
  dans
    Printf.eprintf "Lost connection with process %d" pid;
    soit kont =
      si checkpoint == !current_checkpoint alors début
        Printf.eprintf " (active process)\n";
        filtre !current_checkpoint.c_state avec
          C_stopped ->
            Printf.eprintf "at time %Ld" !current_checkpoint.c_time;
            fonc () -> raise Current_checkpoint_lost
        | C_running duration ->
            Printf.eprintf "between time %Ld and time %Ld"
                          !current_checkpoint.c_time
                          (!current_checkpoint.c_time ++ duration);
            fonc () -> raise (Current_checkpoint_lost_start_at
                              (!current_checkpoint.c_time, duration))
        fin
      sinon ignore dans
    Printf.eprintf "\n"; flush stderr;
    Input_handling.remove_file fd;
    close_io checkpoint.c_fd;
    remove_file checkpoint.c_fd;
    remove_checkpoint checkpoint;
    checkpoint.c_pid <- -1;             (* Don't exist anymore *)
    si checkpoint.c_parent.c_pid > 0 alors
      wait_child checkpoint.c_parent.c_fd;
    kont ()

(* Try to recover when the current checkpoint is lost. *)
soit recover () =
  set_current_checkpoint
    (find_checkpoint_before (current_time ()))

(*** Simple movements. ***)

(* Forward stepping.  Requires `duration >= 0'. *)
soit rec step_forward duration =
  si duration > !checkpoint_small_step alors début
    soit first_step =
      si duration > !checkpoint_big_step alors
        !checkpoint_big_step
      sinon
        !checkpoint_small_step
    dans
      internal_step first_step;
      si not !interrupted alors
        step_forward (duration -- first_step)
    fin
  sinon si duration != _0 alors
    internal_step duration

(* Go to time `time' from current checkpoint (internal). *)
soit internal_go_to time =
  soit duration = time -- (current_time ()) dans
    si duration > _0 alors
      execute_without_breakpoints (fonction () -> step_forward duration)

(* Move to a given time. *)
soit go_to time =
  soit checkpoint = find_checkpoint_before time dans
    set_current_checkpoint checkpoint;
    internal_go_to time

(* Return the time of the last breakpoint *)
(* between current time and `max_time'. *)
soit rec find_last_breakpoint max_time =
  soit rec find break =
    soit time = current_time () dans
    step_forward (max_time -- time);
    filtre !last_breakpoint, !temporary_breakpoint_position avec
      (Some _, _) quand current_time () < max_time ->
        find !last_breakpoint
    | (Some (pc, _), Some pc') quand pc = pc' ->
        (max_time, !last_breakpoint)
    | _ ->
        (time, break)
  dans
    find
      (filtre current_pc_sp () avec
         (Some (pc, _)) tel state quand breakpoint_at_pc pc -> state
       | _                                                -> None)


(* Run from `time_max' back to `time'. *)
(* --- Assume 0 <= time < time_max *)
soit rec back_to time time_max =
  soit
    {c_time = t} = find_checkpoint_before (pre64 time_max)
  dans
    go_to (max time t);
    soit (new_time, break) = find_last_breakpoint time_max dans
    si break <> None || (new_time <= time) alors début
      go_to new_time;
      interrupted := break <> None;
      last_breakpoint := break
    fin sinon
      back_to time new_time

(* Backward stepping. *)
(* --- Assume duration > 1 *)
soit step_backward duration =
  soit time = current_time () dans
    si time > _0 alors
      back_to (max _0 (time -- duration)) time

(* Run the program from current time. *)
(* Stop at the first breakpoint, or at the end of the program. *)
soit rec run () =
  internal_step !checkpoint_big_step;
  si not !interrupted alors
    run ()

(* Run backward the program form current time. *)
(* Stop at the first breakpoint, or at the beginning of the program. *)
soit back_run () =
  si current_time () > _0 alors
    back_to _0 (current_time ())

(* Step in any direction. *)
(* Stop at the first brakpoint, or after `duration' steps. *)
soit step duration =
  si duration >= _0 alors
    step_forward duration
  sinon
    step_backward (_0 -- duration)

(*** Next, finish. ***)

(* Finish current function. *)
soit finish () =
  Symbols.update_current_event ();
  filtre !current_event avec
    None ->
      prerr_endline "`finish' not meaningful in outermost frame.";
      raise Toplevel
  | Some curr_event ->
      set_initial_frame();
      soit (frame, pc) = up_frame curr_event.ev_stacksize dans
      si frame < 0 alors début
        prerr_endline "`finish' not meaningful in outermost frame.";
        raise Toplevel
      fin;
      début
        essaie ignore(Symbols.any_event_at_pc pc)
        avec Not_found ->
               prerr_endline "Calling function has no debugging information.";
               raise Toplevel
      fin;
      exec_with_trap_barrier
        frame
        (fonc () ->
           exec_with_temporary_breakpoint
             pc
             (fonc () ->
                pendant_que
                  run ();
                  filtre !last_breakpoint avec
                    Some (pc', frame') quand pc = pc' ->
                      interrupted := faux;
                      frame <> frame'
                  | _ ->
                      faux
                faire
                  ()
                fait))

soit next_1 () =
  Symbols.update_current_event ();
  filtre !current_event avec
    None ->                             (* Beginning of the program. *)
      step _1
  | Some event1 ->
      soit (frame1, pc1) = initial_frame() dans
      step _1;
      si not !interrupted alors début
        Symbols.update_current_event ();
        filtre !current_event avec
          None -> ()
        | Some event2 ->
            soit (frame2, pc2) = initial_frame() dans
            (* Call `finish' if we've entered a function. *)
            si frame1 >= 0 && frame2 >= 0 &&
               frame2 - event2.ev_stacksize > frame1 - event1.ev_stacksize
            alors finish()
      fin

(* Same as `step' (forward) but skip over function calls. *)
soit rec next =
  fonction
    0 -> ()
  | n ->
      next_1 ();
      si not !interrupted alors
        next (n - 1)

(* Run backward until just before current function. *)
soit start () =
  Symbols.update_current_event ();
  filtre !current_event avec
    None ->
      prerr_endline "`start not meaningful in outermost frame.";
      raise Toplevel
  | Some curr_event ->
      soit (frame, _) = initial_frame() dans
      soit (frame', pc) = up_frame curr_event.ev_stacksize dans
      si frame' < 0 alors début
        prerr_endline "`start not meaningful in outermost frame.";
        raise Toplevel
      fin;
      soit nargs =
        filtre
          essaie Symbols.any_event_at_pc pc avec Not_found ->
            prerr_endline "Calling function has no debugging information.";
            raise Toplevel
        avec
          {ev_info = Event_return nargs} -> nargs
        | _ ->  Misc.fatal_error "Time_travel.start"
      dans
      soit offset = si nargs < 4 alors 1 sinon 2 dans
      soit pc = pc - 4 * offset dans
      pendant_que
        exec_with_temporary_breakpoint pc back_run;
        filtre !last_breakpoint avec
          Some (pc', frame') quand pc = pc' ->
            step _minus1;
            (not !interrupted)
              &&
            (frame' - nargs > frame - curr_event.ev_stacksize)
        | _ ->
            faux
      faire
        ()
      fait

soit previous_1 () =
  Symbols.update_current_event ();
  filtre !current_event avec
    None ->                             (* End of the program. *)
      step _minus1
  | Some event1 ->
      soit (frame1, pc1) = initial_frame() dans
      step _minus1;
      si not !interrupted alors début
        Symbols.update_current_event ();
        filtre !current_event avec
          None -> ()
        | Some event2 ->
            soit (frame2, pc2) = initial_frame() dans
            (* Call `start' if we've entered a function. *)
            si frame1 >= 0 && frame2 >= 0 &&
               frame2 - event2.ev_stacksize > frame1 - event1.ev_stacksize
            alors start()
      fin

(* Same as `step' (backward) but skip over function calls. *)
soit rec previous =
  fonction
    0 -> ()
  | n ->
      previous_1 ();
      si not !interrupted alors
        previous (n - 1)
