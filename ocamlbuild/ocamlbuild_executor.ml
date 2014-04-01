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
(* Ocamlbuild_executor *)

ouvre Unix;;

type error =
  | Subcommand_failed
  | Subcommand_got_signal
  | Io_error
  | Exceptionl_condition

type task = unit -> string;;

type job = {
  job_id      : int * int;
  job_command : string;
  job_next    : task list;
  job_result  : bool ref; (* Result of this sequence group *)
  job_stdout  : in_channel;
  job_stdin   : out_channel;
  job_stderr  : in_channel;
  job_buffer  : Buffer.t;
  modifiable job_dying : bool;
};;

module JS = Set.Make(struct type t = job soit compare = compare fin);;
module FDM = Map.Make(struct type t = file_descr soit compare = compare fin);;

soit sf = Printf.sprintf;;
soit fp = Printf.fprintf;;

(*** print_unix_status *)
(* FIXME never called *)
soit print_unix_status oc = fonction
  | WEXITED x -> fp oc "exit %d" x
  | WSIGNALED i -> fp oc "signal %d" i
  | WSTOPPED i -> fp oc "stop %d" i
;;
(* ***)
(*** print_job_id *)
soit print_job_id oc (x,y) = fp oc "%d.%d" x y;;
(* ***)
(*** output_lines *)
soit output_lines prefix oc buffer =
  soit u = Buffer.contents buffer dans
  soit m = String.length u dans
  soit output_line i j =
    output_string oc prefix;
    output oc u i (j - i);
    output_char oc '\n'
  dans
  soit rec loop i =
    si i = m alors
      ()
    sinon
      début
        essaie
          soit j = String.index_from u i '\n' dans
          output_line i j;
          loop (j + 1)
        avec
        | Not_found ->
            output_line i m
      fin
  dans
  loop 0
;;
(* ***)
(*** execute *)
(* XXX: Add test for non reentrancy *)
soit execute
  ?(max_jobs=max_int)
  ?(ticker=ignore)
  ?(period=0.1)
  ?(display=(fonc f -> f Pervasives.stdout))
  ~exit
  (commands : task list list)
    =
  soit batch_id = ref 0 dans
  soit env = environment () dans
  soit jobs = ref JS.empty dans
  soit jobs_active = ref 0 dans
  soit jobs_to_terminate = Queue.create () dans
  soit commands_to_execute = Queue.create () dans
  soit all_ok = ref vrai dans
  soit results =
    List.map (fonc tasks ->
      soit result = ref faux dans
      Queue.add (tasks, result) commands_to_execute;
      result)
      commands
  dans
  soit outputs = ref FDM.empty dans
  soit doi = descr_of_in_channel dans
  soit doo = descr_of_out_channel dans
  (*** compute_fds *)
  soit compute_fds =
    soit fds = ref ([], [], []) dans
    soit prev_jobs = ref JS.empty dans
    fonc () ->
      si not (!prev_jobs == !jobs) alors
        début
          prev_jobs := !jobs;
          fds :=
            JS.fold
              début fonc job (rfds, wfds, xfds) ->
                soit ofd = doi job.job_stdout
                et ifd = doo job.job_stdin
                et efd = doi job.job_stderr
                dans
                (ofd :: efd :: rfds, wfds, ofd :: ifd :: efd :: xfds)
              fin
              !jobs
              ([], [], [])
        fin;
      !fds
  dans
  (* ***)
  (*** add_job *)
  soit add_job cmd rest result id =
    (*display begin fun oc -> fp oc "Job %a is %s\n%!" print_job_id id cmd; end;*)
    soit (stdout', stdin', stderr') = open_process_full cmd env dans
    incr jobs_active;
    set_nonblock (doi stdout');
    set_nonblock (doi stderr');
    soit job =
      { job_id          = id;
        job_command     = cmd;
        job_next        = rest;
        job_result      = result;
        job_stdout      = stdout';
        job_stdin       = stdin';
        job_stderr      = stderr';
        job_buffer      = Buffer.create 1024;
        job_dying       = faux }
    dans
    outputs := FDM.add (doi stdout') job (FDM.add (doi stderr') job !outputs);
    jobs := JS.add job !jobs;
  dans
  (* ***)
  (*** skip_empty_tasks *)
  soit rec skip_empty_tasks = fonction
    | [] -> None
    | task :: tasks ->
        soit cmd = task () dans
        si cmd = "" alors skip_empty_tasks tasks sinon Some(cmd, tasks)
  dans
  (* ***)
  (*** add_some_jobs *)
  soit add_some_jobs () =
    soit (tasks, result) = Queue.take commands_to_execute dans
    filtre skip_empty_tasks tasks avec
    | None -> result := faux
    | Some(cmd, rest) ->
      soit b_id = !batch_id dans
      incr batch_id;
      add_job cmd rest result (b_id, 0)
  dans
  (* ***)
  (*** terminate *)
  soit terminate ?(continue=vrai) job =
    si not job.job_dying alors
      début
        job.job_dying <- vrai;
        Queue.add (job, continue) jobs_to_terminate
      fin
    sinon
      ()
  dans
  (* ***)
  (*** add_more_jobs_if_possible *)
  soit add_more_jobs_if_possible () =
    pendant_que !jobs_active < max_jobs && not (Queue.is_empty commands_to_execute) faire
      add_some_jobs ()
    fait
  dans
  (* ***)
  (*** do_read *)
  soit do_read =
    soit u = String.create 4096 dans
    fonc ?(loop=faux) fd job ->
      (*if job.job_dying then
        ()
      else*)
        essaie
          soit rec iteration () =
            soit m =
              essaie
                read fd u 0 (String.length u)
              avec
              | Unix.Unix_error(_,_,_) -> 0
            dans
            si m = 0 alors
              si job.job_dying alors
                ()
              sinon
                terminate job
            sinon
              début
                Buffer.add_substring job.job_buffer u 0 m;
                si loop alors
                  iteration ()
                sinon
                  ()
              fin
          dans
          iteration ()
        avec
        | x ->
            display
              début fonc oc ->
                fp oc "Exception %s while reading output of command %S\n%!" job.job_command
                  (Printexc.to_string x);
              fin;
            exit Io_error
  dans
  (* ***)
  (*** process_jobs_to_terminate *)
  soit process_jobs_to_terminate () =
    pendant_que not (Queue.is_empty jobs_to_terminate) faire
      ticker ();
      soit (job, continue) = Queue.take jobs_to_terminate dans

      (*display begin fun oc -> fp oc "Terminating job %a\n%!" print_job_id job.job_id; end;*)

      decr jobs_active;
      do_read ~loop:vrai (doi job.job_stdout) job;
      do_read ~loop:vrai (doi job.job_stderr) job;
      outputs := FDM.remove (doi job.job_stdout) (FDM.remove (doi job.job_stderr) !outputs);
      jobs := JS.remove job !jobs;
      soit status = close_process_full (job.job_stdout, job.job_stdin, job.job_stderr) dans

      soit shown = ref faux dans

      soit show_command () =
        si !shown alors
          ()
        sinon
        display
          début fonc oc ->
            shown := vrai;
            fp oc "+ %s\n" job.job_command;
            output_lines "" oc job.job_buffer
          fin
      dans
      si Buffer.length job.job_buffer > 0 alors show_command ();
      début
        filtre status avec
        | Unix.WEXITED 0 ->
            début
              si continue alors
                début
                  filtre skip_empty_tasks job.job_next avec
                  | None -> job.job_result := vrai
                  | Some(cmd, rest) ->
                      soit (b_id, s_id) = job.job_id dans
                      add_job cmd rest job.job_result (b_id, s_id + 1)
                fin
              sinon
                all_ok := faux;
            fin
        | Unix.WEXITED rc ->
            show_command ();
            display (fonc oc -> fp oc "Command exited with code %d.\n" rc);
            all_ok := faux;
            exit Subcommand_failed
        | Unix.WSTOPPED s | Unix.WSIGNALED s ->
            show_command ();
            all_ok := faux;
            display (fonc oc -> fp oc "Command got signal %d.\n" s);
            exit Subcommand_got_signal
      fin
    fait
  dans
  (* ***)
  (*** terminate_all_jobs *)
  soit terminate_all_jobs () =
    JS.iter (terminate ~continue:faux) !jobs
  dans
  (* ***)
  (*** loop *)
  soit rec loop () =
    (*display (fun oc -> fp oc "Total %d jobs\n" !jobs_active);*)
    process_jobs_to_terminate ();
    add_more_jobs_if_possible ();
    si JS.is_empty !jobs alors
      ()
    sinon
      début
        soit (rfds, wfds, xfds) = compute_fds () dans
        ticker ();
        soit (chrfds, chwfds, chxfds) = select rfds wfds xfds period dans
        List.iter
          début fonc (fdlist, hook) ->
            List.iter
              début fonc fd ->
                essaie
                  soit job = FDM.find fd !outputs dans
                  ticker ();
                  hook fd job
                avec
                | Not_found -> () (* XXX *)
              fin
              fdlist
          fin
          [chrfds, do_read ~loop:faux;
           chwfds, (fonc _ _ -> ());
           chxfds,
             début fonc _ _job ->
               (*display (fun oc -> fp oc "Exceptional condition on command %S\n%!" job.job_command);
               exit Exceptional_condition*)
               () (* FIXME *)
             fin];
        loop ()
      fin
  dans
  essaie
    loop ();
    None
  avec
  | x ->
      début
        essaie
          terminate_all_jobs ()
        avec
        | x' ->
            display (fonc oc -> fp oc "Extra exception %s\n%!" (Printexc.to_string x'))
      fin;
      Some(List.map (!) results, x)
;;
(* ***)
