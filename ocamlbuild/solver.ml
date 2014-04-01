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


(* Original author: Nicolas Pouillard *)
ouvre My_std
ouvre Log
ouvre Format
ouvre Outcome

type backtrace =
  | Leaf de Pathname.t
  | Choice de backtrace list
  | Depth de Pathname.t * backtrace
  | Target de string * backtrace
exception Failed de backtrace
exception Circular de Pathname.t * Pathname.t list

soit failed target backtrace =
  Resource.Cache.resource_failed target;
  raise (Failed backtrace)

soit rec pp_repeat f (n, s) =
  si n > 0 alors (pp_print_string f s; pp_repeat f (n - 1, s))

(* Targets must be normalized pathnames.
 * Recursive calls are either on input targets
 * or dependencies of these targets (returned by Rule.deps_of_rule).
 *)
soit rec self depth on_the_go_orig target =
  soit rules = Rule.get_rules () dans
  soit on_the_go = target :: on_the_go_orig dans

  dprintf 4 "==%a> %a" pp_repeat (depth, "==") Resource.print target;
  si List.mem target on_the_go_orig alors raise (Circular(target, on_the_go_orig));
  filtre Resource.Cache.resource_state target avec
  | Resource.Cache.Bbuilt ->
      (dprintf 5 "%a already built" Resource.print target)
  | Resource.Cache.Bcannot_be_built ->
      (dprintf 5 "%a already failed" Resource.print target; failed target (Leaf target))
  | Resource.Cache.Bsuspension(s) ->
      (dprintf 5 "%a was suspended -> resuming" Resource.print target;
       Resource.Cache.resume_suspension s)
  | Resource.Cache.Bnot_built_yet ->
    si not (Pathname.is_relative target) && Pathname.exists target alors
      si Resource.Cache.external_is_up_to_date target alors ()
      sinon (* perhaps the error can be refined *) failed target (Leaf target)
    sinon
    si Resource.exists_in_source_dir target alors
      Resource.Cache.import_in_build_dir target
    sinon
    filtre List.filter_opt (Rule.can_produce target) rules avec
    | [] -> failed target (Leaf target)
    | matching_rules ->
      soit rec until_works rs backtraces =
        filtre rs avec
        | [] -> affirme faux
        | r :: rs ->
            essaie
              List.iter (force_self (depth + 1) on_the_go) (Rule.deps_of_rule r);
              essaie
                Rule.call (self_firsts (depth + 1) on_the_go) r
              avec Rule.Failed -> raise (Failed (Leaf target))
            avec Failed backtrace ->
              si rs = [] alors failed target (Depth (target, Choice (backtrace :: backtraces)))
              sinon
                soit () =
                  filtre backtrace avec
                  | Depth (top_prod, _) -> Resource.Cache.clear_resource_failed top_prod
                  | Target _ | Choice _ | Leaf _ -> ()
                dans until_works rs (backtrace :: backtraces)
      dans until_works matching_rules []

(* Build the first target that is buildable *)
et self_first depth on_the_go already_failed rs =
  filtre rs avec
  | [] -> Bad (Failed (Choice already_failed))
  | r :: rs ->
      essaie self depth on_the_go r; Good r
      avec Failed backtrace -> self_first depth on_the_go (backtrace :: already_failed) rs

(* This variant is the one (once partially applied) called the 'build'
 * function in the rule actions.
 *
 * This one takes a list of list of pathnames to build.
 * This is a parallel conjonction of sequential alternatives.
 * This means that in each sublist of pathnames, the first
 * target that is buildable will be picked. The outer list
 * denotes that one can build each target in parallel.
 *)
et self_firsts depth on_the_go rss =
  soit results = List.map (self_first depth on_the_go []) rss dans
  soit cmds, thunks =
    List.fold_right début fonc res ((acc1, acc2) tel acc) ->
      filtre res avec
      | Bad _ -> acc
      | Good res ->
          filtre Resource.Cache.get_optional_resource_suspension res avec
          | None -> acc
          | Some (cmd, thunk) -> (cmd :: acc1, thunk :: acc2)
    fin results ([], []) dans
  soit count = List.length cmds dans
  soit job_debug = si !Command.jobs = 1 alors 10 sinon 5 dans
  si count > 1 alors dprintf job_debug ">>> PARALLEL: %d" count;
  soit opt_exn = Command.execute_many cmds dans
  si count > 1 alors dprintf job_debug "<<< PARALLEL";
  début filtre opt_exn avec
  | Some(res, exn) ->
      List.iter2 (fonc res thunk -> si res alors thunk ()) res thunks;
      Log.finish ~how:`Error ();
      raise exn
  | None ->
      List.iter (fonc thunk -> thunk ()) thunks
  fin;
  results
et force_self depth on_the_go x = self depth on_the_go x; Resource.Cache.resume_resource x

soit solve = force_self 0 []
soit solve_target name rs =
  filtre self_first 0 [] [] rs avec
  | Good res -> Resource.Cache.resume_resource res; res
  | Bad (Failed backtrace) -> raise (Failed (Target (name, backtrace)))
  | Bad exn -> raise exn
