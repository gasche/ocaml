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
open My_std
open Format
open Log
open Outcome
module Resources = Resource.Resources

exception Exit_rule_error of string
exception Failed

type env = Pathname.t -> Pathname.t

type rule_id = {
  id_name: string;
  id_prods: Pathname.t list;
}

type build_result = (Pathname.t, exn) Outcome.t
type builder = Pathname.t list list -> build_result list
type build_order = (Pathname.t list * (build_result -> unit)) list
type 'a gen_build_order = ('a * Pathname.t list * (build_result -> unit)) list
type build_wrapper = builder -> builder

type 'a gen_action = env -> 'a action_result
and 'a action_result =
| Return of 'a
| Order of rule_id option gen_build_order * (unit -> 'a action_result)
| Direct of rule_id option * (builder -> 'a action_result)
(** Remark: while the abstract interface only requests (builder -> 'a) for
    direct rules, (build -> 'a action_result) allows to regain some explicit
    rule-structure after executing a fragment of direct rule. It is
    useful for composability and performances; in particular,
    defining (bind) for the (builder -> 'a) version requires to call
    (run), which is not very nice. *)

let return v = Return v
let direct action = Direct (None, fun build -> Return (action build))
let build_order order =
  let order = List.map (fun (dep, check) -> (None, dep, check)) order in
  Order (order, fun () -> Return ())

let rec map_action_result f = function
  | Return result -> Return (f result)
  | Direct (id, action) -> Direct (id, fun builder ->
                                         map_action_result f (action builder))
  | Order (order, next) ->
    Order (order, (fun () -> map_action_result f (next ())))

let rec bind action rest = match action with
  | Return x -> rest x
  | Direct (id, f) -> Direct (id, fun build -> bind (f build) rest)
  | Order (deps, next) -> Order (deps, fun () -> bind (next ()) rest)

let update_id oldid id = match oldid with
  | Some _ -> oldid
  | None -> Some id

let rec annot id = function
  | Return _ as action -> action
  | Direct (oldid, f) ->
    Direct (update_id oldid id,
            fun build -> annot id (f build))
  | Order (deps, next) ->
    let update (oldid, dep, check) = (update_id oldid id, dep, check) in
    Order (List.map update deps, fun () -> annot id (next ()))

let maybe_annot maybe_id action =
  match maybe_id with
    | None -> action
    | Some id -> annot id action

let add_dep {id_name = name; id_prods = prods} = function
  | Bad _ -> ()
  | Good result ->
    dprintf 10 "new dyndep for %S(%a): %S"
      name (List.print Resource.print) prods result;
    (* dyndeps := Resources.add res' !dyndeps; *)
    List.iter (fun prod -> Resource.Cache.add_dependency prod result) prods;
    ()

let maybe_add_dep maybe_id result =
  match maybe_id with
    | None -> ()
    | Some id -> add_dep id result

let wrap_builder maybe_id builder rs =
  let results = builder rs in
  List.iter (maybe_add_dep maybe_id) results;
  results

let rec run_action_result builder = function
  | Return result -> result
  | Direct (id, action) ->
    run_action_result builder (action (wrap_builder id builder))
  | Order (order, next) ->
    let ids, deps, checks = List.split3 order in
    Printf.eprintf "static dep: %s\n%!"
      (String.concat " & " (List.map (String.concat "|") deps));
    let results = builder deps in
    let check_result id check result =
      maybe_add_dep id result;
      check result; in
    List.iter3 check_result ids checks results;
    run_action_result builder (next ())

let merge action_results =
  let rec merge already_returned = function
    | [] -> return already_returned
    | actions ->
      let (returns, directs, orders) =
        let rec add (returns, directs, orders) = function
          | Return v -> (v::returns, directs, orders)
          | Direct (id,act) -> (returns, (id,act)::directs, orders)
          | Order (order, next) -> (returns, directs, (order,next)::orders) in
        List.fold_left add ([], [], []) actions in
      let orders_action cont =
        if orders = [] then cont []
        else begin
          let deps, nexts = List.split orders in
          Order (List.flatten deps, fun () ->
            cont (List.map (fun next -> next ()) nexts))
        end in
      let directs_action cont  =
        (** the Direct parts of the rule description are still executed
            sequentially; trying to merge them would blur the rule
            identity information, and wouldn't improve parallelism
            anyway as their time is spend executing the (action build)
            part.
        *)
        let add_direct cont (id, action) = fun reslist ->
          Direct(id, fun build -> cont (action build :: reslist)) in
        List.fold_left add_direct cont directs [] in
      orders_action & fun after_orders ->
      directs_action & fun after_directs ->
      merge (returns @ already_returned) (after_orders @ after_directs)
  in
  merge [] action_results    

type indirect_builder = Pathname.t list -> build_result action_result

let rec unroll_result indirect_builder = function
  | Return x -> Return x
  | Direct (id, f) ->
    Direct (id, fun build -> unroll_result indirect_builder (f build))
  | Order (deps, next) ->
    unroll_result indirect_builder &
    let action (id, dep, check) =
      dprintf 10 "unrolling %s for %s"
        (String.concat "|" dep)
        (match id with None -> "unknown rule"
          | Some {id_name; id_prods} ->
            Printf.sprintf "%S->%s" id_name (String.concat "&" id_prods));
      bind (maybe_annot id (indirect_builder dep)) & fun result ->
      return (check result) in
    bind (merge (List.map action deps)) & fun units ->
      List.iter (fun () -> ()) units;
      next ()

type action = env -> builder -> Command.t
type indirect_action = Command.t gen_action

type digest_command = { digest : string; command : Command.t }

type 'a gen_rule =
  { name  : string;
    deps  : Pathname.t list; (* These pathnames must be normalized *)
    prods : 'a list; (* Note that prods also contains stamp *)
    stamp : 'a option;
    code  : digest_command gen_action }

type rule = Pathname.t gen_rule
type rule_scheme = Resource.resource_pattern gen_rule

let name_of_rule r = r.name
let deps_of_rule r = r.deps
let prods_of_rule r = r.prods
let stamp_of_rule r = r.stamp

let id_of_rule {name; prods; _} = {
  id_name = name;
  id_prods = prods;
}

type 'a rule_printer = (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a gen_rule -> unit

let compare _ _ = assert false

let print_rule_name f r = pp_print_string f r.name

let print_resource_list = List.print Resource.print

let print_rule_contents ppelt f r =
  fprintf f "@[<v2>{@ @[<2>name  =@ %S@];@ @[<2>deps  =@ %a@];@ @[<2>prods = %a@];@ @[<2>code  = <fun>@]@]@ }"
    r.name print_resource_list r.deps (List.print ppelt) r.prods

let pretty_print ppelt f r =
  fprintf f "@[<hv2>rule@ %S@ ~deps:%a@ ~prods:%a@ <fun>@]"
    r.name print_resource_list r.deps (List.print ppelt) r.prods

let print = print_rule_name

let subst env rule =
  let subst_resources = List.map (Resource.subst env) in
  let subst_resource_patterns = List.map (Resource.subst_pattern env) in
  let finder next_finder p = next_finder (Resource.subst_any env p) in
  let stamp = match rule.stamp with None -> None | Some x -> Some (Resource.subst_pattern env x) in
  let prods = subst_resource_patterns rule.prods in
  { name = sbprintf "%s (%a)" rule.name Resource.print_env env;
    prods = prods;
    deps =
      (* The substition should preserve normalization of pathnames *)
      subst_resources rule.deps; 
    stamp = stamp;
    code = (fun env -> rule.code (finder env)) }

exception Can_produce of rule

let can_produce target rule =
  try
    List.iter begin fun resource ->
      match Resource.matchit resource target with
      | Some env -> raise (Can_produce (subst env rule))
      | None -> ()
    end rule.prods; None
  with Can_produce r -> Some r

let digest_prods r =
  List.fold_right begin fun p acc ->
    let f = Pathname.to_string (Resource.in_build_dir p) in
    if sys_file_exists f then (f, Digest.file f) :: acc else acc
  end r.prods []

let digest_deps r dyndeps =
  let buf = Buffer.create 1024 in
  let add_resource r = Buffer.add_string buf (Digest.to_hex (Resource.digest r)) in
  Buffer.add_string buf "deps:";
  List.iter add_resource r.deps;
  Buffer.add_string buf "dyndeps:";
  Resources.iter add_resource dyndeps;
  Digest.to_hex (Digest.string (Buffer.contents buf))

let digest_rule r dyndeps action =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf action.digest;
  let add_resource r = Buffer.add_string buf (Resource.digest r) in
  Buffer.add_string buf "prods:";
  List.iter add_resource r.prods;
  Buffer.add_string buf "deps:";
  List.iter add_resource r.deps;
  Buffer.add_string buf "dyndeps:";
  Resources.iter add_resource dyndeps;
  Digest.string (Buffer.contents buf)

let cached_digest r =
  try Some (Digest_cache.get ("Rule: " ^ r.name))
  with Not_found -> None

let store_digest r digest = Digest_cache.put ("Rule: " ^ r.name) digest

let print_digest f x = pp_print_string f (Digest.to_hex x)

let exists2 find p rs =
  try Some (find p rs) with Not_found -> None

let build_deps_of_tags builder tags =
  match Command.deps_of_tags tags with
  | [] -> []
  | deps -> List.map Outcome.good (builder (List.map (fun x -> [x]) deps))

let build_deps_of_tags_on_cmd command =
  let add_deps tags action =
    let deps = Command.deps_of_tags tags in
    let order = List.map (fun x -> ([x], ignore_good)) deps in
    bind (build_order order) (fun () -> action) in
  Command.fold_tags add_deps command (Return ())

let indirect_call r =
  annot { id_name = r.name; id_prods = r.prods } &
  (* note that we marked the whole action with the rule identity *)
  let () = dprintf 5 "start rule %a" print r in
  bind (r.code (fun x -> x)) & fun action ->
  let dyndeps = Resource.Cache.dependencies (List.hd r.prods) in
  bind (build_deps_of_tags_on_cmd action.command) & fun () ->
  let () = dprintf 10 "dyndeps: %a" Resources.print dyndeps in
  let (reason, cached) =
    match exists2 List.find (fun r -> not (Resource.exists_in_build_dir r)) r.prods with
    | Some r -> (`cache_miss_missing_prod r, false)
    | _ ->
      begin match exists2 List.find Resource.Cache.resource_has_changed r.deps with
      | Some r -> (`cache_miss_changed_dep r, false)
      | _ ->
        begin match exists2 Resources.find_elt Resource.Cache.resource_has_changed dyndeps with
        | Some r -> (`cache_miss_changed_dyn_dep r, false)
        | _ ->
            begin match cached_digest r with
            | None -> (`cache_miss_no_digest, false)
            | Some d ->
                let rule_digest = digest_rule r dyndeps action in
                if d = rule_digest then (`cache_hit, true)
                else (`cache_miss_digest_changed(d, rule_digest), false)
            end
        end
      end
  in
  let explain_reason l =
    raw_dprintf (l+1) "mid rule %a: " print r;
    match reason with
    | `cache_miss_missing_prod r ->
          dprintf l "cache miss: a product is not in build dir (%a)" Resource.print r
    | `cache_miss_changed_dep r ->
          dprintf l "cache miss: a dependency has changed (%a)" Resource.print r
    | `cache_miss_changed_dyn_dep r ->
          dprintf l "cache miss: a dynamic dependency has changed (%a)" Resource.print r
    | `cache_miss_no_digest ->
          dprintf l "cache miss: no digest found for %S (the command, a dependency, or a product)"
            r.name
    | `cache_hit -> dprintf (l+1) "cache hit"
    | `cache_miss_digest_changed(old_d, new_d) ->
          dprintf l "cache miss: the digest has changed for %S (the command, a dependency, or a product: %a <> %a)"
            r.name print_digest old_d print_digest new_d
  in
  let prod_digests = digest_prods r in
  (if not cached then List.iter Resource.clean r.prods);
  (if !Options.nothing_should_be_rebuilt && not cached then
    (explain_reason (-1);
     let msg = sbprintf "Need to rebuild %a through the rule `%a'" print_resource_list r.prods print r in
     raise (Exit_rule_error msg)));
  explain_reason 3;
  let thunk () =
    try
      if cached then Command.execute ~pretend:true action.command
      else
        begin match r.stamp with
        | Some stamp ->
            reset_filesys_cache ();
            let digest_deps = digest_deps r dyndeps in
            with_output_file stamp (fun oc -> output_string oc digest_deps)
        | None -> ()
        end;
      List.iter (fun r -> Resource.Cache.resource_built r) r.prods;
      (if not cached then
        let new_rule_digest = digest_rule r dyndeps action in
        let new_prod_digests = digest_prods r in
        let () = store_digest r new_rule_digest in
        List.iter begin fun p ->
          let f = Pathname.to_string (Resource.in_build_dir p) in
          (try let digest = List.assoc f prod_digests in
               let new_digest = List.assoc f new_prod_digests in
               if digest <> new_digest then raise Not_found
          with Not_found -> Resource.Cache.resource_changed p)
        end r.prods);
      dprintf 5 "end rule %a" print r
    with exn -> (List.iter Resource.clean r.prods; raise exn)
  in
  begin
    if cached
    then thunk ()
    else List.iter (fun x -> Resource.Cache.suspend_resource x action.command thunk r.prods) r.prods
  end;
  Return ()

let call builder r =
  let dyndeps = ref Resources.empty in
  let builder rs =
    let results = builder rs in
    List.map begin fun res ->
      match res with
      | Good res' ->
          let () = dprintf 10 "new dyndep for %S(%a): %S" r.name print_resource_list r.prods res' in
          dyndeps := Resources.add res' !dyndeps;
          List.iter (fun x -> Resource.Cache.add_dependency x res') r.prods;
          res
      | Bad _ -> res
    end results in
  let () = dprintf 5 "start rule %a" print r in
  let action = run_action_result builder (r.code (fun x -> x)) in
  run_action_result builder (build_deps_of_tags_on_cmd action.command);
  let dyndeps = !dyndeps in
  let () = dprintf 10 "dyndeps: %a" Resources.print dyndeps in
  let (reason, cached) =
    match exists2 List.find (fun r -> not (Resource.exists_in_build_dir r)) r.prods with
    | Some r -> (`cache_miss_missing_prod r, false)
    | _ ->
      begin match exists2 List.find Resource.Cache.resource_has_changed r.deps with
      | Some r -> (`cache_miss_changed_dep r, false)
      | _ ->
        begin match exists2 Resources.find_elt Resource.Cache.resource_has_changed dyndeps with
        | Some r -> (`cache_miss_changed_dyn_dep r, false)
        | _ ->
            begin match cached_digest r with
            | None -> (`cache_miss_no_digest, false)
            | Some d ->
                let rule_digest = digest_rule r dyndeps action in
                if d = rule_digest then (`cache_hit, true)
                else (`cache_miss_digest_changed(d, rule_digest), false)
            end
        end
      end
  in
  let explain_reason l =
    raw_dprintf (l+1) "mid rule %a: " print r;
    match reason with
    | `cache_miss_missing_prod r ->
          dprintf l "cache miss: a product is not in build dir (%a)" Resource.print r
    | `cache_miss_changed_dep r ->
          dprintf l "cache miss: a dependency has changed (%a)" Resource.print r
    | `cache_miss_changed_dyn_dep r ->
          dprintf l "cache miss: a dynamic dependency has changed (%a)" Resource.print r
    | `cache_miss_no_digest ->
          dprintf l "cache miss: no digest found for %S (the command, a dependency, or a product)"
            r.name
    | `cache_hit -> dprintf (l+1) "cache hit"
    | `cache_miss_digest_changed(old_d, new_d) ->
          dprintf l "cache miss: the digest has changed for %S (the command, a dependency, or a product: %a <> %a)"
            r.name print_digest old_d print_digest new_d
  in
  let prod_digests = digest_prods r in
  (if not cached then List.iter Resource.clean r.prods);
  (if !Options.nothing_should_be_rebuilt && not cached then
    (explain_reason (-1);
     let msg = sbprintf "Need to rebuild %a through the rule `%a'" print_resource_list r.prods print r in
     raise (Exit_rule_error msg)));
  explain_reason 3;
  let thunk () =
    try
      if cached then Command.execute ~pretend:true action.command
      else
        begin match r.stamp with
        | Some stamp ->
            reset_filesys_cache ();
            let digest_deps = digest_deps r dyndeps in
            with_output_file stamp (fun oc -> output_string oc digest_deps)
        | None -> ()
        end;
      List.iter (fun r -> Resource.Cache.resource_built r) r.prods;
      (if not cached then
        let new_rule_digest = digest_rule r dyndeps action in
        let new_prod_digests = digest_prods r in
        let () = store_digest r new_rule_digest in
        List.iter begin fun p ->
          let f = Pathname.to_string (Resource.in_build_dir p) in
          (try let digest = List.assoc f prod_digests in
               let new_digest = List.assoc f new_prod_digests in
               if digest <> new_digest then raise Not_found
          with Not_found -> Resource.Cache.resource_changed p)
        end r.prods);
      dprintf 5 "end rule %a" print r
    with exn -> (List.iter Resource.clean r.prods; raise exn)
  in
  if cached
  then thunk ()
  else List.iter (fun x -> Resource.Cache.suspend_resource x action.command thunk r.prods) r.prods

let (get_rules, add_rule, clear_rules) =
  let rules = ref [] in
  (fun () -> !rules),
  begin fun pos r ->
    try
      let _ = List.find (fun x -> x.name = r.name) !rules in
      raise (Exit_rule_error (sbprintf "Rule.add_rule: already exists: (%a)" print r))
    with Not_found ->
      match pos with
      | `bottom -> rules := !rules @ [r]
      | `top -> rules := r :: !rules
      | `after s ->
          rules :=
            List.fold_right begin fun x acc ->
              if x.name = s then x :: r :: acc else x :: acc
            end !rules []
      | `before s ->
          rules :=
            List.fold_right begin fun x acc ->
              if x.name = s then r :: x :: acc else x :: acc
            end !rules []
  end,
  (fun () -> rules := [])

let indirect_rule name
    ?tags ?(prods=[]) ?(deps=[]) ?prod ?dep ?stamp ?(insert = `bottom) code =
  let () =
    match tags with
      | None -> ()
      | Some _ ->
        Log.eprintf "Warning: your ocamlbuild rule %S uses the ~tags parameter,
                     which is deprecated and ignored."
          name
  in
  let res_add import xs xopt =
    let init =
      match xopt with
      | None -> []
      | Some r -> [import r]
    in
    List.fold_right begin fun x acc ->
      let r = import x in
      if List.mem r acc then
        failwith (sprintf "in rule %s, multiple occurrences of the resource %s" name x)
      else r :: acc
    end xs init
  in
  if prods = [] && prod = None && stamp = None then raise (Exit_rule_error "Can't make a rule that produces nothing");
  let stamp, prods =
    match stamp with
    | None -> None, prods
    | Some stamp ->
        Some (Resource.import_pattern stamp), stamp :: prods
  in
  let prods = res_add Resource.import_pattern prods prod in
  let code env =
    map_action_result (fun cmd -> { 
      digest = Command.digest cmd;
      command = cmd;
    }) (code env)
  in
  add_rule insert
  { name  = name;
    deps  = res_add Resource.import (* should normalize *) deps dep;
    stamp = stamp;
    prods = prods;
    code  = code }

let rule name ?tags ?prods ?deps ?prod ?dep ?stamp ?insert code =
  indirect_rule name ?tags ?prods ?deps ?prod ?dep ?stamp ?insert
    (fun env -> direct (fun build -> code env build))

module Common_commands = struct
  open Command
  let mv src dest = Cmd (S [A"mv"; P src; Px dest])
  let cp src dest = Cmd (S [A"cp"; P src; Px dest])
  let cp_p src dest = Cmd (S [A"cp"; A"-p"; P src; Px dest])
  let ln_f pointed pointer = Cmd (S [A"ln"; A"-f"; P pointed; Px pointer])
  let ln_s pointed pointer = Cmd (S[A"ln"; A"-s"; P pointed; Px pointer])
  let rm_f x = Cmd (S [A"rm"; A"-f"; Px x])
  let chmod opts file = Cmd (S[A"chmod"; opts; Px file])
  let cmp a b = Cmd (S[A"cmp"; P a; Px b])
end
open Common_commands

let copy_rule name ?insert src dest =
  rule name ?insert ~prod:dest ~dep:src
    begin fun env _ ->
      let src = env src and dest = env dest in
      Shell.mkdir_p (Pathname.dirname dest);
      cp_p src dest
    end
