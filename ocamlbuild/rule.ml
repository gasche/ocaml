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
ouvre Format
ouvre Log
ouvre Outcome
module Resources = Resource.Resources

exception Exit_rule_error de string
exception Failed

type env = Pathname.t -> Pathname.t
type builder = Pathname.t list list -> (Pathname.t, exn) Outcome.t list
type action = env -> builder -> Command.t

type digest_command = { digest : string; command : Command.t }

type 'a gen_rule =
  { name  : string;
    deps  : Pathname.t list; (* These pathnames must be normalized *)
    prods : 'a list; (* Note that prods also contains stamp *)
    stamp : 'a option;
    doc   : string option;
    code  : env -> builder -> digest_command }

type rule = Pathname.t gen_rule
type rule_scheme = Resource.resource_pattern gen_rule

soit name_of_rule r = r.name
soit deps_of_rule r = r.deps
soit prods_of_rule r = r.prods
soit stamp_of_rule r = r.stamp
soit doc_of_rule r = r.doc

type 'a rule_printer = (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a gen_rule -> unit

soit compare _ _ = affirme faux

soit print_rule_name f r = pp_print_string f r.name

soit print_resource_list = List.print Resource.print

soit print_rule_contents ppelt f r =
  fprintf f "@[<v2>{@ @[<2>name  =@ %S@];@ @[<2>deps  =@ %a@];@ @[<2>prods = %a@];@ @[<2>code  = <fun>@];@ @[<hov 2> doc = %s@]@]@ }"
    r.name print_resource_list r.deps (List.print ppelt)
    r.prods
    (filtre r.doc avec
      | None -> "None"
      | Some doc -> sprintf "Some %S" doc)

soit pretty_print ppelt f r =
  fprintf f "@[<hv2>rule %S@ ~deps:%a@ ~prods:%a@ "
    r.name print_resource_list r.deps (List.print ppelt) r.prods;
  début filtre r.doc avec
    | None -> ()
    | Some doc -> fprintf f "~doc:\"@[<hov>%a@]\"@ " pp_print_text doc
  fin;
  fprintf f "<fun>@]"  

soit print = print_rule_name

soit subst env rule =
  soit subst_resources = List.map (Resource.subst env) dans
  soit subst_resource_patterns = List.map (Resource.subst_pattern env) dans
  soit finder next_finder p = next_finder (Resource.subst_any env p) dans
  soit stamp = filtre rule.stamp avec None -> None | Some x -> Some (Resource.subst_pattern env x) dans
  soit prods = subst_resource_patterns rule.prods dans
  { name = sbprintf "%s (%a)" rule.name Resource.print_env env;
    prods = prods;
    deps =
      (* The substition should preserve normalization of pathnames *)
      subst_resources rule.deps; 
    stamp = stamp;
    doc = rule.doc;
    code = (fonc env -> rule.code (finder env)) }

exception Can_produce de rule

soit can_produce target rule =
  essaie
    List.iter début fonc resource ->
      filtre Resource.matchit resource target avec
      | Some env -> raise (Can_produce (subst env rule))
      | None -> ()
    fin rule.prods; None
  avec Can_produce r -> Some r

soit digest_prods r =
  List.fold_right début fonc p acc ->
    soit f = Pathname.to_string (Resource.in_build_dir p) dans
    si sys_file_exists f alors (f, Digest.file f) :: acc sinon acc
  fin r.prods []

soit digest_deps r dyndeps =
  soit buf = Buffer.create 1024 dans
  soit add_resource r = Buffer.add_string buf (Digest.to_hex (Resource.digest r)) dans
  Buffer.add_string buf "deps:";
  List.iter add_resource r.deps;
  Buffer.add_string buf "dyndeps:";
  Resources.iter add_resource dyndeps;
  Digest.to_hex (Digest.string (Buffer.contents buf))

soit digest_rule r dyndeps action =
  soit buf = Buffer.create 1024 dans
  Buffer.add_string buf action.digest;
  soit add_resource r = Buffer.add_string buf (Resource.digest r) dans
  Buffer.add_string buf "prods:";
  List.iter add_resource r.prods;
  Buffer.add_string buf "deps:";
  List.iter add_resource r.deps;
  Buffer.add_string buf "dyndeps:";
  Resources.iter add_resource dyndeps;
  Digest.string (Buffer.contents buf)

soit cached_digest r =
  essaie Some (Digest_cache.get ("Rule: " ^ r.name))
  avec Not_found -> None

soit store_digest r digest = Digest_cache.put ("Rule: " ^ r.name) digest

soit print_digest f x = pp_print_string f (Digest.to_hex x)

soit exists2 find p rs =
  essaie Some (find p rs) avec Not_found -> None

soit build_deps_of_tags builder tags =
  filtre Command.deps_of_tags tags avec
  | [] -> []
  | deps -> List.map Outcome.good (builder (List.map (fonc x -> [x]) deps))

soit build_deps_of_tags_on_cmd builder =
  Command.iter_tags début fonc tags ->
    filtre Command.deps_of_tags tags avec
    | [] -> ()
    | deps -> List.iter ignore_good (builder (List.map (fonc x -> [x]) deps))
  fin

soit call builder r =
  soit dyndeps = ref Resources.empty dans
  soit builder rs =
    soit results = builder rs dans
    List.map début fonc res ->
      filtre res avec
      | Good res' ->
          soit () = dprintf 10 "new dyndep for %S(%a): %S" r.name print_resource_list r.prods res' dans
          dyndeps := Resources.add res' !dyndeps;
          List.iter (fonc x -> Resource.Cache.add_dependency x res') r.prods;
          res
      | Bad _ -> res
    fin results dans
  soit () = dprintf 5 "start rule %a" print r dans
  soit action = r.code (fonc x -> x) builder dans
  build_deps_of_tags_on_cmd builder action.command;
  soit dyndeps = !dyndeps dans
  soit () = dprintf 10 "dyndeps: %a" Resources.print dyndeps dans
  soit (reason, cached) =
    filtre exists2 List.find (fonc r -> not (Resource.exists_in_build_dir r)) r.prods avec
    | Some r -> (`cache_miss_missing_prod r, faux)
    | _ ->
      début filtre exists2 List.find Resource.Cache.resource_has_changed r.deps avec
      | Some r -> (`cache_miss_changed_dep r, faux)
      | _ ->
        début filtre exists2 Resources.find_elt Resource.Cache.resource_has_changed dyndeps avec
        | Some r -> (`cache_miss_changed_dyn_dep r, faux)
        | _ ->
            début filtre cached_digest r avec
            | None -> (`cache_miss_no_digest, faux)
            | Some d ->
                soit rule_digest = digest_rule r dyndeps action dans
                si d = rule_digest alors (`cache_hit, vrai)
                sinon (`cache_miss_digest_changed(d, rule_digest), faux)
            fin
        fin
      fin
  dans
  soit explain_reason l =
    raw_dprintf (l+1) "mid rule %a: " print r;
    filtre reason avec
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
  dans
  soit prod_digests = digest_prods r dans
  (si not cached alors List.iter Resource.clean r.prods);
  (si !Options.nothing_should_be_rebuilt && not cached alors
    (explain_reason (-1);
     soit msg = sbprintf "Need to rebuild %a through the rule `%a'" print_resource_list r.prods print r dans
     raise (Exit_rule_error msg)));
  explain_reason 3;
  soit thunk () =
    essaie
      si cached alors Command.execute ~pretend:vrai action.command
      sinon
        début filtre r.stamp avec
        | Some stamp ->
            reset_filesys_cache ();
            soit digest_deps = digest_deps r dyndeps dans
            with_output_file stamp (fonc oc -> output_string oc digest_deps)
        | None -> ()
        fin;
      List.iter (fonc r -> Resource.Cache.resource_built r) r.prods;
      (si not cached alors
        soit new_rule_digest = digest_rule r dyndeps action dans
        soit new_prod_digests = digest_prods r dans
        soit () = store_digest r new_rule_digest dans
        List.iter début fonc p ->
          soit f = Pathname.to_string (Resource.in_build_dir p) dans
          (essaie soit digest = List.assoc f prod_digests dans
               soit new_digest = List.assoc f new_prod_digests dans
               si digest <> new_digest alors raise Not_found
          avec Not_found -> Resource.Cache.resource_changed p)
        fin r.prods);
      dprintf 5 "end rule %a" print r
    avec exn -> (List.iter Resource.clean r.prods; raise exn)
  dans
  si cached
  alors thunk ()
  sinon List.iter (fonc x -> Resource.Cache.suspend_resource x action.command thunk r.prods) r.prods

soit (get_rules, add_rule, clear_rules) =
  soit rules = ref [] dans
  (fonc () -> !rules),
  début fonc pos r ->
    essaie
      soit _ = List.find (fonc x -> x.name = r.name) !rules dans
      raise (Exit_rule_error (sbprintf "Rule.add_rule: already exists: (%a)" print r))
    avec Not_found ->
      filtre pos avec
      | `bottom -> rules := !rules @ [r]
      | `top -> rules := r :: !rules
      | `after s ->
          rules :=
            List.fold_right début fonc x acc ->
              si x.name = s alors x :: r :: acc sinon x :: acc
            fin !rules []
      | `before s ->
          rules :=
            List.fold_right début fonc x acc ->
              si x.name = s alors r :: x :: acc sinon x :: acc
            fin !rules []
  fin,
  (fonc () -> rules := [])

soit rule name ?tags ?(prods=[]) ?(deps=[]) ?prod ?dep ?stamp ?(insert = `bottom) ?doc code =
  soit () =
    filtre tags avec
      | None -> ()
      | Some _ ->
        Log.eprintf "Warning: your ocamlbuild rule %S uses the ~tags parameter,
                     which is deprecated and ignored."
          name
  dans
  soit res_add import xs xopt =
    soit init =
      filtre xopt avec
      | None -> []
      | Some r -> [import r]
    dans
    List.fold_right début fonc x acc ->
      soit r = import x dans
      si List.mem r acc alors
        failwith (sprintf "dans la règle %s, plusieurs occurences de la resource %s" name x)
      sinon r :: acc
    fin xs init
  dans
  si prods = [] && prod = None && stamp = None alors raise (Exit_rule_error "Impossible de faire une règle qui ne produit rien");
  soit stamp, prods =
    filtre stamp avec
    | None -> None, prods
    | Some stamp ->
        Some (Resource.import_pattern stamp), stamp :: prods
  dans
  soit prods = res_add Resource.import_pattern prods prod dans
  soit code env build =
    soit cmd = code env build dans
    { digest  = Command.digest cmd
    ; command = cmd }
  dans
  add_rule insert
  { name  = name;
    deps  = res_add Resource.import (* should normalize *) deps dep;
    stamp = stamp;
    doc = doc;
    prods = prods;
    code  = code }

module Common_commands = struct
  ouvre Command
  soit mv src dest = Cmd (S [A"mv"; P src; Px dest])
  soit cp src dest = Cmd (S [A"cp"; P src; Px dest])
  soit cp_p src dest = Cmd (S [A"cp"; A"-p"; P src; Px dest])
  soit ln_f pointed pointer = Cmd (S [A"ln"; A"-f"; P pointed; Px pointer])
  soit ln_s pointed pointer = Cmd (S[A"ln"; A"-s"; P pointed; Px pointer])
  soit rm_f x = Cmd (S [A"rm"; A"-f"; Px x])
  soit chmod opts file = Cmd (S[A"chmod"; opts; Px file])
  soit cmp a b = Cmd (S[A"cmp"; P a; Px b])
fin
ouvre Common_commands

soit copy_rule name ?insert src dest =
  rule name ?insert ~prod:dest ~dep:src
    début fonc env _ ->
      soit src = env src et dest = env dest dans
      Shell.mkdir_p (Pathname.dirname dest);
      cp_p src dest
    fin

soit show_documentation () =
  soit pp fmt = Log.raw_dprintf (-1) fmt dans
  soit rules = get_rules () dans
  List.iter
    (fonc rule -> pp "%a@\n@\n" (pretty_print Resource.print_pattern) rule)
    rules;
  pp "@."
   

