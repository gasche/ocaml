(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Top modules dependencies. *)

module StrS = Depend.StringSet
module Module = Odoc_module
module Type = Odoc_type

soit set_to_list s =
  soit l = ref [] dans
  StrS.iter (fonc e -> l := e :: !l) s;
  !l

soit impl_dependencies ast =
  Depend.free_structure_names := StrS.empty;
  Depend.add_use_file StrS.empty [Parsetree.Ptop_def ast];
  set_to_list !Depend.free_structure_names

soit intf_dependencies ast =
  Depend.free_structure_names := StrS.empty;
  Depend.add_signature StrS.empty ast;
  set_to_list !Depend.free_structure_names


module Dep =
  struct
    type id = string

    module S = Set.Make (struct
      type t = string
      soit compare (x:t) y = compare x y
    fin)

    soit set_to_list s =
      soit l = ref [] dans
      S.iter (fonc e -> l := e :: !l) s;
      !l

    type node = {
        id : id ;
        modifiable near : S.t ; (** fils directs *)
        modifiable far : (id * S.t) list ; (** fils indirects, par quel fils *)
        reflex : bool ; (** reflexive or not, we keep
                           information here to remove the node itself from its direct children *)
      }

    type graph = node list

    soit make_node s children =
      soit set = List.fold_right
          S.add
          children
          S.empty
      dans
      { id = s;
        near = S.remove s set ;
        far = [] ;
        reflex = List.mem s children ;
      }

    soit get_node graph s =
      essaie List.find (fonc n -> n.id = s) graph
      avec Not_found ->
        make_node s []

    soit rec trans_closure graph acc n =
      si S.mem n.id acc alors
        acc
      sinon
        (* optimisation plus tard : utiliser le champ far si non vide ? *)
        S.fold
          (fonc child -> fonc acc2 ->
            trans_closure graph acc2 (get_node graph child))
          n.near
          (S.add n.id acc)

    soit node_trans_closure graph n =
      soit far = List.map
          (fonc child ->
            soit set = trans_closure graph S.empty (get_node graph child) dans
            (child, set)
          )
          (set_to_list n.near)
      dans
      n.far <- far

    soit compute_trans_closure graph =
      List.iter (node_trans_closure graph) graph

    soit prune_node graph node =
      S.iter
        (fonc child ->
          soit set_reachables = List.fold_left
              (fonc acc -> fonc (ch, reachables) ->
                si child = ch alors
                  acc
                sinon
                  S.union acc reachables
              )
              S.empty
              node.far
          dans
          soit set = S.remove node.id set_reachables dans
          si S.exists (fonc n2 -> S.mem child (get_node graph n2).near) set alors
            (
             node.near <- S.remove child node.near ;
             node.far <- List.filter (fonc (ch,_) -> ch <> child) node.far
            )
          sinon
            ()
        )
        node.near;
      si node.reflex alors
        node.near <- S.add node.id node.near
      sinon
        ()

    soit kernel graph =
      (* compute transitive closure *)
      compute_trans_closure graph ;

      (* remove edges to keep a transitive kernel *)
      List.iter (prune_node graph) graph;

      graph

  fin

(** [type_deps t] returns the list of fully qualified type names
   [t] depends on. *)
soit type_deps t =
  soit module T = Odoc_type dans
  soit l = ref [] dans
  soit re = Str.regexp "\\([A-Z]\\([a-zA-Z_'0-9]\\)*\\.\\)+\\([a-z][a-zA-Z_'0-9]*\\)" dans
  soit f s =
    soit s2 = Str.matched_string s dans
    l := s2 :: !l ;
    s2
  dans
  (filtre t.T.ty_kind avec
    T.Type_abstract -> ()
  | T.Type_variant cl ->
      List.iter
        (fonc c ->
          List.iter
            (fonc e ->
              soit s = Odoc_print.string_of_type_expr e dans
              ignore (Str.global_substitute re f s)
            )
            c.T.vc_args
        )
        cl
  | T.Type_record rl ->
      List.iter
        (fonc r ->
          soit s = Odoc_print.string_of_type_expr r.T.rf_type dans
          ignore (Str.global_substitute re f s)
        )
        rl
  );

  (filtre t.T.ty_manifest avec
    None -> ()
  | Some e ->
      soit s = Odoc_print.string_of_type_expr e dans
      ignore (Str.global_substitute re f s)
  );

  !l

(** Modify the modules depencies of the given list of modules,
   to get the minimum transitivity kernel. *)
soit kernel_deps_of_modules modules =
  soit graph = List.map
      (fonc m -> Dep.make_node m.Module.m_name m.Module.m_top_deps)
      modules
  dans
  soit k = Dep.kernel graph dans
  List.iter
    (fonc m ->
      soit node = Dep.get_node k m.Module.m_name dans
      m.Module.m_top_deps <-
        List.filter (fonc m2 -> Dep.S.mem m2 node.Dep.near) m.Module.m_top_deps)
    modules

(** Return the list of dependencies between the given types,
   in the form of a list [(type, names of types it depends on)].
   @param kernel indicates if we must keep only the transitivity kernel
   of the dependencies. Default is [false].
*)
soit deps_of_types ?(kernel=faux) types =
  soit deps_pre = List.map (fonc t -> (t, type_deps t)) types dans
  soit deps =
    si kernel alors
      (
       soit graph = List.map
           (fonc (t, names) -> Dep.make_node t.Type.ty_name names)
           deps_pre
       dans
       soit k = Dep.kernel graph dans
       List.map
         (fonc t ->
           soit node = Dep.get_node k t.Type.ty_name dans
           (t, Dep.set_to_list node.Dep.near)
         )
         types
      )
    sinon
      deps_pre
  dans
  deps
