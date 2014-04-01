(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Construction of the interference graph.
   Annotate pseudoregs with interference lists and preference lists. *)

module IntPairSet =
  Set.Make(struct
    type t = int * int
    soit compare ((a1,b1) : t) (a2,b2) =
      filtre compare a1 a2 avec
        | 0 -> compare b1 b2
        | c -> c
  fin)

ouvre Reg
ouvre Mach

soit build_graph fundecl =

  (* The interference graph is represented in two ways:
     - by adjacency lists for each register
     - by a sparse bit matrix (a set of pairs of register stamps) *)

  soit mat = ref IntPairSet.empty dans

  (* Record an interference between two registers *)
  soit add_interf ri rj =
    si Proc.register_class ri = Proc.register_class rj alors début
      soit i = ri.stamp et j = rj.stamp dans
      si i <> j alors début
        soit p = si i < j alors (i, j) sinon (j, i) dans
        si not(IntPairSet.mem p !mat) alors début
          mat := IntPairSet.add p !mat;
          si ri.loc = Unknown alors début
            ri.interf <- rj :: ri.interf;
            si not rj.spill alors ri.degree <- ri.degree + 1
          fin;
          si rj.loc = Unknown alors début
            rj.interf <- ri :: rj.interf;
            si not ri.spill alors rj.degree <- rj.degree + 1
          fin
        fin
      fin
    fin dans

  (* Record interferences between a register array and a set of registers *)
  soit add_interf_set v s =
    pour i = 0 à Array.length v - 1 faire
      soit r1 = v.(i) dans
      Reg.Set.iter (add_interf r1) s
    fait dans

  (* Record interferences between elements of an array *)
  soit add_interf_self v =
    pour i = 0 à Array.length v - 2 faire
      soit ri = v.(i) dans
      pour j = i+1 à Array.length v - 1 faire
        add_interf ri v.(j)
      fait
    fait dans

  (* Record interferences between the destination of a move and a set
     of live registers. Since the destination is equal to the source,
     do not add an interference between them if the source is still live
     afterwards. *)
  soit add_interf_move src dst s =
    Reg.Set.iter (fonc r -> si r.stamp <> src.stamp alors add_interf dst r) s dans

  (* Compute interferences *)

  soit rec interf i =
    soit destroyed = Proc.destroyed_at_oper i.desc dans
    si Array.length destroyed > 0 alors add_interf_set destroyed i.live;
    filtre i.desc avec
      Iend -> ()
    | Ireturn -> ()
    | Iop(Imove | Ispill | Ireload) ->
        add_interf_move i.arg.(0) i.res.(0) i.live;
        interf i.next
    | Iop(Itailcall_ind) -> ()
    | Iop(Itailcall_imm lbl) -> ()
    | Iop op ->
        add_interf_set i.res i.live;
        add_interf_self i.res;
        interf i.next
    | Iifthenelse(tst, ifso, ifnot) ->
        interf ifso;
        interf ifnot;
        interf i.next
    | Iswitch(index, cases) ->
        pour i = 0 à Array.length cases - 1 faire
          interf cases.(i)
        fait;
        interf i.next
    | Iloop body ->
        interf body; interf i.next
    | Icatch(_, body, handler) ->
        interf body; interf handler; interf i.next
    | Iexit _ ->
        ()
    | Itrywith(body, handler) ->
        add_interf_set Proc.destroyed_at_raise handler.live;
        interf body; interf handler; interf i.next
    | Iraise _ -> () dans

  (* Add a preference from one reg to another.
     Do not add anything if the two registers conflict,
     or if the source register already has a location,
     or if the two registers belong to different classes.
     (The last case can occur e.g. on Sparc when passing
      float arguments in integer registers, PR#6227.) *)

  soit add_pref weight r1 r2 =
    si weight > 0 alors début
      soit i = r1.stamp et j = r2.stamp dans
      si i <> j
      && r1.loc = Unknown
      && Proc.register_class r1 = Proc.register_class r2
      && (soit p = si i < j alors (i, j) sinon (j, i) dans
          not (IntPairSet.mem p !mat))
      alors r1.prefer <- (r2, weight) :: r1.prefer
    fin dans

  (* Add a mutual preference between two regs *)
  soit add_mutual_pref weight r1 r2 =
    add_pref weight r1 r2; add_pref weight r2 r1 dans

  (* Update the spill cost of the registers involved in an operation *)

  soit add_spill_cost cost arg =
    pour i = 0 à Array.length arg - 1 faire
      soit r = arg.(i) dans r.spill_cost <- r.spill_cost + cost
    fait dans

  (* Compute preferences and spill costs *)

  soit rec prefer weight i =
    add_spill_cost weight i.arg;
    add_spill_cost weight i.res;
    filtre i.desc avec
      Iend -> ()
    | Ireturn -> ()
    | Iop(Imove) ->
        add_mutual_pref weight i.arg.(0) i.res.(0);
        prefer weight i.next
    | Iop(Ispill) ->
        add_pref (weight / 4) i.arg.(0) i.res.(0);
        prefer weight i.next
    | Iop(Ireload) ->
        add_pref (weight / 4) i.res.(0) i.arg.(0);
        prefer weight i.next
    | Iop(Itailcall_ind) -> ()
    | Iop(Itailcall_imm lbl) -> ()
    | Iop op ->
        prefer weight i.next
    | Iifthenelse(tst, ifso, ifnot) ->
        prefer (weight / 2) ifso;
        prefer (weight / 2) ifnot;
        prefer weight i.next
    | Iswitch(index, cases) ->
        pour i = 0 à Array.length cases - 1 faire
          prefer (weight / 2) cases.(i)
        fait;
        prefer weight i.next
    | Iloop body ->
        (* Avoid overflow of weight and spill_cost *)
        prefer (si weight < 1000 alors 8 * weight sinon weight) body;
        prefer weight i.next
    | Icatch(_, body, handler) ->
        prefer weight body; prefer weight handler; prefer weight i.next
    | Iexit _ ->
        ()
    | Itrywith(body, handler) ->
        prefer weight body; prefer weight handler; prefer weight i.next
    | Iraise _ -> ()
  dans

  interf fundecl.fun_body; prefer 8 fundecl.fun_body
