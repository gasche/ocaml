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

(* Register allocation by coloring of the interference graph *)

module OrderedRegSet =
  Set.Make(struct
    type t = Reg.t
    soit compare r1 r2 =
      soit ouvre Reg dans
      soit c1 = r1.spill_cost et d1 = r1.degree dans
      soit c2 = r2.spill_cost et d2 = r2.degree dans
      soit n = c2 * d1 - c1 * d2 dans
      si n <> 0 alors n sinon
        soit n = c2 - c1 dans
        si n <> 0 alors n sinon
          soit n = d1 - d2 dans
          si n <> 0 alors n sinon r1.stamp - r2.stamp
  fin)

ouvre Reg

soit allocate_registers() =

  (* Constrained regs with degree >= number of available registers,
     sorted by spill cost (highest first).
     The spill cost measure is [r.spill_cost / r.degree].
     [r.spill_cost] estimates the number of accesses to [r]. *)
  soit constrained = ref OrderedRegSet.empty dans

  (* Unconstrained regs with degree < number of available registers *)
  soit unconstrained = ref [] dans

  (* Preallocate the spilled registers in the stack.
     Split the remaining registers into constrained and unconstrained. *)
  soit remove_reg reg =
    soit cl = Proc.register_class reg dans
    si reg.spill alors début
      (* Preallocate the registers in the stack *)
      soit nslots = Proc.num_stack_slots.(cl) dans
      soit conflict = Array.create nslots faux dans
      List.iter
        (fonc r ->
          filtre r.loc avec
            Stack(Local n) ->
              si Proc.register_class r = cl alors conflict.(n) <- vrai
          | _ -> ())
        reg.interf;
      soit slot = ref 0 dans
      pendant_que !slot < nslots && conflict.(!slot) faire incr slot fait;
      reg.loc <- Stack(Local !slot);
      si !slot >= nslots alors Proc.num_stack_slots.(cl) <- !slot + 1
    fin sinon si reg.degree < Proc.num_available_registers.(cl) alors
      unconstrained := reg :: !unconstrained
    sinon début
      constrained := OrderedRegSet.add reg !constrained
    fin dans

  (* Iterate over all registers preferred by the given register (transitive) *)
  soit iter_preferred f reg =
    soit rec walk r w =
      si not r.visited alors début
        f r w;
        début filtre r.prefer avec
            [] -> ()
          | p  -> r.visited <- vrai;
                  List.iter (fonc (r1, w1) -> walk r1 (min w w1)) p;
                  r.visited <- faux
        fin
      fin dans
    reg.visited <- vrai;
    List.iter (fonc (r, w) -> walk r w) reg.prefer;
    reg.visited <- faux dans

  (* Where to start the search for a suitable register.
     Used to introduce some "randomness" in the choice between registers
     with equal scores. This offers more opportunities for scheduling. *)
  soit start_register = Array.create Proc.num_register_classes 0 dans

  (* Assign a location to a register, the best we can. *)
  soit assign_location reg =
    soit cl = Proc.register_class reg dans
    soit first_reg = Proc.first_available_register.(cl) dans
    soit num_regs = Proc.num_available_registers.(cl) dans
    soit score = Array.create num_regs 0 dans
    soit best_score = ref (-1000000) et best_reg = ref (-1) dans
    soit start = start_register.(cl) dans
    si num_regs <> 0 alors début
      (* Favor the registers that have been assigned to pseudoregs for which
         we have a preference. If these pseudoregs have not been assigned
         already, avoid the registers with which they conflict. *)
      iter_preferred
        (fonc r w ->
          filtre r.loc avec
            Reg n -> soit n = n - first_reg dans
                     si n < num_regs alors
                       score.(n) <- score.(n) + w
          | Unknown ->
              List.iter
                (fonc neighbour ->
                  filtre neighbour.loc avec
                    Reg n -> soit n = n - first_reg dans
                             si n < num_regs alors
                               score.(n) <- score.(n) - w
                  | _ -> ())
                r.interf
          | _ -> ())
        reg;
      List.iter
        (fonc neighbour ->
          (* Prohibit the registers that have been assigned
             to our neighbours *)
          début filtre neighbour.loc avec
            Reg n -> soit n = n - first_reg dans
                     si n < num_regs alors
                       score.(n) <- (-1000000)
          | _ -> ()
          fin;
          (* Avoid the registers that have been assigned to pseudoregs
             for which our neighbours have a preference *)
          iter_preferred
            (fonc r w ->
              filtre r.loc avec
                Reg n -> soit n = n - first_reg dans
                         si n < num_regs alors
                           score.(n) <- score.(n) - (w-1)
                         (* w-1 to break the symmetry when two conflicting regs
                            have the same preference for a third reg. *)
              | _ -> ())
            neighbour)
        reg.interf;
      (* Pick the register with the best score *)
      pour n = start à num_regs - 1 faire
        si score.(n) > !best_score alors début
          best_score := score.(n);
          best_reg := n
        fin
      fait;
      pour n = 0 à start - 1 faire
        si score.(n) > !best_score alors début
          best_score := score.(n);
          best_reg := n
        fin
      fait
    fin;
    (* Found a register? *)
    si !best_reg >= 0 alors début
      reg.loc <- Reg(first_reg + !best_reg);
      si Proc.rotate_registers alors
        start_register.(cl) <- (soit start = start + 1 dans
                                si start >= num_regs alors 0 sinon start)
    fin sinon début
      (* Sorry, we must put the pseudoreg in a stack location *)
      soit nslots = Proc.num_stack_slots.(cl) dans
      soit score = Array.create nslots 0 dans
      (* Compute the scores as for registers *)
      List.iter
        (fonc (r, w) ->
          filtre r.loc avec
            Stack(Local n) -> score.(n) <- score.(n) + w
          | Unknown ->
              List.iter
                (fonc neighbour ->
                  filtre neighbour.loc avec
                    Stack(Local n) -> score.(n) <- score.(n) - w
                  | _ -> ())
                r.interf
          | _ -> ())
        reg.prefer;
      List.iter
        (fonc neighbour ->
          début filtre neighbour.loc avec
              Stack(Local n) -> score.(n) <- (-1000000)
          | _ -> ()
          fin;
          List.iter
            (fonc (r, w) ->
              filtre r.loc avec
                Stack(Local n) -> score.(n) <- score.(n) - w
              | _ -> ())
            neighbour.prefer)
        reg.interf;
      (* Pick the location with the best score *)
      soit best_score = ref (-1000000) et best_slot = ref (-1) dans
      pour n = 0 à nslots - 1 faire
        si score.(n) > !best_score alors début
          best_score := score.(n);
          best_slot := n
        fin
      fait;
      (* Found one? *)
      si !best_slot >= 0 alors
        reg.loc <- Stack(Local !best_slot)
      sinon début
        (* Allocate a new stack slot *)
        reg.loc <- Stack(Local nslots);
        Proc.num_stack_slots.(cl) <- nslots + 1
      fin
    fin;
    (* Cancel the preferences of this register so that they don't influence
       transitively the allocation of registers that prefer this reg. *)
    reg.prefer <- [] dans

  (* Reset the stack slot counts *)
  pour i = 0 à Proc.num_register_classes - 1 faire
    Proc.num_stack_slots.(i) <- 0;
  fait;

  (* First pass: preallocate spill registers and split remaining regs
     Second pass: assign locations to constrained regs
     Third pass: assign locations to unconstrained regs *)
  List.iter remove_reg (Reg.all_registers());
  OrderedRegSet.iter assign_location !constrained;
  List.iter assign_location !unconstrained
