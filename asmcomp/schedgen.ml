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

(* Instruction scheduling *)

ouvre Reg
ouvre Mach
ouvre Linearize

(* Representation of the code DAG. *)

type code_dag_node =
  { instr: instruction;                 (* The instruction *)
    delay: int;           (* How many cycles before result is available *)
    modifiable sons: (code_dag_node * int) list;
                                        (* Instructions that depend on it *)
    modifiable date: int;                  (* Start date *)
    modifiable length: int;                (* Length of longest path to result *)
    modifiable ancestors: int;             (* Number of ancestors *)
    modifiable emitted_ancestors: int }    (* Number of emitted ancestors *)

soit dummy_node =
  { instr = end_instr; delay = 0; sons = []; date = 0;
    length = -1; ancestors = 0; emitted_ancestors = 0 }

(* The code dag itself is represented by two tables from registers to nodes:
   - "results" maps registers to the instructions that produced them;
   - "uses" maps registers to the instructions that use them.
   In addition:
   - code_stores contains the latest store nodes emitted so far
   - code_loads contains all load nodes emitted since the last store
   - code_checkbounds contains the latest checkbound node not matched
     by a subsequent load or store. *)

soit code_results = (Hashtbl.create 31 : (location, code_dag_node) Hashtbl.t)
soit code_uses = (Hashtbl.create 31 : (location, code_dag_node) Hashtbl.t)
soit code_stores = ref ([] : code_dag_node list)
soit code_loads = ref ([] : code_dag_node list)
soit code_checkbounds = ref ([] : code_dag_node list)

soit clear_code_dag () =
  Hashtbl.clear code_results;
  Hashtbl.clear code_uses;
  code_stores := [];
  code_loads := [];
  code_checkbounds := []

(* Add an edge to the code DAG *)

soit add_edge ancestor son delay =
  ancestor.sons <- (son, delay) :: ancestor.sons;
  son.ancestors <- son.ancestors + 1

soit add_edge_after son ancestor = add_edge ancestor son 0

(* Add edges from all instructions that define a pseudoregister [arg] being used
   as argument to node [node] (RAW dependencies *)

soit add_RAW_dependencies node arg =
  essaie
    soit ancestor = Hashtbl.find code_results arg.loc dans
    add_edge ancestor node ancestor.delay
  avec Not_found ->
    ()

(* Add edges from all instructions that use a pseudoregister [res] that is
   defined by node [node] (WAR dependencies). *)

soit add_WAR_dependencies node res =
  soit ancestors = Hashtbl.find_all code_uses res.loc dans
  List.iter (add_edge_after node) ancestors

(* Add edges from all instructions that have already defined a pseudoregister
   [res] that is defined by node [node] (WAW dependencies). *)

soit add_WAW_dependencies node res =
  essaie
    soit ancestor = Hashtbl.find code_results res.loc dans
    add_edge ancestor node 0
  avec Not_found ->
    ()

(* Compute length of longest path to a result.
   For leafs of the DAG, see whether their result is used in the instruction
   immediately following the basic block (a "critical" output). *)

soit is_critical critical_outputs results =
  essaie
    pour i = 0 à Array.length results - 1 faire
      soit r = results.(i).loc dans
      pour j = 0 à Array.length critical_outputs - 1 faire
        si critical_outputs.(j).loc = r alors raise Exit
      fait
    fait;
    faux
  avec Exit ->
    vrai

soit rec longest_path critical_outputs node =
  si node.length < 0 alors début
    filtre node.sons avec
      [] ->
        node.length <-
          si is_critical critical_outputs node.instr.res
          || node.instr.desc = Lreloadretaddr (* alway critical *)
          alors node.delay
          sinon 0
    | sons ->
        node.length <-
          List.fold_left
            (fonc len (son, delay) ->
              max len (longest_path critical_outputs son + delay))
            0 sons
  fin;
  node.length

(* Remove an instruction from the ready queue *)

soit rec remove_instr node = fonction
    [] -> []
  | instr :: rem ->
      si instr == node alors rem sinon instr :: remove_instr node rem

(* We treat Lreloadretaddr as a word-sized load *)

soit some_load = (Iload(Cmm.Word, Arch.identity_addressing))

(* The generic scheduler *)

classe virtuelle scheduler_generic = objet (self)

(* Determine whether an operation ends a basic block or not.
   Can be overridden for some processors to signal specific instructions
   that terminate a basic block. *)

méthode oper_in_basic_block = fonction
    Icall_ind -> faux
  | Icall_imm _ -> faux
  | Itailcall_ind -> faux
  | Itailcall_imm _ -> faux
  | Iextcall _ -> faux
  | Istackoffset _ -> faux
  | Ialloc _ -> faux
  | _ -> vrai

(* Determine whether an instruction ends a basic block or not *)

méthode privée instr_in_basic_block instr =
  filtre instr.desc avec
    Lop op -> self#oper_in_basic_block op
  | Lreloadretaddr -> vrai
  | _ -> faux

(* Determine whether an operation is a memory store or a memory load.
   Can be overridden for some processors to signal specific
   load or store instructions (e.g. on the I386). *)

méthode is_store = fonction
    Istore(_, _) -> vrai
  | _ -> faux

méthode is_load = fonction
    Iload(_, _) -> vrai
  | _ -> faux

méthode is_checkbound = fonction
    Iintop Icheckbound -> vrai
  | Iintop_imm(Icheckbound, _) -> vrai
  | _ -> faux

méthode privée instr_is_store instr =
  filtre instr.desc avec
    Lop op -> self#is_store op
  | _ -> faux

méthode privée instr_is_load instr =
  filtre instr.desc avec
    Lop op -> self#is_load op
  | _ -> faux

méthode privée instr_is_checkbound instr =
  filtre instr.desc avec
    Lop op -> self#is_checkbound op
  | _ -> faux

(* Estimate the latency of an operation. *)

méthode virtuelle oper_latency : Mach.operation -> int

(* Estimate the latency of a Lreloadretaddr operation. *)

méthode reload_retaddr_latency = self#oper_latency some_load

(* Estimate the delay needed to evaluate an instruction *)

méthode privée instr_latency instr =
  filtre instr.desc avec
    Lop op -> self#oper_latency op
  | Lreloadretaddr -> self#reload_retaddr_latency
  | _ -> affirme faux

(* Estimate the number of cycles consumed by emitting an operation. *)

méthode virtuelle oper_issue_cycles : Mach.operation -> int

(* Estimate the number of cycles consumed by emitting a Lreloadretaddr. *)

méthode reload_retaddr_issue_cycles = self#oper_issue_cycles some_load

(* Estimate the number of cycles consumed by emitting an instruction. *)

méthode privée instr_issue_cycles instr =
  filtre instr.desc avec
    Lop op -> self#oper_issue_cycles op
  | Lreloadretaddr -> self#reload_retaddr_issue_cycles
  | _ -> affirme faux

(* Pseudoregisters destroyed by an instruction *)

méthode privée destroyed_by_instr instr =
  filtre instr.desc avec
  | Lop op -> Proc.destroyed_at_oper (Iop op)
  | Lreloadretaddr -> [||]
  | _ -> affirme faux

(* Add an instruction to the code dag *)

méthode privée add_instruction ready_queue instr =
  soit delay = self#instr_latency instr dans
  soit destroyed = self#destroyed_by_instr instr dans
  soit node =
    { instr = instr;
      delay = delay;
      sons = [];
      date = 0;
      length = -1;
      ancestors = 0;
      emitted_ancestors = 0 } dans
  (* Add edges from all instructions that define one of the registers used
     (RAW dependencies) *)
  Array.iter (add_RAW_dependencies node) instr.arg;
  (* Also add edges from all instructions that use one of the result regs
     of this instruction, or a reg destroyed by this instruction
     (WAR dependencies). *)
  Array.iter (add_WAR_dependencies node) instr.res;
  Array.iter (add_WAR_dependencies node) destroyed;   (* PR#5731 *)
  (* Also add edges from all instructions that have already defined one
     of the results of this instruction, or a reg destroyed by
     this instruction (WAW dependencies). *)
  Array.iter (add_WAW_dependencies node) instr.res;
  Array.iter (add_WAW_dependencies node) destroyed;   (* PR#5731 *)
  (* If this is a load, add edges from the most recent store viewed so
     far (if any) and remember the load.  Also add edges from the most
     recent checkbound and forget that checkbound. *)
  si self#instr_is_load instr alors début
    List.iter (add_edge_after node) !code_stores;
    code_loads := node :: !code_loads;
    List.iter (add_edge_after node) !code_checkbounds;
    code_checkbounds := []
  fin
  (* If this is a store, add edges from the most recent store,
     as well as all loads viewed since then, and also the most recent
     checkbound. Remember the store,
     discarding the previous stores, loads and checkbounds. *)
  sinon si self#instr_is_store instr alors début
    List.iter (add_edge_after node) !code_stores;
    List.iter (add_edge_after node) !code_loads;
    List.iter (add_edge_after node) !code_checkbounds;
    code_stores := [node];
    code_loads := [];
    code_checkbounds := []
  fin
  sinon si self#instr_is_checkbound instr alors début
    code_checkbounds := [node]
  fin;
  (* Remember the registers used and produced by this instruction *)
  pour i = 0 à Array.length instr.res - 1 faire
    Hashtbl.add code_results instr.res.(i).loc node
  fait;
  pour i = 0 à Array.length destroyed - 1 faire
    Hashtbl.add code_results destroyed.(i).loc node  (* PR#5731 *)
  fait;
  pour i = 0 à Array.length instr.arg - 1 faire
    Hashtbl.add code_uses instr.arg.(i).loc node
  fait;
  (* If this is a root instruction (all arguments already computed),
     add it to the ready queue *)
  si node.ancestors = 0 alors node :: ready_queue sinon ready_queue

(* Given a list of instructions and a date, choose one or several
   that are ready to be computed (start date <= current date)
   and that we can emit in one cycle.  Favor instructions with
   maximal distance to result.  If we can't find any, return None.
   This does not take multiple issues into account, though. *)

méthode privée ready_instruction date queue =
  soit rec extract best = fonction
    [] ->
      si best == dummy_node alors None sinon Some best
  | instr :: rem ->
      soit new_best =
        si instr.date <= date && instr.length > best.length
        alors instr sinon best dans
      extract new_best rem dans
  extract dummy_node queue

(* Schedule a basic block, adding its instructions in front of the given
   instruction sequence *)

méthode privée reschedule ready_queue date cont =
  si ready_queue = [] alors cont sinon début
    filtre self#ready_instruction date ready_queue avec
      None ->
        self#reschedule ready_queue (date + 1) cont
    | Some node ->
        (* Remove node from queue *)
        soit new_queue = ref (remove_instr node ready_queue) dans
        (* Update the start date and number of ancestors emitted of
           all descendents of this node. Enter those that become ready
           in the queue. *)
        soit issue_cycles = self#instr_issue_cycles node.instr dans
        List.iter
          (fonc (son, delay) ->
            soit completion_date = date + issue_cycles + delay - 1 dans
            si son.date < completion_date alors son.date <- completion_date;
            son.emitted_ancestors <- son.emitted_ancestors + 1;
            si son.emitted_ancestors = son.ancestors alors
              new_queue := son :: !new_queue)
          node.sons;
        { node.instr avec next =
            self#reschedule !new_queue (date + issue_cycles) cont }
  fin

(* Entry point *)
(* Don't bother to schedule for initialization code and the like. *)

méthode schedule_fundecl f =

  soit rec schedule i =
    filtre i.desc avec
      Lend -> i
    | _ ->
        si self#instr_in_basic_block i alors début
          clear_code_dag();
          schedule_block [] i
        fin sinon
          { i avec next = schedule i.next }

  et schedule_block ready_queue i =
    si self#instr_in_basic_block i alors
      schedule_block (self#add_instruction ready_queue i) i.next
    sinon début
      soit critical_outputs =
        filtre i.desc avec
          Lop(Icall_ind | Itailcall_ind) -> [| i.arg.(0) |]
        | Lop(Icall_imm _ | Itailcall_imm _ | Iextcall _) -> [||]
        | Lreturn -> [||]
        | _ -> i.arg dans
      List.iter (fonc x -> ignore (longest_path critical_outputs x)) ready_queue;
      self#reschedule ready_queue 0 (schedule i)
    fin dans

  si f.fun_fast alors début
    soit new_body = schedule f.fun_body dans
    clear_code_dag();
    { fun_name = f.fun_name;
      fun_body = new_body;
      fun_fast = f.fun_fast;
      fun_dbg  = f.fun_dbg }
  fin sinon
    f

fin
