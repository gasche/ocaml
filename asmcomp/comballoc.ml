(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Combine heap allocations occurring in the same basic block *)

ouvre Mach

type allocation_state =
    No_alloc                            (* no allocation is pending *)
  | Pending_alloc de Reg.t * int        (* an allocation is pending *)
(* The arguments of Pending_alloc(reg, ofs) are:
     reg  the register holding the result of the last allocation
     ofs  the alloc position in the allocated block *)

soit allocated_size = fonction
    No_alloc -> 0
  | Pending_alloc(reg, ofs) -> ofs

soit rec combine i allocstate =
  filtre i.desc avec
    Iend | Ireturn | Iexit _ | Iraise _ ->
      (i, allocated_size allocstate)
  | Iop(Ialloc sz) ->
      début filtre allocstate avec
        No_alloc ->
          soit (newnext, newsz) =
            combine i.next (Pending_alloc(i.res.(0), sz)) dans
          (instr_cons (Iop(Ialloc newsz)) i.arg i.res newnext, 0)
      | Pending_alloc(reg, ofs) ->
          si ofs + sz < Config.max_young_wosize * Arch.size_addr alors début
            soit (newnext, newsz) =
              combine i.next (Pending_alloc(reg, ofs + sz)) dans
            (instr_cons (Iop(Iintop_imm(Iadd, ofs))) [| reg |] i.res newnext,
             newsz)
          fin sinon début
            soit (newnext, newsz) =
              combine i.next (Pending_alloc(i.res.(0), sz)) dans
            (instr_cons (Iop(Ialloc newsz)) i.arg i.res newnext, ofs)
          fin
      fin
  | Iop(Icall_ind | Icall_imm _ | Iextcall _ |
        Itailcall_ind | Itailcall_imm _) ->
      soit newnext = combine_restart i.next dans
      (instr_cons_debug i.desc i.arg i.res i.dbg newnext,
       allocated_size allocstate)
  | Iop op ->
      soit (newnext, sz) = combine i.next allocstate dans
      (instr_cons_debug i.desc i.arg i.res i.dbg newnext, sz)
  | Iifthenelse(test, ifso, ifnot) ->
      soit newifso = combine_restart ifso dans
      soit newifnot = combine_restart ifnot dans
      soit newnext = combine_restart i.next dans
      (instr_cons (Iifthenelse(test, newifso, newifnot)) i.arg i.res newnext,
       allocated_size allocstate)
  | Iswitch(table, cases) ->
      soit newcases = Array.map combine_restart cases dans
      soit newnext = combine_restart i.next dans
      (instr_cons (Iswitch(table, newcases)) i.arg i.res newnext,
       allocated_size allocstate)
  | Iloop(body) ->
      soit newbody = combine_restart body dans
      (instr_cons (Iloop(newbody)) i.arg i.res i.next,
       allocated_size allocstate)
  | Icatch(io, body, handler) ->
      soit (newbody, sz) = combine body allocstate dans
      soit newhandler = combine_restart handler dans
      soit newnext = combine_restart i.next dans
      (instr_cons (Icatch(io, newbody, newhandler)) i.arg i.res newnext, sz)
  | Itrywith(body, handler) ->
      soit (newbody, sz) = combine body allocstate dans
      soit newhandler = combine_restart handler dans
      soit newnext = combine_restart i.next dans
      (instr_cons (Itrywith(newbody, newhandler)) i.arg i.res newnext, sz)

et combine_restart i =
  soit (newi, _) = combine i No_alloc dans newi

soit fundecl f =
  {f avec fun_body = combine_restart f.fun_body}
