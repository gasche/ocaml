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

(* Insert load/stores for pseudoregs that got assigned to stack locations. *)

ouvre Misc
ouvre Reg
ouvre Mach

soit access_stack r =
  essaie
    pour i = 0 à Array.length r - 1 faire
      filtre r.(i).loc avec Stack _ -> raise Exit | _ -> ()
    fait;
    faux
  avec Exit ->
    vrai

soit insert_move src dst next =
  si src.loc = dst.loc
  alors next
  sinon instr_cons (Iop Imove) [|src|] [|dst|] next

soit insert_moves src dst next =
  soit rec insmoves i =
    si i >= Array.length src
    alors next
    sinon insert_move src.(i) dst.(i) (insmoves (i+1))
  dans insmoves 0

classe reload_generic = objet (self)

val modifiable redo_regalloc = faux

méthode makereg r =
  filtre r.loc avec
    Unknown -> fatal_error "Reload.makereg"
  | Reg _ -> r
  | Stack _ ->
      redo_regalloc <- vrai;
      soit newr = Reg.clone r dans
      (* Strongly discourage spilling this register *)
      newr.spill_cost <- 100000;
      newr

méthode privée makeregs rv =
  soit n = Array.length rv dans
  soit newv = Array.create n Reg.dummy dans
  pour i = 0 à n-1 faire newv.(i) <- self#makereg rv.(i) fait;
  newv

méthode privée makereg1 rv =
  soit newv = Array.copy rv dans
  newv.(0) <- self#makereg rv.(0);
  newv

méthode reload_operation op arg res =
  (* By default, assume that arguments and results must reside
     in hardware registers. For moves, allow one arg or one
     res to be stack-allocated, but do something for
     stack-to-stack moves *)
  filtre op avec
    Imove | Ireload | Ispill ->
      début filtre arg.(0), res.(0) avec
        {loc = Stack s1}, {loc = Stack s2} quand s1 <> s2 ->
          ([| self#makereg arg.(0) |], res)
      | _ ->
          (arg, res)
      fin
  | _ ->
      (self#makeregs arg, self#makeregs res)

méthode reload_test tst args =
  self#makeregs args

méthode privée reload i =
  filtre i.desc avec
    (* For function calls, returns, etc: the arguments and results are
       already at the correct position (e.g. on stack for some arguments).
       However, something needs to be done for the function pointer in
       indirect calls. *)
    Iend | Ireturn | Iop(Itailcall_imm _) | Iraise _ -> i
  | Iop(Itailcall_ind) ->
      soit newarg = self#makereg1 i.arg dans
      insert_moves i.arg newarg
        {i avec arg = newarg}
  | Iop(Icall_imm _ | Iextcall _) ->
      {i avec next = self#reload i.next}
  | Iop(Icall_ind) ->
      soit newarg = self#makereg1 i.arg dans
      insert_moves i.arg newarg
        {i avec arg = newarg; next = self#reload i.next}
  | Iop op ->
      soit (newarg, newres) = self#reload_operation op i.arg i.res dans
      insert_moves i.arg newarg
        {i avec arg = newarg; res = newres; next =
          (insert_moves newres i.res
            (self#reload i.next))}
  | Iifthenelse(tst, ifso, ifnot) ->
      soit newarg = self#reload_test tst i.arg dans
      insert_moves i.arg newarg
        (instr_cons
          (Iifthenelse(tst, self#reload ifso, self#reload ifnot)) newarg [||]
          (self#reload i.next))
  | Iswitch(index, cases) ->
      soit newarg = self#makeregs i.arg dans
      insert_moves i.arg newarg
        (instr_cons (Iswitch(index, Array.map (self#reload) cases)) newarg [||]
          (self#reload i.next))
  | Iloop body ->
      instr_cons (Iloop(self#reload body)) [||] [||] (self#reload i.next)
  | Icatch(nfail, body, handler) ->
      instr_cons
        (Icatch(nfail, self#reload body, self#reload handler)) [||] [||]
        (self#reload i.next)
  | Iexit i ->
      instr_cons (Iexit i) [||] [||] dummy_instr
  | Itrywith(body, handler) ->
      instr_cons (Itrywith(self#reload body, self#reload handler)) [||] [||]
        (self#reload i.next)

méthode fundecl f =
  redo_regalloc <- faux;
  soit new_body = self#reload f.fun_body dans
  ({fun_name = f.fun_name; fun_args = f.fun_args;
    fun_body = new_body; fun_fast = f.fun_fast;
    fun_dbg  = f.fun_dbg},
   redo_regalloc)

fin
