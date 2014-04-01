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

(* Selection of pseudo-instructions, assignment of pseudo-registers,
   sequentialization. *)

ouvre Misc
ouvre Cmm
ouvre Reg
ouvre Mach

type environment = (Ident.t, Reg.t array) Tbl.t

(* Infer the type of the result of an operation *)

soit oper_result_type = fonction
    Capply(ty, _) -> ty
  | Cextcall(s, ty, alloc, _) -> ty
  | Cload c ->
      début filtre c avec
        Word -> typ_addr
      | Single | Double | Double_u -> typ_float
      | _ -> typ_int
      fin
  | Calloc -> typ_addr
  | Cstore c -> typ_void
  | Caddi | Csubi | Cmuli | Cmulhi | Cdivi | Cmodi |
    Cand | Cor | Cxor | Clsl | Clsr | Casr |
    Ccmpi _ | Ccmpa _ | Ccmpf _ -> typ_int
  | Cadda | Csuba -> typ_addr
  | Cnegf | Cabsf | Caddf | Csubf | Cmulf | Cdivf -> typ_float
  | Cfloatofint -> typ_float
  | Cintoffloat -> typ_int
  | Craise _ -> typ_void
  | Ccheckbound _ -> typ_void

(* Infer the size in bytes of the result of a simple expression *)

soit size_expr env exp =
  soit rec size localenv = fonction
      Cconst_int _ | Cconst_natint _ -> Arch.size_int
    | Cconst_symbol _ | Cconst_pointer _ | Cconst_natpointer _ ->
        Arch.size_addr
    | Cconst_float _ -> Arch.size_float
    | Cvar id ->
        début essaie
          Tbl.find id localenv
        avec Not_found ->
        essaie
          soit regs = Tbl.find id env dans
          size_machtype (Array.map (fonc r -> r.typ) regs)
        avec Not_found ->
          fatal_error("Selection.size_expr: variable non liée " ^
                      Ident.unique_name id)
        fin
    | Ctuple el ->
        List.fold_right (fonc e sz -> size localenv e + sz) el 0
    | Cop(op, args) ->
        size_machtype(oper_result_type op)
    | Clet(id, arg, body) ->
        size (Tbl.add id (size localenv arg) localenv) body
    | Csequence(e1, e2) ->
        size localenv e2
    | _ ->
        fatal_error "Selection.size_expr"
  dans size Tbl.empty exp

(* Swap the two arguments of an integer comparison *)

soit swap_intcomp = fonction
    Isigned cmp -> Isigned(swap_comparison cmp)
  | Iunsigned cmp -> Iunsigned(swap_comparison cmp)

(* Naming of registers *)

soit all_regs_anonymous rv =
  essaie
    pour i = 0 à Array.length rv - 1 faire
      si not (Reg.anonymous rv.(i)) alors raise Exit
    fait;
    vrai
  avec Exit ->
    faux

soit name_regs id rv =
  si Array.length rv = 1 alors
    rv.(0).raw_name <- Raw_name.create_from_ident id
  sinon
    pour i = 0 à Array.length rv - 1 faire
      rv.(i).raw_name <- Raw_name.create_from_ident id;
      rv.(i).part <- Some i
    fait

(* "Join" two instruction sequences, making sure they return their results
   in the same registers. *)

soit join opt_r1 seq1 opt_r2 seq2 =
  filtre (opt_r1, opt_r2) avec
    (None, _) -> opt_r2
  | (_, None) -> opt_r1
  | (Some r1, Some r2) ->
      soit l1 = Array.length r1 dans
      affirme (l1 = Array.length r2);
      soit r = Array.create l1 Reg.dummy dans
      pour i = 0 à l1-1 faire
        si Reg.anonymous r1.(i) alors début
          r.(i) <- r1.(i);
          seq2#insert_move r2.(i) r1.(i)
        fin sinon si Reg.anonymous r2.(i) alors début
          r.(i) <- r2.(i);
          seq1#insert_move r1.(i) r2.(i)
        fin sinon début
          r.(i) <- Reg.create r1.(i).typ;
          seq1#insert_move r1.(i) r.(i);
          seq2#insert_move r2.(i) r.(i)
        fin
      fait;
      Some r

(* Same, for N branches *)

soit join_array rs =
  soit some_res = ref None dans
  pour i = 0 à Array.length rs - 1 faire
    soit (r, s) = rs.(i) dans
    si r <> None alors some_res := r
  fait;
  filtre !some_res avec
    None -> None
  | Some template ->
      soit size_res = Array.length template dans
      soit res = Array.create size_res Reg.dummy dans
      pour i = 0 à size_res - 1 faire
        res.(i) <- Reg.create template.(i).typ
      fait;
      pour i = 0 à Array.length rs - 1 faire
        soit (r, s) = rs.(i) dans
        filtre r avec
          None -> ()
        | Some r -> s#insert_moves r res
      fait;
      Some res

(* Extract debug info contained in a C-- operation *)
soit debuginfo_op = fonction
  | Capply(_, dbg) -> dbg
  | Cextcall(_, _, _, dbg) -> dbg
  | Craise (_, dbg) -> dbg
  | Ccheckbound dbg -> dbg
  | _ -> Debuginfo.none

(* Registers for catch constructs *)
soit catch_regs = ref []

(* Name of function being compiled *)
soit current_function_name = ref ""

(* The default instruction selection class *)

classe virtuelle selector_generic = objet (self)

(* Says if an expression is "simple". A "simple" expression has no
   side-effects and its execution can be delayed until its value
   is really needed. In the case of e.g. an [alloc] instruction,
   the non-simple arguments are computed in right-to-left order
   first, then the block is allocated, then the simple arguments are
   evaluated and stored. *)

méthode is_simple_expr = fonction
    Cconst_int _ -> vrai
  | Cconst_natint _ -> vrai
  | Cconst_float _ -> vrai
  | Cconst_symbol _ -> vrai
  | Cconst_pointer _ -> vrai
  | Cconst_natpointer _ -> vrai
  | Cvar _ -> vrai
  | Ctuple el -> List.for_all self#is_simple_expr el
  | Clet(id, arg, body) -> self#is_simple_expr arg && self#is_simple_expr body
  | Csequence(e1, e2) -> self#is_simple_expr e1 && self#is_simple_expr e2
  | Cop(op, args) ->
      début filtre op avec
        (* The following may have side effects *)
      | Capply _ | Cextcall _ | Calloc | Cstore _ | Craise _ -> faux
        (* The remaining operations are simple if their args are *)
      | _ ->
          List.for_all self#is_simple_expr args
      fin
  | _ -> faux

(* Says whether an integer constant is a suitable immediate argument *)

méthode virtuelle is_immediate : int -> bool

(* Selection of addressing modes *)

méthode virtuelle select_addressing :
  Cmm.memory_chunk -> Cmm.expression -> Arch.addressing_mode * Cmm.expression

(* Default instruction selection for stores (of words) *)

méthode select_store addr arg =
  (Istore(Word, addr), arg)

(* Default instruction selection for operators *)

méthode select_operation op args =
  filtre (op, args) avec
    (Capply(ty, dbg), Cconst_symbol s :: rem) -> (Icall_imm s, rem)
  | (Capply(ty, dbg), _) -> (Icall_ind, args)
  | (Cextcall(s, ty, alloc, dbg), _) -> (Iextcall(s, alloc), args)
  | (Cload chunk, [arg]) ->
      soit (addr, eloc) = self#select_addressing chunk arg dans
      (Iload(chunk, addr), [eloc])
  | (Cstore chunk, [arg1; arg2]) ->
      soit (addr, eloc) = self#select_addressing chunk arg1 dans
      si chunk = Word alors début
        soit (op, newarg2) = self#select_store addr arg2 dans
        (op, [newarg2; eloc])
      fin sinon début
        (Istore(chunk, addr), [arg2; eloc])
        (* Inversion addr/datum in Istore *)
      fin
  | (Calloc, _) -> (Ialloc 0, args)
  | (Caddi, _) -> self#select_arith_comm Iadd args
  | (Csubi, _) -> self#select_arith Isub args
  | (Cmuli, _) -> self#select_arith_comm Imul args
  | (Cmulhi, _) -> self#select_arith_comm Imulh args
  | (Cdivi, _) -> (Iintop Idiv, args)
  | (Cmodi, _) -> (Iintop Imod, args)
  | (Cand, _) -> self#select_arith_comm Iand args
  | (Cor, _) -> self#select_arith_comm Ior args
  | (Cxor, _) -> self#select_arith_comm Ixor args
  | (Clsl, _) -> self#select_shift Ilsl args
  | (Clsr, _) -> self#select_shift Ilsr args
  | (Casr, _) -> self#select_shift Iasr args
  | (Ccmpi comp, _) -> self#select_arith_comp (Isigned comp) args
  | (Cadda, _) -> self#select_arith_comm Iadd args
  | (Csuba, _) -> self#select_arith Isub args
  | (Ccmpa comp, _) -> self#select_arith_comp (Iunsigned comp) args
  | (Cnegf, _) -> (Inegf, args)
  | (Cabsf, _) -> (Iabsf, args)
  | (Caddf, _) -> (Iaddf, args)
  | (Csubf, _) -> (Isubf, args)
  | (Cmulf, _) -> (Imulf, args)
  | (Cdivf, _) -> (Idivf, args)
  | (Cfloatofint, _) -> (Ifloatofint, args)
  | (Cintoffloat, _) -> (Iintoffloat, args)
  | (Ccheckbound _, _) -> self#select_arith Icheckbound args
  | _ -> fatal_error "Selection.select_oper"

méthode privée select_arith_comm op = fonction
    [arg; Cconst_int n] quand self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [arg; Cconst_pointer n] quand self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [Cconst_int n; arg] quand self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [Cconst_pointer n; arg] quand self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

méthode privée select_arith op = fonction
    [arg; Cconst_int n] quand self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [arg; Cconst_pointer n] quand self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

méthode privée select_shift op = fonction
    [arg; Cconst_int n] quand n >= 0 && n < Arch.size_int * 8 ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

méthode privée select_arith_comp cmp = fonction
    [arg; Cconst_int n] quand self#is_immediate n ->
      (Iintop_imm(Icomp cmp, n), [arg])
  | [arg; Cconst_pointer n] quand self#is_immediate n ->
      (Iintop_imm(Icomp cmp, n), [arg])
  | [Cconst_int n; arg] quand self#is_immediate n ->
      (Iintop_imm(Icomp(swap_intcomp cmp), n), [arg])
  | [Cconst_pointer n; arg] quand self#is_immediate n ->
      (Iintop_imm(Icomp(swap_intcomp cmp), n), [arg])
  | args ->
      (Iintop(Icomp cmp), args)

(* Instruction selection for conditionals *)

méthode select_condition = fonction
    Cop(Ccmpi cmp, [arg1; Cconst_int n]) quand self#is_immediate n ->
      (Iinttest_imm(Isigned cmp, n), arg1)
  | Cop(Ccmpi cmp, [Cconst_int n; arg2]) quand self#is_immediate n ->
      (Iinttest_imm(Isigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpi cmp, [arg1; Cconst_pointer n]) quand self#is_immediate n ->
      (Iinttest_imm(Isigned cmp, n), arg1)
  | Cop(Ccmpi cmp, [Cconst_pointer n; arg2]) quand self#is_immediate n ->
      (Iinttest_imm(Isigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpi cmp, args) ->
      (Iinttest(Isigned cmp), Ctuple args)
  | Cop(Ccmpa cmp, [arg1; Cconst_pointer n]) quand self#is_immediate n ->
      (Iinttest_imm(Iunsigned cmp, n), arg1)
  | Cop(Ccmpa cmp, [arg1; Cconst_int n]) quand self#is_immediate n ->
      (Iinttest_imm(Iunsigned cmp, n), arg1)
  | Cop(Ccmpa cmp, [Cconst_pointer n; arg2]) quand self#is_immediate n ->
      (Iinttest_imm(Iunsigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpa cmp, [Cconst_int n; arg2]) quand self#is_immediate n ->
      (Iinttest_imm(Iunsigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpa cmp, args) ->
      (Iinttest(Iunsigned cmp), Ctuple args)
  | Cop(Ccmpf cmp, args) ->
      (Ifloattest(cmp, faux), Ctuple args)
  | Cop(Cand, [arg; Cconst_int 1]) ->
      (Ioddtest, arg)
  | arg ->
      (Itruetest, arg)

(* Return an array of fresh registers of the given type.
   Normally implemented as Reg.createv, but some
   ports (e.g. Arm) can override this definition to store float values
   in pairs of integer registers. *)

méthode regs_for tys = Reg.createv tys

(* Buffering of instruction sequences *)

val modifiable instr_seq = dummy_instr

méthode insert_debug desc dbg arg res =
  instr_seq <- instr_cons_debug desc arg res dbg instr_seq

méthode insert desc arg res =
  instr_seq <- instr_cons desc arg res instr_seq

méthode extract =
  soit rec extract res i =
    si i == dummy_instr
    alors res
    sinon extract {i avec next = res} i.next dans
  extract (end_instr()) instr_seq

(* Insert a sequence of moves from one pseudoreg set to another. *)

méthode insert_move src dst =
  si src.stamp <> dst.stamp alors
    self#insert (Iop Imove) [|src|] [|dst|]

méthode insert_moves src dst =
  pour i = 0 à min (Array.length src) (Array.length dst) - 1 faire
    self#insert_move src.(i) dst.(i)
  fait

(* Insert moves and stack offsets for function arguments and results *)

méthode insert_move_args arg loc stacksize =
  si stacksize <> 0 alors self#insert (Iop(Istackoffset stacksize)) [||] [||];
  self#insert_moves arg loc

méthode insert_move_results loc res stacksize =
  si stacksize <> 0 alors self#insert(Iop(Istackoffset(-stacksize))) [||] [||];
  self#insert_moves loc res

(* Add an Iop opcode. Can be overridden by processor description
   to insert moves before and after the operation, i.e. for two-address
   instructions, or instructions using dedicated registers. *)

méthode insert_op_debug op dbg rs rd =
  self#insert_debug (Iop op) dbg rs rd;
  rd

méthode insert_op op rs rd =
  self#insert_op_debug op Debuginfo.none rs rd

(* Add the instructions for the given expression
   at the end of the self sequence *)

méthode emit_expr env exp =
  filtre exp avec
    Cconst_int n ->
      soit r = self#regs_for typ_int dans
      Some(self#insert_op (Iconst_int(Nativeint.of_int n)) [||] r)
  | Cconst_natint n ->
      soit r = self#regs_for typ_int dans
      Some(self#insert_op (Iconst_int n) [||] r)
  | Cconst_blockheader n ->
      soit r = self#regs_for typ_int dans
      Some(self#insert_op (Iconst_blockheader n) [||] r)
  | Cconst_float n ->
      soit r = self#regs_for typ_float dans
      Some(self#insert_op (Iconst_float n) [||] r)
  | Cconst_symbol n ->
      soit r = self#regs_for typ_addr dans
      Some(self#insert_op (Iconst_symbol n) [||] r)
  | Cconst_pointer n ->
      soit r = self#regs_for typ_addr dans
      Some(self#insert_op (Iconst_int(Nativeint.of_int n)) [||] r)
  | Cconst_natpointer n ->
      soit r = self#regs_for typ_addr dans
      Some(self#insert_op (Iconst_int n) [||] r)
  | Cvar v ->
      début essaie
        Some(Tbl.find v env)
      avec Not_found ->
        fatal_error("Selection.emit_expr: variable non liée " ^ Ident.unique_name v)
      fin
  | Clet(v, e1, e2) ->
      début filtre self#emit_expr env e1 avec
        None -> None
      | Some r1 -> self#emit_expr (self#bind_let env v r1) e2
      fin
  | Cassign(v, e1) ->
      soit rv =
        essaie
          Tbl.find v env
        avec Not_found ->
          fatal_error ("Selection.emit_expr: variable non liée " ^ Ident.name v) dans
      début filtre self#emit_expr env e1 avec
        None -> None
      | Some r1 -> self#insert_moves r1 rv; Some [||]
      fin
  | Ctuple [] ->
      Some [||]
  | Ctuple exp_list ->
      début filtre self#emit_parts_list env exp_list avec
        None -> None
      | Some(simple_list, ext_env) ->
          Some(self#emit_tuple ext_env simple_list)
      fin
  | Cop(Craise (k, dbg), [arg]) ->
      si !Clflags.debug && k <> Lambda.Raise_notrace alors
        Proc.contains_calls := vrai;    (* PR#6239 *)
      début filtre self#emit_expr env arg avec
        None -> None
      | Some r1 ->
          soit rd = [|Proc.loc_exn_bucket|] dans
          self#insert (Iop Imove) r1 rd;
          self#insert_debug (Iraise k) dbg rd [||];
          None
      fin
  | Cop(Ccmpf comp, args) ->
      self#emit_expr env (Cifthenelse(exp, Cconst_int 1, Cconst_int 0))
  | Cop(op, args) ->
      début filtre self#emit_parts_list env args avec
        None -> None
      | Some(simple_args, env) ->
          soit ty = oper_result_type op dans
          soit (new_op, new_args) = self#select_operation op simple_args dans
          soit dbg = debuginfo_op op dans
          filtre new_op avec
            Icall_ind ->
              Proc.contains_calls := vrai;
              soit r1 = self#emit_tuple env new_args dans
              soit rarg = Array.sub r1 1 (Array.length r1 - 1) dans
              soit rd = self#regs_for ty dans
              soit (loc_arg, stack_ofs) = Proc.loc_arguments rarg dans
              soit loc_res = Proc.loc_results rd dans
              self#insert_move_args rarg loc_arg stack_ofs;
              self#insert_debug (Iop Icall_ind) dbg
                          (Array.append [|r1.(0)|] loc_arg) loc_res;
              self#insert_move_results loc_res rd stack_ofs;
              Some rd
          | Icall_imm lbl ->
              Proc.contains_calls := vrai;
              soit r1 = self#emit_tuple env new_args dans
              soit rd = self#regs_for ty dans
              soit (loc_arg, stack_ofs) = Proc.loc_arguments r1 dans
              soit loc_res = Proc.loc_results rd dans
              self#insert_move_args r1 loc_arg stack_ofs;
              self#insert_debug (Iop(Icall_imm lbl)) dbg loc_arg loc_res;
              self#insert_move_results loc_res rd stack_ofs;
              Some rd
          | Iextcall(lbl, alloc) ->
              Proc.contains_calls := vrai;
              soit (loc_arg, stack_ofs) =
                self#emit_extcall_args env new_args dans
              soit rd = self#regs_for ty dans
              soit loc_res = self#insert_op_debug (Iextcall(lbl, alloc)) dbg
                                    loc_arg (Proc.loc_external_results rd) dans
              self#insert_move_results loc_res rd stack_ofs;
              Some rd
          | Ialloc _ ->
              Proc.contains_calls := vrai;
              soit rd = self#regs_for typ_addr dans
              soit size = size_expr env (Ctuple new_args) dans
              self#insert (Iop(Ialloc size)) [||] rd;
              self#emit_stores env new_args rd;
              Some rd
          | op ->
              soit r1 = self#emit_tuple env new_args dans
              soit rd = self#regs_for ty dans
              Some (self#insert_op_debug op dbg r1 rd)
      fin
  | Csequence(e1, e2) ->
      début filtre self#emit_expr env e1 avec
        None -> None
      | Some r1 -> self#emit_expr env e2
      fin
  | Cifthenelse(econd, eif, eelse) ->
      soit (cond, earg) = self#select_condition econd dans
      début filtre self#emit_expr env earg avec
        None -> None
      | Some rarg ->
          soit (rif, sif) = self#emit_sequence env eif dans
          soit (relse, selse) = self#emit_sequence env eelse dans
          soit r = join rif sif relse selse dans
          self#insert (Iifthenelse(cond, sif#extract, selse#extract))
                      rarg [||];
          r
      fin
  | Cswitch(esel, index, ecases) ->
      début filtre self#emit_expr env esel avec
        None -> None
      | Some rsel ->
          soit rscases = Array.map (self#emit_sequence env) ecases dans
          soit r = join_array rscases dans
          self#insert (Iswitch(index,
                               Array.map (fonc (r, s) -> s#extract) rscases))
                      rsel [||];
          r
      fin
  | Cloop(ebody) ->
      soit (rarg, sbody) = self#emit_sequence env ebody dans
      self#insert (Iloop(sbody#extract)) [||] [||];
      Some [||]
  | Ccatch(nfail, ids, e1, e2) ->
      soit rs =
        List.map
          (fonc id ->
            soit r = self#regs_for typ_addr dans name_regs id r; r)
          ids dans
      catch_regs := (nfail, Array.concat rs) :: !catch_regs ;
      soit (r1, s1) = self#emit_sequence env e1 dans
      catch_regs := List.tl !catch_regs ;
      soit new_env =
        List.fold_left
        (fonc env (id,r) -> Tbl.add id r env)
        env (List.combine ids rs) dans
      soit (r2, s2) = self#emit_sequence new_env e2 dans
      soit r = join r1 s1 r2 s2 dans
      self#insert (Icatch(nfail, s1#extract, s2#extract)) [||] [||];
      r
  | Cexit (nfail,args) ->
      début filtre self#emit_parts_list env args avec
        None -> None
      | Some (simple_list, ext_env) ->
          soit src = self#emit_tuple ext_env simple_list dans
          soit dest =
            essaie List.assoc nfail !catch_regs
            avec Not_found ->
              Misc.fatal_error
                ("Selectgen.emit_expr, on exit("^string_of_int nfail^")") dans
          self#insert_moves src dest ;
          self#insert (Iexit nfail) [||] [||];
          None
      fin
  | Ctrywith(e1, v, e2) ->
      Proc.contains_calls := vrai;
      soit (r1, s1) = self#emit_sequence env e1 dans
      soit rv = self#regs_for typ_addr dans
      soit (r2, s2) = self#emit_sequence (Tbl.add v rv env) e2 dans
      soit r = join r1 s1 r2 s2 dans
      self#insert
        (Itrywith(s1#extract,
                  instr_cons (Iop Imove) [|Proc.loc_exn_bucket|] rv
                             (s2#extract)))
        [||] [||];
      r

méthode privée emit_sequence env exp =
  soit s = {< instr_seq = dummy_instr >} dans
  soit r = s#emit_expr env exp dans
  (r, s)

méthode privée bind_let env v r1 =
  si all_regs_anonymous r1 alors début
    name_regs v r1;
    Tbl.add v r1 env
  fin sinon début
    soit rv = Reg.createv_like r1 dans
    name_regs v rv;
    self#insert_moves r1 rv;
    Tbl.add v rv env
  fin

méthode privée emit_parts env exp =
  si self#is_simple_expr exp alors
    Some (exp, env)
  sinon début
    filtre self#emit_expr env exp avec
      None -> None
    | Some r ->
        si Array.length r = 0 alors
          Some (Ctuple [], env)
        sinon début
          (* The normal case *)
          soit id = Ident.create "bind" dans
          si all_regs_anonymous r alors
            (* r is an anonymous, unshared register; use it directly *)
            Some (Cvar id, Tbl.add id r env)
          sinon début
            (* Introduce a fresh temp to hold the result *)
            soit tmp = Reg.createv_like r dans
            self#insert_moves r tmp;
            Some (Cvar id, Tbl.add id tmp env)
          fin
        fin
  fin

méthode privée emit_parts_list env exp_list =
  filtre exp_list avec
    [] -> Some ([], env)
  | exp :: rem ->
      (* This ensures right-to-left evaluation, consistent with the
         bytecode compiler *)
      filtre self#emit_parts_list env rem avec
        None -> None
      | Some(new_rem, new_env) ->
          filtre self#emit_parts new_env exp avec
            None -> None
          | Some(new_exp, fin_env) -> Some(new_exp :: new_rem, fin_env)

méthode privée emit_tuple env exp_list =
  soit rec emit_list = fonction
    [] -> []
  | exp :: rem ->
      (* Again, force right-to-left evaluation *)
      soit loc_rem = emit_list rem dans
      filtre self#emit_expr env exp avec
        None -> affirme faux  (* should have been caught in emit_parts *)
      | Some loc_exp -> loc_exp :: loc_rem dans
  Array.concat(emit_list exp_list)

méthode emit_extcall_args env args =
  soit r1 = self#emit_tuple env args dans
  soit (loc_arg, stack_ofs tel arg_stack) = Proc.loc_external_arguments r1 dans
  self#insert_move_args r1 loc_arg stack_ofs;
  arg_stack

méthode emit_stores env data regs_addr =
  soit a =
    ref (Arch.offset_addressing Arch.identity_addressing (-Arch.size_int)) dans
  List.iter
    (fonc e ->
      soit (op, arg) = self#select_store !a e dans
      filtre self#emit_expr env arg avec
        None -> affirme faux
      | Some regs ->
          filtre op avec
            Istore(_, _) ->
              pour i = 0 à Array.length regs - 1 faire
                soit r = regs.(i) dans
                soit kind = si r.typ = Float alors Double_u sinon Word dans
                self#insert (Iop(Istore(kind, !a)))
                            (Array.append [|r|] regs_addr) [||];
                a := Arch.offset_addressing !a (size_component r.typ)
              fait
          | _ ->
              self#insert (Iop op) (Array.append regs regs_addr) [||];
              a := Arch.offset_addressing !a (size_expr env e))
    data

(* Same, but in tail position *)

méthode privée emit_return env exp =
  filtre self#emit_expr env exp avec
    None -> ()
  | Some r ->
      soit loc = Proc.loc_results r dans
      self#insert_moves r loc;
      self#insert Ireturn loc [||]

méthode emit_tail env exp =
  filtre exp avec
    Clet(v, e1, e2) ->
      début filtre self#emit_expr env e1 avec
        None -> ()
      | Some r1 -> self#emit_tail (self#bind_let env v r1) e2
      fin
  | Cop(Capply(ty, dbg) tel op, args) ->
      début filtre self#emit_parts_list env args avec
        None -> ()
      | Some(simple_args, env) ->
          soit (new_op, new_args) = self#select_operation op simple_args dans
          filtre new_op avec
            Icall_ind ->
              soit r1 = self#emit_tuple env new_args dans
              soit rarg = Array.sub r1 1 (Array.length r1 - 1) dans
              soit (loc_arg, stack_ofs) = Proc.loc_arguments rarg dans
              si stack_ofs = 0 alors début
                self#insert_moves rarg loc_arg;
                self#insert (Iop Itailcall_ind)
                            (Array.append [|r1.(0)|] loc_arg) [||]
              fin sinon début
                Proc.contains_calls := vrai;
                soit rd = self#regs_for ty dans
                soit loc_res = Proc.loc_results rd dans
                self#insert_move_args rarg loc_arg stack_ofs;
                self#insert_debug (Iop Icall_ind) dbg
                            (Array.append [|r1.(0)|] loc_arg) loc_res;
                self#insert(Iop(Istackoffset(-stack_ofs))) [||] [||];
                self#insert Ireturn loc_res [||]
              fin
          | Icall_imm lbl ->
              soit r1 = self#emit_tuple env new_args dans
              soit (loc_arg, stack_ofs) = Proc.loc_arguments r1 dans
              si stack_ofs = 0 alors début
                self#insert_moves r1 loc_arg;
                self#insert (Iop(Itailcall_imm lbl)) loc_arg [||]
              fin sinon si lbl = !current_function_name alors début
                soit loc_arg' = Proc.loc_parameters r1 dans
                self#insert_moves r1 loc_arg';
                self#insert (Iop(Itailcall_imm lbl)) loc_arg' [||]
              fin sinon début
                Proc.contains_calls := vrai;
                soit rd = self#regs_for ty dans
                soit loc_res = Proc.loc_results rd dans
                self#insert_move_args r1 loc_arg stack_ofs;
                self#insert_debug (Iop(Icall_imm lbl)) dbg loc_arg loc_res;
                self#insert(Iop(Istackoffset(-stack_ofs))) [||] [||];
                self#insert Ireturn loc_res [||]
              fin
          | _ -> fatal_error "Selection.emit_tail"
      fin
  | Csequence(e1, e2) ->
      début filtre self#emit_expr env e1 avec
        None -> ()
      | Some r1 -> self#emit_tail env e2
      fin
  | Cifthenelse(econd, eif, eelse) ->
      soit (cond, earg) = self#select_condition econd dans
      début filtre self#emit_expr env earg avec
        None -> ()
      | Some rarg ->
          self#insert (Iifthenelse(cond, self#emit_tail_sequence env eif,
                                         self#emit_tail_sequence env eelse))
                      rarg [||]
      fin
  | Cswitch(esel, index, ecases) ->
      début filtre self#emit_expr env esel avec
        None -> ()
      | Some rsel ->
          self#insert
            (Iswitch(index, Array.map (self#emit_tail_sequence env) ecases))
            rsel [||]
      fin
  | Ccatch(nfail, ids, e1, e2) ->
       soit rs =
        List.map
          (fonc id ->
            soit r = self#regs_for typ_addr dans
            name_regs id r  ;
            r)
          ids dans
      catch_regs := (nfail, Array.concat rs) :: !catch_regs ;
      soit s1 = self#emit_tail_sequence env e1 dans
      catch_regs := List.tl !catch_regs ;
      soit new_env =
        List.fold_left
        (fonc env (id,r) -> Tbl.add id r env)
        env (List.combine ids rs) dans
      soit s2 = self#emit_tail_sequence new_env e2 dans
      self#insert (Icatch(nfail, s1, s2)) [||] [||]
  | Ctrywith(e1, v, e2) ->
      Proc.contains_calls := vrai;
      soit (opt_r1, s1) = self#emit_sequence env e1 dans
      soit rv = self#regs_for typ_addr dans
      soit s2 = self#emit_tail_sequence (Tbl.add v rv env) e2 dans
      self#insert
        (Itrywith(s1#extract,
                  instr_cons (Iop Imove) [|Proc.loc_exn_bucket|] rv s2))
        [||] [||];
      début filtre opt_r1 avec
        None -> ()
      | Some r1 ->
          soit loc = Proc.loc_results r1 dans
          self#insert_moves r1 loc;
          self#insert Ireturn loc [||]
      fin
  | _ ->
      self#emit_return env exp

méthode privée emit_tail_sequence env exp =
  soit s = {< instr_seq = dummy_instr >} dans
  s#emit_tail env exp;
  s#extract

(* Sequentialization of a function definition *)

méthode emit_fundecl f =
  Proc.contains_calls := faux;
  current_function_name := f.Cmm.fun_name;
  soit rargs =
    List.map
      (fonc (id, ty) -> soit r = self#regs_for ty dans name_regs id r; r)
      f.Cmm.fun_args dans
  soit rarg = Array.concat rargs dans
  soit loc_arg = Proc.loc_parameters rarg dans
  soit env =
    List.fold_right2
      (fonc (id, ty) r env -> Tbl.add id r env)
      f.Cmm.fun_args rargs Tbl.empty dans
  self#insert_moves loc_arg rarg;
  self#emit_tail env f.Cmm.fun_body;
  { fun_name = f.Cmm.fun_name;
    fun_args = loc_arg;
    fun_body = self#extract;
    fun_fast = f.Cmm.fun_fast;
    fun_dbg  = f.Cmm.fun_dbg }

fin

(* Tail call criterion (estimated).  Assumes:
- all arguments are of type "int" (always the case for OCaml function calls)
- one extra argument representing the closure environment (conservative).
*)

soit is_tail_call nargs =
  affirme (Reg.dummy.typ = Int);
  soit args = Array.make (nargs + 1) Reg.dummy dans
  soit (loc_arg, stack_ofs) = Proc.loc_arguments args dans
  stack_ofs = 0

soit _ =
  Simplif.is_tail_native_heuristic := is_tail_call
