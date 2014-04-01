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

(* Pretty-printing of linearized machine code *)

ouvre Format
ouvre Mach
ouvre Printmach
ouvre Linearize

soit label ppf l =
  Format.fprintf ppf "L%i" l

soit instr ppf i =
  début filtre i.desc avec
  | Lend -> ()
  | Lop op ->
      début filtre op avec
      | Ialloc _ | Icall_ind | Icall_imm _ | Iextcall(_, _) ->
          fprintf ppf "@[<1>{%a}@]@," regsetaddr i.live
      | _ -> ()
      fin;
      operation op i.arg ppf i.res
  | Lreloadretaddr ->
      fprintf ppf "reload retaddr"
  | Lreturn ->
      fprintf ppf "return %a" regs i.arg
  | Llabel lbl ->
      fprintf ppf "%a:" label lbl
  | Lbranch lbl ->
      fprintf ppf "goto %a" label lbl
  | Lcondbranch(tst, lbl) ->
      fprintf ppf "if %a goto %a" (test tst) i.arg label lbl
  | Lcondbranch3(lbl0, lbl1, lbl2) ->
      fprintf ppf "switch3 %a" reg i.arg.(0);
      soit case n = fonction
      | None -> ()
      | Some lbl ->
         fprintf ppf "@,case %i: goto %a" n label lbl dans
      case 0 lbl0; case 1 lbl1; case 2 lbl2;
      fprintf ppf "@,endswitch"
  | Lswitch lblv ->
      fprintf ppf "switch %a" reg i.arg.(0);
      pour i = 0 à Array.length lblv - 1 faire
       fprintf ppf "case %i: goto %a" i label lblv.(i)
      fait;
      fprintf ppf "@,endswitch"
  | Lsetuptrap lbl ->
      fprintf ppf "setup trap %a" label lbl
  | Lpushtrap ->
      fprintf ppf "push trap"
  | Lpoptrap ->
      fprintf ppf "pop trap"
  | Lraise k ->
      fprintf ppf "%s %a" (Lambda.raise_kind k) reg i.arg.(0)
  fin;
  si not (Debuginfo.is_none i.dbg) alors
    fprintf ppf " %s" (Debuginfo.to_string i.dbg)

soit rec all_instr ppf i =
  filtre i.desc avec
  | Lend -> ()
  | _ -> fprintf ppf "%a@,%a" instr i all_instr i.next

soit fundecl ppf f =
  soit dbg =
    si Debuginfo.is_none f.fun_dbg alors
      ""
    sinon
      " " ^ Debuginfo.to_string f.fun_dbg dans
  fprintf ppf "@[<v 2>%s:%s@,%a@]" f.fun_name dbg all_instr f.fun_body
