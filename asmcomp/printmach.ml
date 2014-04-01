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

(* Pretty-printing of pseudo machine code *)

ouvre Format
ouvre Cmm
ouvre Reg
ouvre Mach

soit reg ppf r =
  si not (Reg.anonymous r) alors
    fprintf ppf "%s" (Reg.name r)
  sinon
    fprintf ppf "%s" (filtre r.typ avec Addr -> "A" | Int -> "I" | Float -> "F");
  fprintf ppf "/%i" r.stamp;
  début filtre r.loc avec
  | Unknown -> ()
  | Reg r ->
      fprintf ppf "[%s]" (Proc.register_name r)
  | Stack(Local s) ->
      fprintf ppf "[s%i]" s
  | Stack(Incoming s) ->
      fprintf ppf "[si%i]" s
  | Stack(Outgoing s) ->
      fprintf ppf "[so%i]" s
  fin

soit regs ppf v =
  filtre Array.length v avec
  | 0 -> ()
  | 1 -> reg ppf v.(0)
  | n -> reg ppf v.(0);
         pour i = 1 à n-1 faire fprintf ppf " %a" reg v.(i) fait

soit regset ppf s =
  soit first = ref vrai dans
  Reg.Set.iter
    (fonc r ->
      si !first alors début first := faux; fprintf ppf "%a" reg r fin
      sinon fprintf ppf "@ %a" reg r)
    s

soit regsetaddr ppf s =
  soit first = ref vrai dans
  Reg.Set.iter
    (fonc r ->
      si !first alors début first := faux; fprintf ppf "%a" reg r fin
      sinon fprintf ppf "@ %a" reg r;
      filtre r.typ avec Addr -> fprintf ppf "*" | _ -> ())
    s

soit intcomp = fonction
  | Isigned c -> Printf.sprintf " %ss " (Printcmm.comparison c)
  | Iunsigned c -> Printf.sprintf " %su " (Printcmm.comparison c)

soit floatcomp c =
    Printf.sprintf " %sf " (Printcmm.comparison c)

soit intop = fonction
  | Iadd -> " + "
  | Isub -> " - "
  | Imul -> " * "
  | Imulh -> " *h "
  | Idiv -> " div "
  | Imod -> " mod "
  | Iand -> " & "
  | Ior ->  " | "
  | Ixor -> " ^ "
  | Ilsl -> " << "
  | Ilsr -> " >>u "
  | Iasr -> " >>s "
  | Icomp cmp -> intcomp cmp
  | Icheckbound -> " check > "

soit test tst ppf arg =
  filtre tst avec
  | Itruetest -> reg ppf arg.(0)
  | Ifalsetest -> fprintf ppf "not %a" reg arg.(0)
  | Iinttest cmp -> fprintf ppf "%a%s%a" reg arg.(0) (intcomp cmp) reg arg.(1)
  | Iinttest_imm(cmp, n) -> fprintf ppf "%a%s%i" reg arg.(0) (intcomp cmp) n
  | Ifloattest(cmp, neg) ->
      fprintf ppf "%s%a%s%a"
       (si neg alors "not " sinon "")
       reg arg.(0) (floatcomp cmp) reg arg.(1)
  | Ieventest -> fprintf ppf "%a & 1 == 0" reg arg.(0)
  | Ioddtest -> fprintf ppf "%a & 1 == 1" reg arg.(0)

soit print_live = ref faux

soit operation op arg ppf res =
  si Array.length res > 0 alors fprintf ppf "%a := " regs res;
  filtre op avec
  | Imove -> regs ppf arg
  | Ispill -> fprintf ppf "%a (spill)" regs arg
  | Ireload -> fprintf ppf "%a (reload)" regs arg
  | Iconst_int n
  | Iconst_blockheader n -> fprintf ppf "%s" (Nativeint.to_string n)
  | Iconst_float s -> fprintf ppf "%s" s
  | Iconst_symbol s -> fprintf ppf "\"%s\"" s
  | Icall_ind -> fprintf ppf "call %a" regs arg
  | Icall_imm lbl -> fprintf ppf "call \"%s\" %a" lbl regs arg
  | Itailcall_ind -> fprintf ppf "tailcall %a" regs arg
  | Itailcall_imm lbl -> fprintf ppf "tailcall \"%s\" %a" lbl regs arg
  | Iextcall(lbl, alloc) ->
      fprintf ppf "extcall \"%s\" %a%s" lbl regs arg
      (si alloc alors "" sinon " (noalloc)")
  | Istackoffset n ->
      fprintf ppf "offset stack %i" n
  | Iload(chunk, addr) ->
      fprintf ppf "%s[%a]"
       (Printcmm.chunk chunk) (Arch.print_addressing reg addr) arg
  | Istore(chunk, addr) ->
      fprintf ppf "%s[%a] := %a"
       (Printcmm.chunk chunk)
       (Arch.print_addressing reg addr)
       (Array.sub arg 1 (Array.length arg - 1))
       reg arg.(0)
  | Ialloc n -> fprintf ppf "alloc %i" n
  | Iintop(op) -> fprintf ppf "%a%s%a" reg arg.(0) (intop op) reg arg.(1)
  | Iintop_imm(op, n) -> fprintf ppf "%a%s%i" reg arg.(0) (intop op) n
  | Inegf -> fprintf ppf "-f %a" reg arg.(0)
  | Iabsf -> fprintf ppf "absf %a" reg arg.(0)
  | Iaddf -> fprintf ppf "%a +f %a" reg arg.(0) reg arg.(1)
  | Isubf -> fprintf ppf "%a -f %a" reg arg.(0) reg arg.(1)
  | Imulf -> fprintf ppf "%a *f %a" reg arg.(0) reg arg.(1)
  | Idivf -> fprintf ppf "%a /f %a" reg arg.(0) reg arg.(1)
  | Ifloatofint -> fprintf ppf "floatofint %a" reg arg.(0)
  | Iintoffloat -> fprintf ppf "intoffloat %a" reg arg.(0)
  | Ispecific op ->
      Arch.print_specific_operation reg op ppf arg

soit rec instr ppf i =
  si !print_live alors début
    fprintf ppf "@[<1>{%a" regsetaddr i.live;
    si Array.length i.arg > 0 alors fprintf ppf "@ +@ %a" regs i.arg;
    fprintf ppf "}@]@,";
  fin;
  début filtre i.desc avec
  | Iend -> ()
  | Iop op ->
      operation op i.arg ppf i.res
  | Ireturn ->
      fprintf ppf "return %a" regs i.arg
  | Iifthenelse(tst, ifso, ifnot) ->
      fprintf ppf "@[<v 2>if %a then@,%a" (test tst) i.arg instr ifso;
      début filtre ifnot.desc avec
      | Iend -> ()
      | _ -> fprintf ppf "@;<0 -2>else@,%a" instr ifnot
      fin;
      fprintf ppf "@;<0 -2>endif@]"
  | Iswitch(index, cases) ->
      fprintf ppf "switch %a" reg i.arg.(0);
      pour i = 0 à Array.length cases - 1 faire
        fprintf ppf "@,@[<v 2>@[";
        pour j = 0 à Array.length index - 1 faire
          si index.(j) = i alors fprintf ppf "case %i:@," j
        fait;
        fprintf ppf "@]@,%a@]" instr cases.(i)
      fait;
      fprintf ppf "@,endswitch"
  | Iloop(body) ->
      fprintf ppf "@[<v 2>loop@,%a@;<0 -2>endloop@]" instr body
  | Icatch(i, body, handler) ->
      fprintf
        ppf "@[<v 2>catch@,%a@;<0 -2>with(%d)@,%a@;<0 -2>endcatch@]"
        instr body i instr handler
  | Iexit i ->
      fprintf ppf "exit(%d)" i
  | Itrywith(body, handler) ->
      fprintf ppf "@[<v 2>try@,%a@;<0 -2>with@,%a@;<0 -2>endtry@]"
             instr body instr handler
  | Iraise k ->
      fprintf ppf "%s %a" (Lambda.raise_kind k) reg i.arg.(0)
  fin;
  si not (Debuginfo.is_none i.dbg) alors
    fprintf ppf "%s" (Debuginfo.to_string i.dbg);
  début filtre i.next.desc avec
    Iend -> ()
  | _ -> fprintf ppf "@,%a" instr i.next
  fin

soit fundecl ppf f =
  soit dbg =
    si Debuginfo.is_none f.fun_dbg alors
      ""
    sinon
      " " ^ Debuginfo.to_string f.fun_dbg dans
  fprintf ppf "@[<v 2>%s(%a)%s@,%a@]"
    f.fun_name regs f.fun_args dbg instr f.fun_body

soit phase msg ppf f =
  fprintf ppf "*** %s@.%a@." msg fundecl f

soit interference ppf r =
  soit interf ppf =
   List.iter
    (fonc r -> fprintf ppf "@ %a" reg r)
    r.interf dans
  fprintf ppf "@[<2>%a:%t@]@." reg r interf

soit interferences ppf () =
  fprintf ppf "*** Interferences@.";
  List.iter (interference ppf) (Reg.all_registers())

soit preference ppf r =
  soit prefs ppf =
    List.iter
      (fonc (r, w) -> fprintf ppf "@ %a weight %i" reg r w)
      r.prefer dans
  fprintf ppf "@[<2>%a: %t@]@." reg r prefs

soit preferences ppf () =
  fprintf ppf "*** Preferences@.";
  List.iter (preference ppf) (Reg.all_registers())
