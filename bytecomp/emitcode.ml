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

(* Generation of bytecode + relocation information *)

ouvre Config
ouvre Misc
ouvre Asttypes
ouvre Lambda
ouvre Instruct
ouvre Opcodes
ouvre Cmo_format

(* Buffering of bytecode *)

soit out_buffer = ref(LongString.create 1024)
et out_position = ref 0

soit out_word b1 b2 b3 b4 =
  soit p = !out_position dans
  si p >= LongString.length !out_buffer alors début
    soit len = LongString.length !out_buffer dans
    soit new_buffer = LongString.create (2 * len) dans
    LongString.blit !out_buffer 0 new_buffer 0 len;
    out_buffer := new_buffer
  fin;
  LongString.set !out_buffer p (Char.unsafe_chr b1);
  LongString.set !out_buffer (p+1) (Char.unsafe_chr b2);
  LongString.set !out_buffer (p+2) (Char.unsafe_chr b3);
  LongString.set !out_buffer (p+3) (Char.unsafe_chr b4);
  out_position := p + 4

soit out opcode =
  out_word opcode 0 0 0


exception AsInt

soit const_as_int = fonction
  | Const_base(Const_int i) -> i
  | Const_base(Const_char c) -> Char.code c
  | Const_pointer i -> i
  | _ -> raise AsInt

soit is_immed i = immed_min <= i && i <= immed_max
soit is_immed_const k =
  essaie
    is_immed (const_as_int k)
  avec
  | AsInt -> faux


soit out_int n =
  out_word n (n dda 8) (n dda 16) (n dda 24)

soit out_const c =
  essaie
    out_int (const_as_int c)
  avec
  | AsInt -> Misc.fatal_error "Emitcode.const_as_int"


(* Handling of local labels and backpatching *)

type label_definition =
    Label_defined de int
  | Label_undefined de (int * int) list

soit label_table  = ref ([| |] : label_definition array)

soit extend_label_table needed =
  soit new_size = ref(Array.length !label_table) dans
  pendant_que needed >= !new_size faire new_size := 2 * !new_size fait;
  soit new_table = Array.create !new_size (Label_undefined []) dans
  Array.blit !label_table 0 new_table 0 (Array.length !label_table);
  label_table := new_table

soit backpatch (pos, orig) =
  soit displ = (!out_position - orig) dda 2 dans
  LongString.set !out_buffer pos (Char.unsafe_chr displ);
  LongString.set !out_buffer (pos+1) (Char.unsafe_chr (displ dda 8));
  LongString.set !out_buffer (pos+2) (Char.unsafe_chr (displ dda 16));
  LongString.set !out_buffer (pos+3) (Char.unsafe_chr (displ dda 24))

soit define_label lbl =
  si lbl >= Array.length !label_table alors extend_label_table lbl;
  filtre (!label_table).(lbl) avec
    Label_defined _ ->
      fatal_error "Emitcode.define_label"
  | Label_undefined patchlist ->
      List.iter backpatch patchlist;
      (!label_table).(lbl) <- Label_defined !out_position

soit out_label_with_orig orig lbl =
  si lbl >= Array.length !label_table alors extend_label_table lbl;
  filtre (!label_table).(lbl) avec
    Label_defined def ->
      out_int((def - orig) dda 2)
  | Label_undefined patchlist ->
      (!label_table).(lbl) <-
         Label_undefined((!out_position, orig) :: patchlist);
      out_int 0

soit out_label l = out_label_with_orig !out_position l

(* Relocation information *)

soit reloc_info = ref ([] : (reloc_info * int) list)

soit enter info =
  reloc_info := (info, !out_position) :: !reloc_info

soit slot_for_literal sc =
  enter (Reloc_literal sc);
  out_int 0
et slot_for_getglobal id =
  enter (Reloc_getglobal id);
  out_int 0
et slot_for_setglobal id =
  enter (Reloc_setglobal id);
  out_int 0
et slot_for_c_prim name =
  enter (Reloc_primitive name);
  out_int 0

(* Debugging events *)

soit events = ref ([] : debug_event list)

soit record_event ev =
  ev.ev_pos <- !out_position;
  events := ev :: !events

(* Initialization *)

soit init () =
  out_position := 0;
  label_table := Array.create 16 (Label_undefined []);
  reloc_info := [];
  events := []

(* Emission of one instruction *)

soit emit_comp = fonction
| Ceq -> out opEQ    | Cneq -> out opNEQ
| Clt -> out opLTINT | Cle -> out opLEINT
| Cgt -> out opGTINT | Cge -> out opGEINT

et emit_branch_comp = fonction
| Ceq -> out opBEQ    | Cneq -> out opBNEQ
| Clt -> out opBLTINT | Cle -> out opBLEINT
| Cgt -> out opBGTINT | Cge -> out opBGEINT

soit emit_instr = fonction
    Klabel lbl -> define_label lbl
  | Kacc n ->
      si n < 8 alors out(opACC0 + n) sinon (out opACC; out_int n)
  | Kenvacc n ->
      si n >= 1 && n <= 4
      alors out(opENVACC1 + n - 1)
      sinon (out opENVACC; out_int n)
  | Kpush ->
      out opPUSH
  | Kpop n ->
      out opPOP; out_int n
  | Kassign n ->
      out opASSIGN; out_int n
  | Kpush_retaddr lbl -> out opPUSH_RETADDR; out_label lbl
  | Kapply n ->
      si n < 4 alors out(opAPPLY1 + n - 1) sinon (out opAPPLY; out_int n)
  | Kappterm(n, sz) ->
      si n < 4 alors (out(opAPPTERM1 + n - 1); out_int sz)
               sinon (out opAPPTERM; out_int n; out_int sz)
  | Kreturn n -> out opRETURN; out_int n
  | Krestart -> out opRESTART
  | Kgrab n -> out opGRAB; out_int n
  | Kclosure(lbl, n) -> out opCLOSURE; out_int n; out_label lbl
  | Kclosurerec(lbls, n) ->
      out opCLOSUREREC; out_int (List.length lbls); out_int n;
      soit org = !out_position dans
      List.iter (out_label_with_orig org) lbls
  | Koffsetclosure ofs ->
      si ofs = -2 || ofs = 0 || ofs = 2
      alors out (opOFFSETCLOSURE0 + ofs / 2)
      sinon (out opOFFSETCLOSURE; out_int ofs)
  | Kgetglobal q -> out opGETGLOBAL; slot_for_getglobal q
  | Ksetglobal q -> out opSETGLOBAL; slot_for_setglobal q
  | Kconst sc ->
      début filtre sc avec
        Const_base(Const_int i) quand is_immed i ->
          si i >= 0 && i <= 3
          alors out (opCONST0 + i)
          sinon (out opCONSTINT; out_int i)
      | Const_base(Const_char c) ->
          out opCONSTINT; out_int (Char.code c)
      | Const_pointer i ->
          si i >= 0 && i <= 3
          alors out (opCONST0 + i)
          sinon (out opCONSTINT; out_int i)
      | Const_block(t, []) ->
          si t = 0 alors out opATOM0 sinon (out opATOM; out_int t)
      | _ ->
          out opGETGLOBAL; slot_for_literal sc
      fin
  | Kmakeblock(n, t) ->
      si n = 0 alors
        si t = 0 alors out opATOM0 sinon (out opATOM; out_int t)
      sinon si n < 4 alors (out(opMAKEBLOCK1 + n - 1); out_int t)
      sinon (out opMAKEBLOCK; out_int n; out_int t)
  | Kgetfield n ->
      si n < 4 alors out(opGETFIELD0 + n) sinon (out opGETFIELD; out_int n)
  | Ksetfield n ->
      si n < 4 alors out(opSETFIELD0 + n) sinon (out opSETFIELD; out_int n)
  | Kmakefloatblock(n) ->
      si n = 0 alors out opATOM0 sinon (out opMAKEFLOATBLOCK; out_int n)
  | Kgetfloatfield n -> out opGETFLOATFIELD; out_int n
  | Ksetfloatfield n -> out opSETFLOATFIELD; out_int n
  | Kvectlength -> out opVECTLENGTH
  | Kgetvectitem -> out opGETVECTITEM
  | Ksetvectitem -> out opSETVECTITEM
  | Kgetstringchar -> out opGETSTRINGCHAR
  | Ksetstringchar -> out opSETSTRINGCHAR
  | Kbranch lbl -> out opBRANCH; out_label lbl
  | Kbranchif lbl -> out opBRANCHIF; out_label lbl
  | Kbranchifnot lbl -> out opBRANCHIFNOT; out_label lbl
  | Kstrictbranchif lbl -> out opBRANCHIF; out_label lbl
  | Kstrictbranchifnot lbl -> out opBRANCHIFNOT; out_label lbl
  | Kswitch(tbl_const, tbl_block) ->
      out opSWITCH;
      out_int (Array.length tbl_const + (Array.length tbl_block dgl 16));
      soit org = !out_position dans
      Array.iter (out_label_with_orig org) tbl_const;
      Array.iter (out_label_with_orig org) tbl_block
  | Kboolnot -> out opBOOLNOT
  | Kpushtrap lbl -> out opPUSHTRAP; out_label lbl
  | Kpoptrap -> out opPOPTRAP
  | Kraise Raise_regular -> out opRAISE
  | Kraise Raise_reraise -> out opRERAISE
  | Kraise Raise_notrace -> out opRAISE_NOTRACE
  | Kcheck_signals -> out opCHECK_SIGNALS
  | Kccall(name, n) ->
      si n <= 5
      alors (out (opC_CALL1 + n - 1); slot_for_c_prim name)
      sinon (out opC_CALLN; out_int n; slot_for_c_prim name)
  | Knegint -> out opNEGINT  | Kaddint -> out opADDINT
  | Ksubint -> out opSUBINT  | Kmulint -> out opMULINT
  | Kdivint -> out opDIVINT  | Kmodint -> out opMODINT
  | Kandint -> out opANDINT  | Korint -> out opORINT
  | Kxorint -> out opXORINT  | Klslint -> out opLSLINT
  | Klsrint -> out opLSRINT  | Kasrint -> out opASRINT
  | Kintcomp c -> emit_comp c
  | Koffsetint n -> out opOFFSETINT; out_int n
  | Koffsetref n -> out opOFFSETREF; out_int n
  | Kisint -> out opISINT
  | Kisout -> out opULTINT
  | Kgetmethod -> out opGETMETHOD
  | Kgetpubmet tag -> out opGETPUBMET; out_int tag; out_int 0
  | Kgetdynmet -> out opGETDYNMET
  | Kevent ev -> record_event ev
  | Kstop -> out opSTOP

(* Emission of a list of instructions. Include some peephole optimization. *)

soit rec emit = fonction
    [] -> ()
  (* Peephole optimizations *)
(* optimization of integer tests *)
  | Kpush::Kconst k::Kintcomp c::Kbranchif lbl::rem
      quand is_immed_const k ->
        emit_branch_comp c ;
        out_const k ;
        out_label lbl ;
        emit rem
  | Kpush::Kconst k::Kintcomp c::Kbranchifnot lbl::rem
      quand is_immed_const k ->
        emit_branch_comp (negate_comparison c) ;
        out_const k ;
        out_label lbl ;
        emit rem
(* same for range tests *)
  | Kpush::Kconst k::Kisout::Kbranchif lbl::rem
      quand is_immed_const k ->
        out opBULTINT ;
        out_const k ;
        out_label lbl ;
        emit rem
  | Kpush::Kconst k::Kisout::Kbranchifnot lbl::rem
      quand is_immed_const k ->
        out opBUGEINT ;
        out_const k ;
        out_label lbl ;
        emit rem
(* Some special case of push ; i ; ret generated by the match compiler *)
  | Kpush :: Kacc 0 :: Kreturn m :: c ->
      emit (Kreturn (m-1) :: c)
(* General push then access scheme *)
  | Kpush :: Kacc n :: c ->
      si n < 8 alors out(opPUSHACC0 + n) sinon (out opPUSHACC; out_int n);
      emit c
  | Kpush :: Kenvacc n :: c ->
      si n >= 1 && n < 4
      alors out(opPUSHENVACC1 + n - 1)
      sinon (out opPUSHENVACC; out_int n);
      emit c
  | Kpush :: Koffsetclosure ofs :: c ->
      si ofs = -2 || ofs = 0 || ofs = 2
      alors out(opPUSHOFFSETCLOSURE0 + ofs / 2)
      sinon (out opPUSHOFFSETCLOSURE; out_int ofs);
      emit c
  | Kpush :: Kgetglobal id :: Kgetfield n :: c ->
      out opPUSHGETGLOBALFIELD; slot_for_getglobal id; out_int n; emit c
  | Kpush :: Kgetglobal id :: c ->
      out opPUSHGETGLOBAL; slot_for_getglobal id; emit c
  | Kpush :: Kconst sc :: c ->
      début filtre sc avec
        Const_base(Const_int i) quand is_immed i ->
          si i >= 0 && i <= 3
          alors out (opPUSHCONST0 + i)
          sinon (out opPUSHCONSTINT; out_int i)
      | Const_base(Const_char c) ->
          out opPUSHCONSTINT; out_int(Char.code c)
      | Const_pointer i ->
          si i >= 0 && i <= 3
          alors out (opPUSHCONST0 + i)
          sinon (out opPUSHCONSTINT; out_int i)
      | Const_block(t, []) ->
          si t = 0 alors out opPUSHATOM0 sinon (out opPUSHATOM; out_int t)
      | _ ->
          out opPUSHGETGLOBAL; slot_for_literal sc
      fin;
      emit c
  | Kpush :: (Kevent {ev_kind = Event_before} tel ev) ::
    (Kgetglobal _ tel instr1) :: (Kgetfield _ tel instr2) :: c ->
      emit (Kpush :: instr1 :: instr2 :: ev :: c)
  | Kpush :: (Kevent {ev_kind = Event_before} tel ev) ::
    (Kacc _ | Kenvacc _ | Koffsetclosure _ | Kgetglobal _ | Kconst _ tel instr)::
    c ->
      emit (Kpush :: instr :: ev :: c)
  | Kgetglobal id :: Kgetfield n :: c ->
      out opGETGLOBALFIELD; slot_for_getglobal id; out_int n; emit c
  (* Default case *)
  | instr :: c ->
      emit_instr instr; emit c

(* Emission to a file *)

soit to_file outchan unit_name code =
  init();
  output_string outchan cmo_magic_number;
  soit pos_depl = pos_out outchan dans
  output_binary_int outchan 0;
  soit pos_code = pos_out outchan dans
  emit code;
  LongString.output outchan !out_buffer 0 !out_position;
  soit (pos_debug, size_debug) =
    si !Clflags.debug alors début
      soit p = pos_out outchan dans
      output_value outchan !events;
      (p, pos_out outchan - p)
    fin sinon
      (0, 0) dans
  soit compunit =
    { cu_name = unit_name;
      cu_pos = pos_code;
      cu_codesize = !out_position;
      cu_reloc = List.rev !reloc_info;
      cu_imports = Env.imported_units();
      cu_primitives = List.map Primitive.byte_name
                               !Translmod.primitive_declarations;
      cu_force_link = faux;
      cu_debug = pos_debug;
      cu_debugsize = size_debug } dans
  init();                               (* Free out_buffer and reloc_info *)
  Btype.cleanup_abbrev ();              (* Remove any cached abbreviation
                                           expansion before saving *)
  soit pos_compunit = pos_out outchan dans
  output_value outchan compunit;
  seek_out outchan pos_depl;
  output_binary_int outchan pos_compunit

(* Emission to a memory block *)

soit to_memory init_code fun_code =
  init();
  emit init_code;
  emit fun_code;
  soit code = Meta.static_alloc !out_position dans
  LongString.unsafe_blit_to_string !out_buffer 0 code 0 !out_position;
  soit reloc = List.rev !reloc_info
  et code_size = !out_position dans
  init();
  (code, code_size, reloc)

(* Emission to a file for a packed library *)

soit to_packed_file outchan code =
  init();
  emit code;
  LongString.output outchan !out_buffer 0 !out_position;
  soit reloc = !reloc_info dans
  init();
  reloc
