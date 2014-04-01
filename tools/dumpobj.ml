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

(* Disassembler for executable and .cmo object files *)

ouvre Asttypes
ouvre Config
ouvre Instruct
ouvre Lambda
ouvre Location
ouvre Opcodes
ouvre Opnames
ouvre Cmo_format
ouvre Printf

soit print_locations = ref vrai

(* Read signed and unsigned integers *)

soit inputu ic =
  soit b1 = input_byte ic dans
  soit b2 = input_byte ic dans
  soit b3 = input_byte ic dans
  soit b4 = input_byte ic dans
  (b4 dgl 24) + (b3 dgl 16) + (b2 dgl 8) + b1

soit inputs ic =
  soit b1 = input_byte ic dans
  soit b2 = input_byte ic dans
  soit b3 = input_byte ic dans
  soit b4 = input_byte ic dans
  soit b4' = si b4 >= 128 alors b4-256 sinon b4 dans
  (b4' dgl 24) + (b3 dgl 16) + (b2 dgl 8) + b1

(* Global variables *)

type global_table_entry =
    Empty
  | Global de Ident.t
  | Constant de Obj.t

soit start = ref 0                              (* Position of beg. of code *)
soit reloc = ref ([] : (reloc_info * int) list) (* Relocation table *)
soit globals = ref ([||] : global_table_entry array) (* Global map *)
soit primitives = ref ([||] : string array)     (* Table of primitives *)
soit objfile = ref faux                        (* true if dumping a .cmo *)

(* Events (indexed by PC) *)

soit event_table = (Hashtbl.create 253 : (int, debug_event) Hashtbl.t)

soit relocate_event orig ev =
  ev.ev_pos <- orig + ev.ev_pos;
  filtre ev.ev_repr avec
    Event_parent repr -> repr := ev.ev_pos
  | _                 -> ()

soit record_events orig evl =
  List.iter
    (fonc ev ->
      relocate_event orig ev;
      Hashtbl.add event_table ev.ev_pos ev)
    evl

(* Print a structured constant *)

soit print_float f =
  si String.contains f '.'
  alors printf "%s" f
  sinon printf "%s." f
;;

soit rec print_struct_const = fonction
    Const_base(Const_int i) -> printf "%d" i
  | Const_base(Const_float f) -> print_float f
  | Const_base(Const_string (s, _)) -> printf "%S" s
  | Const_immstring s -> printf "%S" s
  | Const_base(Const_char c) -> printf "%C" c
  | Const_base(Const_int32 i) -> printf "%ldl" i
  | Const_base(Const_nativeint i) -> printf "%ndn" i
  | Const_base(Const_int64 i) -> printf "%LdL" i
  | Const_pointer n -> printf "%da" n
  | Const_block(tag, args) ->
      printf "<%d>" tag;
      début filtre args avec
        [] -> ()
      | [a1] ->
          printf "("; print_struct_const a1; printf ")"
      | a1::al ->
          printf "("; print_struct_const a1;
          List.iter (fonc a -> printf ", "; print_struct_const a) al;
          printf ")"
      fin
  | Const_float_array a ->
      printf "[|";
      List.iter (fonc f -> print_float f; printf "; ") a;
      printf "|]"

(* Print an obj *)

soit same_custom x y =
  Obj.field x 0 = Obj.field (Obj.repr y) 0

soit rec print_obj x =
  si Obj.is_block x alors début
    soit tag = Obj.tag x dans
    si tag = Obj.string_tag alors
        printf "%S" (Obj.magic x : string)
    sinon si tag = Obj.double_tag alors
        printf "%.12g" (Obj.magic x : float)
    sinon si tag = Obj.double_array_tag alors début
        soit a = (Obj.magic x : float array) dans
        printf "[|";
        pour i = 0 à Array.length a - 1 faire
          si i > 0 alors printf ", ";
          printf "%.12g" a.(i)
        fait;
        printf "|]"
    fin sinon si tag = Obj.custom_tag && same_custom x 0l alors
        printf "%ldl" (Obj.magic x : int32)
    sinon si tag = Obj.custom_tag && same_custom x 0n alors
        printf "%ndn" (Obj.magic x : nativeint)
    sinon si tag = Obj.custom_tag && same_custom x 0L alors
        printf "%LdL" (Obj.magic x : int64)
    sinon si tag < Obj.no_scan_tag alors début
        printf "<%d>" (Obj.tag x);
        filtre Obj.size x avec
          0 -> ()
        | 1 ->
            printf "("; print_obj (Obj.field x 0); printf ")"
        | n ->
            printf "("; print_obj (Obj.field x 0);
            pour i = 1 à n - 1 faire
              printf ", "; print_obj (Obj.field x i)
            fait;
            printf ")"
    fin sinon
        printf "<tag %d>" tag
  fin sinon
    printf "%d" (Obj.magic x : int)

(* Current position in input file *)

soit currpos ic =
  pos_in ic - !start

(* Access in the relocation table *)

soit rec rassoc key = fonction
    [] -> raise Not_found
  | (a,b) :: l -> si b = key alors a sinon rassoc key l

soit find_reloc ic =
  rassoc (pos_in ic - !start) !reloc

(* Symbolic printing of global names, etc *)

soit print_getglobal_name ic =
  si !objfile alors début
    début essaie
      filtre find_reloc ic avec
          Reloc_getglobal id -> print_string (Ident.name id)
        | Reloc_literal sc -> print_struct_const sc
        | _ -> print_string "<wrong reloc>"
    avec Not_found ->
      print_string "<no reloc>"
    fin;
    ignore (inputu ic);
  fin
  sinon début
    soit n = inputu ic dans
    si n >= Array.length !globals || n < 0
    alors print_string "<global table overflow>"
    sinon filtre !globals.(n) avec
           Global id -> print_string(Ident.name id)
         | Constant obj -> print_obj obj
         | _ -> print_string "???"
  fin

soit print_setglobal_name ic =
  si !objfile alors début
    début essaie
      filtre find_reloc ic avec
        Reloc_setglobal id -> print_string (Ident.name id)
      | _ -> print_string "<wrong reloc>"
    avec Not_found ->
      print_string "<no reloc>"
    fin;
    ignore (inputu ic);
  fin
  sinon début
    soit n = inputu ic dans
    si n >= Array.length !globals || n < 0
    alors print_string "<global table overflow>"
    sinon filtre !globals.(n) avec
           Global id -> print_string(Ident.name id)
         | _ -> print_string "???"
  fin

soit print_primitive ic =
  si !objfile alors début
    début essaie
      filtre find_reloc ic avec
        Reloc_primitive s -> print_string s
      | _ -> print_string "<wrong reloc>"
    avec Not_found ->
      print_string "<no reloc>"
    fin;
    ignore (inputu ic);
  fin
  sinon début
    soit n = inputu ic dans
    si n >= Array.length !primitives || n < 0
    alors print_int n
    sinon print_string !primitives.(n)
  fin

(* Disassemble one instruction *)

soit currpc ic =
  currpos ic / 4

type shape =
  | Nothing
  | Uint
  | Sint
  | Uint_Uint
  | Disp
  | Uint_Disp
  | Sint_Disp
  | Getglobal
  | Getglobal_Uint
  | Setglobal
  | Primitive
  | Uint_Primitive
  | Switch
  | Closurerec
  | Pubmet
;;

soit op_shapes = [
  opACC0, Nothing;
  opACC1, Nothing;
  opACC2, Nothing;
  opACC3, Nothing;
  opACC4, Nothing;
  opACC5, Nothing;
  opACC6, Nothing;
  opACC7, Nothing;
  opACC, Uint;
  opPUSH, Nothing;
  opPUSHACC0, Nothing;
  opPUSHACC1, Nothing;
  opPUSHACC2, Nothing;
  opPUSHACC3, Nothing;
  opPUSHACC4, Nothing;
  opPUSHACC5, Nothing;
  opPUSHACC6, Nothing;
  opPUSHACC7, Nothing;
  opPUSHACC, Uint;
  opPOP, Uint;
  opASSIGN, Uint;
  opENVACC1, Nothing;
  opENVACC2, Nothing;
  opENVACC3, Nothing;
  opENVACC4, Nothing;
  opENVACC, Uint;
  opPUSHENVACC1, Nothing;
  opPUSHENVACC2, Nothing;
  opPUSHENVACC3, Nothing;
  opPUSHENVACC4, Nothing;
  opPUSHENVACC, Uint;
  opPUSH_RETADDR, Disp;
  opAPPLY, Uint;
  opAPPLY1, Nothing;
  opAPPLY2, Nothing;
  opAPPLY3, Nothing;
  opAPPTERM, Uint_Uint;
  opAPPTERM1, Uint;
  opAPPTERM2, Uint;
  opAPPTERM3, Uint;
  opRETURN, Uint;
  opRESTART, Nothing;
  opGRAB, Uint;
  opCLOSURE, Uint_Disp;
  opCLOSUREREC, Closurerec;
  opOFFSETCLOSUREM2, Nothing;
  opOFFSETCLOSURE0, Nothing;
  opOFFSETCLOSURE2, Nothing;
  opOFFSETCLOSURE, Sint;  (* was Uint *)
  opPUSHOFFSETCLOSUREM2, Nothing;
  opPUSHOFFSETCLOSURE0, Nothing;
  opPUSHOFFSETCLOSURE2, Nothing;
  opPUSHOFFSETCLOSURE, Sint; (* was Nothing *)
  opGETGLOBAL, Getglobal;
  opPUSHGETGLOBAL, Getglobal;
  opGETGLOBALFIELD, Getglobal_Uint;
  opPUSHGETGLOBALFIELD, Getglobal_Uint;
  opSETGLOBAL, Setglobal;
  opATOM0, Nothing;
  opATOM, Uint;
  opPUSHATOM0, Nothing;
  opPUSHATOM, Uint;
  opMAKEBLOCK, Uint_Uint;
  opMAKEBLOCK1, Uint;
  opMAKEBLOCK2, Uint;
  opMAKEBLOCK3, Uint;
  opMAKEFLOATBLOCK, Uint;
  opGETFIELD0, Nothing;
  opGETFIELD1, Nothing;
  opGETFIELD2, Nothing;
  opGETFIELD3, Nothing;
  opGETFIELD, Uint;
  opGETFLOATFIELD, Uint;
  opSETFIELD0, Nothing;
  opSETFIELD1, Nothing;
  opSETFIELD2, Nothing;
  opSETFIELD3, Nothing;
  opSETFIELD, Uint;
  opSETFLOATFIELD, Uint;
  opVECTLENGTH, Nothing;
  opGETVECTITEM, Nothing;
  opSETVECTITEM, Nothing;
  opGETSTRINGCHAR, Nothing;
  opSETSTRINGCHAR, Nothing;
  opBRANCH, Disp;
  opBRANCHIF, Disp;
  opBRANCHIFNOT, Disp;
  opSWITCH, Switch;
  opBOOLNOT, Nothing;
  opPUSHTRAP, Disp;
  opPOPTRAP, Nothing;
  opRAISE, Nothing;
  opCHECK_SIGNALS, Nothing;
  opC_CALL1, Primitive;
  opC_CALL2, Primitive;
  opC_CALL3, Primitive;
  opC_CALL4, Primitive;
  opC_CALL5, Primitive;
  opC_CALLN, Uint_Primitive;
  opCONST0, Nothing;
  opCONST1, Nothing;
  opCONST2, Nothing;
  opCONST3, Nothing;
  opCONSTINT, Sint;
  opPUSHCONST0, Nothing;
  opPUSHCONST1, Nothing;
  opPUSHCONST2, Nothing;
  opPUSHCONST3, Nothing;
  opPUSHCONSTINT, Sint;
  opNEGINT, Nothing;
  opADDINT, Nothing;
  opSUBINT, Nothing;
  opMULINT, Nothing;
  opDIVINT, Nothing;
  opMODINT, Nothing;
  opANDINT, Nothing;
  opORINT, Nothing;
  opXORINT, Nothing;
  opLSLINT, Nothing;
  opLSRINT, Nothing;
  opASRINT, Nothing;
  opEQ, Nothing;
  opNEQ, Nothing;
  opLTINT, Nothing;
  opLEINT, Nothing;
  opGTINT, Nothing;
  opGEINT, Nothing;
  opOFFSETINT, Sint;
  opOFFSETREF, Sint;
  opISINT, Nothing;
  opGETMETHOD, Nothing;
  opGETDYNMET, Nothing;
  opGETPUBMET, Pubmet;
  opBEQ, Sint_Disp;
  opBNEQ, Sint_Disp;
  opBLTINT, Sint_Disp;
  opBLEINT, Sint_Disp;
  opBGTINT, Sint_Disp;
  opBGEINT, Sint_Disp;
  opULTINT, Nothing;
  opUGEINT, Nothing;
  opBULTINT, Uint_Disp;
  opBUGEINT, Uint_Disp;
  opSTOP, Nothing;
  opEVENT, Nothing;
  opBREAK, Nothing;
];;

soit print_event ev =
  si !print_locations alors
    soit ls = ev.ev_loc.loc_start dans
    soit le = ev.ev_loc.loc_end dans
    printf "File \"%s\", line %d, characters %d-%d:\n" ls.Lexing.pos_fname
      ls.Lexing.pos_lnum (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
      (le.Lexing.pos_cnum - ls.Lexing.pos_bol)

soit print_instr ic =
  soit pos = currpos ic dans
  List.iter print_event (Hashtbl.find_all event_table pos);
  printf "%8d  " (pos / 4);
  soit op = inputu ic dans
  si op >= Array.length names_of_instructions || op < 0
  alors (print_string "*** unknown opcode : "; print_int op)
  sinon print_string names_of_instructions.(op);
  print_string " ";
  début essaie filtre List.assoc op op_shapes avec
  | Uint -> print_int (inputu ic)
  | Sint -> print_int (inputs ic)
  | Uint_Uint
     -> print_int (inputu ic); print_string ", "; print_int (inputu ic)
  | Disp -> soit p = currpc ic dans print_int (p + inputs ic)
  | Uint_Disp
     -> print_int (inputu ic); print_string ", ";
        soit p = currpc ic dans print_int (p + inputs ic)
  | Sint_Disp
     -> print_int (inputs ic); print_string ", ";
        soit p = currpc ic dans print_int (p + inputs ic)
  | Getglobal -> print_getglobal_name ic
  | Getglobal_Uint
     -> print_getglobal_name ic; print_string ", "; print_int (inputu ic)
  | Setglobal -> print_setglobal_name ic
  | Primitive -> print_primitive ic
  | Uint_Primitive
     -> print_int(inputu ic); print_string ", "; print_primitive ic
  | Switch
     -> soit n = inputu ic dans
        soit orig = currpc ic dans
        pour i = 0 à (n etl 0xFFFF) - 1 faire
          print_string "\n        int "; print_int i; print_string " -> ";
          print_int(orig + inputs ic);
        fait;
        pour i = 0 à (n ddl 16) - 1 faire
          print_string "\n        tag "; print_int i; print_string " -> ";
          print_int(orig + inputs ic);
        fait;
  | Closurerec
     -> soit nfuncs = inputu ic dans
        soit nvars = inputu ic dans
        soit orig = currpc ic dans
        print_int nvars;
        pour _i = 0 à nfuncs - 1 faire
          print_string ", ";
          print_int (orig + inputs ic);
        fait;
  | Pubmet
     -> soit tag = inputs ic dans
        soit _cache = inputu ic dans
        print_int tag
  | Nothing -> ()
  avec Not_found -> print_string "(unknown arguments)"
  fin;
  print_string "\n";
;;

(* Disassemble a block of code *)

soit print_code ic len =
  start := pos_in ic;
  soit stop = !start + len dans
  pendant_que pos_in ic < stop faire print_instr ic fait

(* Dump relocation info *)

soit print_reloc (info, pos) =
  printf "    %d    (%d)    " pos (pos/4);
  filtre info avec
    Reloc_literal sc -> print_struct_const sc; printf "\n"
  | Reloc_getglobal id -> printf "require    %s\n" (Ident.name id)
  | Reloc_setglobal id -> printf "provide    %s\n" (Ident.name id)
  | Reloc_primitive s -> printf "prim    %s\n" s

(* Print a .cmo file *)

soit dump_obj filename ic =
  soit buffer = Misc.input_bytes ic (String.length cmo_magic_number) dans
  si buffer <> cmo_magic_number alors début
    prerr_endline "Not an object file"; exit 2
  fin;
  soit cu_pos = input_binary_int ic dans
  seek_in ic cu_pos;
  soit cu = (input_value ic : compilation_unit) dans
  reloc := cu.cu_reloc;
  si cu.cu_debug > 0 alors début
    seek_in ic cu.cu_debug;
    soit evl = (input_value ic : debug_event list) dans
    record_events 0 evl
  fin;
  seek_in ic cu.cu_pos;
  print_code ic cu.cu_codesize

(* Read the primitive table from an executable *)

soit read_primitive_table ic len =
  soit p = Misc.input_bytes ic len dans
  soit rec split beg cur =
    si cur >= len alors []
    sinon si p.[cur] = '\000' alors
      String.sub p beg (cur - beg) :: split (cur + 1) (cur + 1)
    sinon
      split beg (cur + 1) dans
  Array.of_list(split 0 0)

(* Print an executable file *)

soit dump_exe ic =
  Bytesections.read_toc ic;
  soit prim_size = Bytesections.seek_section ic "PRIM" dans
  primitives := read_primitive_table ic prim_size;
  ignore(Bytesections.seek_section ic "DATA");
  soit init_data = (input_value ic : Obj.t array) dans
  globals := Array.create (Array.length init_data) Empty;
  pour i = 0 à Array.length init_data - 1 faire
    !globals.(i) <- Constant (init_data.(i))
  fait;
  ignore(Bytesections.seek_section ic "SYMB");
  soit (_, sym_table) = (input_value ic : int * (Ident.t, int) Tbl.t) dans
  Tbl.iter (fonc id pos -> !globals.(pos) <- Global id) sym_table;
  début essaie
    ignore (Bytesections.seek_section ic "DBUG");
    soit num_eventlists = input_binary_int ic dans
    pour _i = 1 à num_eventlists faire
      soit orig = input_binary_int ic dans
      soit evl = (input_value ic : debug_event list) dans
      record_events orig evl
    fait
  avec Not_found -> ()
  fin;
  soit code_size = Bytesections.seek_section ic "CODE" dans
  print_code ic code_size

soit arg_list = [
  "-noloc", Arg.Clear print_locations, " : don't print source information";
]
soit arg_usage =
  Printf.sprintf "%s [OPTIONS] FILES : dump content of bytecode files"
                 Sys.argv.(0)

soit first_file = ref vrai

soit arg_fun filename =
  soit ic = open_in_bin filename dans
  si not !first_file alors print_newline ();
  first_file := faux;
  printf "## start of ocaml dump of %S\n%!" filename;
  début essaie
          objfile := faux; dump_exe ic
    avec Bytesections.Bad_magic_number ->
      objfile := vrai; seek_in ic 0; dump_obj filename ic
  fin;
  close_in ic;
  printf "## end of ocaml dump of %S\n%!" filename

soit main() =
  Arg.parse arg_list arg_fun arg_usage;
    exit 0

soit _ = main ()
