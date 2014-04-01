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

(* Common functions for emitting assembly code *)

ouvre Debuginfo

soit output_channel = ref stdout

soit emit_string s = output_string !output_channel s

soit emit_int n = output_string !output_channel (string_of_int n)

soit emit_char c = output_char !output_channel c

soit emit_nativeint n = output_string !output_channel (Nativeint.to_string n)

soit emit_printf fmt =
  Printf.fprintf !output_channel fmt

soit emit_int32 n = emit_printf "0x%lx" n

soit emit_symbol esc s =
  pour i = 0 à String.length s - 1 faire
    soit c = s.[i] dans
    filtre c avec
      'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
        output_char !output_channel c
    | _ ->
        Printf.fprintf !output_channel "%c%02x" esc (Char.code c)
  fait

soit emit_string_literal s =
  soit last_was_escape = ref faux dans
  emit_string "\"";
  pour i = 0 à String.length s - 1 faire
    soit c = s.[i] dans
    si c >= '0' && c <= '9' alors
      si !last_was_escape
      alors Printf.fprintf !output_channel "\\%o" (Char.code c)
      sinon output_char !output_channel c
    sinon si c >= ' ' && c <= '~' && c <> '"' (* '"' *) && c <> '\\' alors début
      output_char !output_channel c;
      last_was_escape := faux
    fin sinon début
      Printf.fprintf !output_channel "\\%o" (Char.code c);
      last_was_escape := vrai
    fin
  fait;
  emit_string "\""

soit emit_string_directive directive s =
  soit l = String.length s dans
  si l = 0 alors ()
  sinon si l < 80 alors début
    emit_string directive;
    emit_string_literal s;
    emit_char '\n'
  fin sinon début
    soit i = ref 0 dans
    pendant_que !i < l faire
      soit n = min (l - !i) 80 dans
      emit_string directive;
      emit_string_literal (String.sub s !i n);
      emit_char '\n';
      i := !i + n
    fait
  fin

soit emit_bytes_directive directive s =
   soit pos = ref 0 dans
   pour i = 0 à String.length s - 1 faire
     si !pos = 0
     alors emit_string directive
     sinon emit_char ',';
     emit_int(Char.code s.[i]);
     incr pos;
     si !pos >= 16 alors début emit_char '\n'; pos := 0 fin
   fait;
   si !pos > 0 alors emit_char '\n'

(* PR#4813: assemblers do strange things with float literals indeed,
   so we convert to IEEE representation ourselves and emit float
   literals as 32- or 64-bit integers. *)

soit emit_float64_directive directive f =
  soit x = Int64.bits_of_float (float_of_string f) dans
  emit_printf "\t%s\t0x%Lx\n" directive x

soit emit_float64_split_directive directive f =
  soit x = Int64.bits_of_float (float_of_string f) dans
  soit lo = Int64.logand x 0xFFFF_FFFFL
  et hi = Int64.shift_right_logical x 32 dans
  emit_printf "\t%s\t0x%Lx, 0x%Lx\n"
    directive
    (si Arch.big_endian alors hi sinon lo)
    (si Arch.big_endian alors lo sinon hi)

soit emit_float32_directive directive f =
  soit x = Int32.bits_of_float (float_of_string f) dans
  emit_printf "\t%s\t0x%lx\n" directive x

(* Record live pointers at call points *)

type frame_descr =
  { fd_lbl: int;                        (* Return address *)
    fd_frame_size: int;                 (* Size of stack frame *)
    fd_live_offset: int list;           (* Offsets/regs of live addresses *)
    fd_debuginfo: Debuginfo.t }         (* Location, if any *)

soit frame_descriptors = ref([] : frame_descr list)

type emit_frame_actions =
  { efa_label: int -> unit;
    efa_16: int -> unit;
    efa_32: int32 -> unit;
    efa_word: int -> unit;
    efa_align: int -> unit;
    efa_label_rel: int -> int32 -> unit;
    efa_def_label: int -> unit;
    efa_string: string -> unit }

soit emit_frames a =
  soit filenames = Hashtbl.create 7 dans
  soit label_filename name =
    essaie
      Hashtbl.find filenames name
    avec Not_found ->
      soit lbl = Linearize.new_label () dans
      Hashtbl.add filenames name lbl;
      lbl dans
  soit emit_frame fd =
    a.efa_label fd.fd_lbl;
    a.efa_16 (si Debuginfo.is_none fd.fd_debuginfo
              alors fd.fd_frame_size
              sinon fd.fd_frame_size + 1);
    a.efa_16 (List.length fd.fd_live_offset);
    List.iter a.efa_16 fd.fd_live_offset;
    a.efa_align Arch.size_addr;
    si not (Debuginfo.is_none fd.fd_debuginfo) alors début
      soit d = fd.fd_debuginfo dans
      soit line = min 0xFFFFF d.dinfo_line
      et char_start = min 0xFF d.dinfo_char_start
      et char_end = min 0x3FF d.dinfo_char_end
      et kind = filtre d.dinfo_kind avec Dinfo_call -> 0 | Dinfo_raise -> 1 dans
      soit info =
        Int64.add (Int64.shift_left (Int64.of_int line) 44) (
        Int64.add (Int64.shift_left (Int64.of_int char_start) 36) (
        Int64.add (Int64.shift_left (Int64.of_int char_end) 26)
                  (Int64.of_int kind))) dans
      a.efa_label_rel
        (label_filename d.dinfo_file)
        (Int64.to_int32 info);
      a.efa_32 (Int64.to_int32 (Int64.shift_right info 32))
    fin dans
  soit emit_filename name lbl =
    a.efa_def_label lbl;
    a.efa_string name;
    a.efa_align Arch.size_addr dans
  a.efa_word (List.length !frame_descriptors);
  List.iter emit_frame !frame_descriptors;
  Hashtbl.iter emit_filename filenames;
  frame_descriptors := []

(* Detection of functions that can be duplicated between a DLL and
   the main program (PR#4690) *)

soit isprefix s1 s2 =
  String.length s1 <= String.length s2
  && String.sub s2 0 (String.length s1) = s1

soit is_generic_function name =
  List.exists
    (fonc p -> isprefix p name)
    ["caml_apply"; "caml_curry"; "caml_send"; "caml_tuplify"]

(* CFI directives *)

soit is_cfi_enabled () =
  Config.asm_cfi_supported

soit cfi_startproc () =
  si is_cfi_enabled () alors
    emit_string "\t.cfi_startproc\n"

soit cfi_endproc () =
  si is_cfi_enabled () alors
    emit_string "\t.cfi_endproc\n"

soit cfi_adjust_cfa_offset n =
  si is_cfi_enabled () alors
  début
    emit_string "\t.cfi_adjust_cfa_offset\t"; emit_int n; emit_string "\n";
  fin

(* Emit debug information *)

(* This assoc list is expected to be very short *)
soit file_pos_nums =
  (ref [] : (string * int) list ref)

(* Number of files *)
soit file_pos_num_cnt = ref 1

(* Reset debug state at beginning of asm file *)
soit reset_debug_info () =
  file_pos_nums := [];
  file_pos_num_cnt := 1

(* We only diplay .file if the file has not been seen before. We
   display .loc for every instruction. *)
soit emit_debug_info dbg =
  si is_cfi_enabled () &&
    (!Clflags.debug || Config.with_frame_pointers)
     && dbg.Debuginfo.dinfo_line > 0 (* PR#6243 *)
  alors début
    soit line = dbg.Debuginfo.dinfo_line dans
    soit file_name = dbg.Debuginfo.dinfo_file dans
    soit file_num =
      essaie List.assoc file_name !file_pos_nums
      avec Not_found ->
        soit file_num = !file_pos_num_cnt dans
        incr file_pos_num_cnt;
        emit_string "\t.file\t";
        emit_int file_num; emit_char '\t';
        emit_string_literal file_name; emit_char '\n';
        file_pos_nums := (file_name,file_num) :: !file_pos_nums;
        file_num dans
    emit_string "\t.loc\t";
    emit_int file_num; emit_char '\t';
    emit_int line; emit_char '\n'
  fin
