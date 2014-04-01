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

(* From lambda to assembly code *)

ouvre Format
ouvre Config
ouvre Clflags
ouvre Misc
ouvre Cmm

type error = Assembler_error de string

exception Error de error

soit liveness ppf phrase =
  Liveness.fundecl ppf phrase; phrase

soit dump_if ppf flag message phrase =
  si !flag alors Printmach.phase message ppf phrase

soit pass_dump_if ppf flag message phrase =
  dump_if ppf flag message phrase; phrase

soit pass_dump_linear_if ppf flag message phrase =
  si !flag alors fprintf ppf "*** %s@.%a@." message Printlinear.fundecl phrase;
  phrase

soit clambda_dump_if ppf ulambda =
  si !dump_clambda alors Printclambda.clambda ppf ulambda; ulambda

soit rec regalloc ppf round fd =
  si round > 50 alors
    fatal_error(fd.Mach.fun_name ^
                ": fonction trop complexe, impossible de finir l'allocation de registres");
  dump_if ppf dump_live "Liveness analysis" fd;
  Interf.build_graph fd;
  si !dump_interf alors Printmach.interferences ppf ();
  si !dump_prefer alors Printmach.preferences ppf ();
  Coloring.allocate_registers();
  dump_if ppf dump_regalloc "After register allocation" fd;
  soit (newfd, redo_regalloc) = Reload.fundecl fd dans
  dump_if ppf dump_reload "After insertion of reloading code" newfd;
  si redo_regalloc alors début
    Reg.reinit(); Liveness.fundecl ppf newfd; regalloc ppf (round + 1) newfd
  fin sinon newfd

soit (++) x f = f x

soit compile_fundecl (ppf : formatter) fd_cmm =
  Proc.init ();
  Reg.reset();
  fd_cmm
  ++ Selection.fundecl
  ++ pass_dump_if ppf dump_selection "After instruction selection"
  ++ Comballoc.fundecl
  ++ pass_dump_if ppf dump_combine "After allocation combining"
  ++ liveness ppf
  ++ pass_dump_if ppf dump_live "Liveness analysis"
  ++ Spill.fundecl
  ++ liveness ppf
  ++ pass_dump_if ppf dump_spill "After spilling"
  ++ Split.fundecl
  ++ pass_dump_if ppf dump_split "After live range splitting"
  ++ liveness ppf
  ++ regalloc ppf 1
  ++ Linearize.fundecl
  ++ pass_dump_linear_if ppf dump_linear "Linearized code"
  ++ Scheduling.fundecl
  ++ pass_dump_linear_if ppf dump_scheduling "After instruction scheduling"
  ++ Emit.fundecl

soit compile_phrase ppf p =
  si !dump_cmm alors fprintf ppf "%a@." Printcmm.phrase p;
  filtre p avec
  | Cfunction fd -> compile_fundecl ppf fd
  | Cdata dl -> Emit.data dl


(* For the native toplevel: generates generic functions unless
   they are already available in the process *)
soit compile_genfuns ppf f =
  List.iter
    (fonction
       | (Cfunction {fun_name = name}) tel ph quand f name ->
           compile_phrase ppf ph
       | _ -> ())
    (Cmmgen.generic_functions vrai [Compilenv.current_unit_infos ()])

soit compile_implementation ?toplevel prefixname ppf (size, lam) =
  soit asmfile =
    si !keep_asm_file
    alors prefixname ^ ext_asm
    sinon Filename.temp_file "camlasm" ext_asm dans
  soit oc = open_out asmfile dans
  début essaie
    Emitaux.output_channel := oc;
    Emit.begin_assembly();
    Closure.intro size lam
    ++ clambda_dump_if ppf
    ++ Cmmgen.compunit size
    ++ List.iter (compile_phrase ppf) ++ (fonc () -> ());
    (filtre toplevel avec None -> () | Some f -> compile_genfuns ppf f);

    (* We add explicit references to external primitive symbols.  This
       is to ensure that the object files that define these symbols,
       when part of a C library, won't be discarded by the linker.
       This is important if a module that uses such a symbol is later
       dynlinked. *)

    compile_phrase ppf
      (Cmmgen.reference_symbols
         (List.filter (fonc s -> s <> "" && s.[0] <> '%')
            (List.map Primitive.native_name !Translmod.primitive_declarations))
      );

    Emit.end_assembly();
    close_out oc
  avec x ->
    close_out oc;
    si !keep_asm_file alors () sinon remove_file asmfile;
    raise x
  fin;
  si Proc.assemble_file asmfile (prefixname ^ ext_obj) <> 0
  alors raise(Error(Assembler_error asmfile));
  si !keep_asm_file alors () sinon remove_file asmfile

(* Error report *)

soit report_error ppf = fonction
  | Assembler_error file ->
      fprintf ppf "Erreur d'assemblage, entrée laissée dans le fichier %a"
        Location.print_filename file

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
