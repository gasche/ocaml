(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*      Damien Doligez and Francois Rouaix, INRIA Rocquencourt         *)
(*          Ported to Caml Special Light by John Malecki               *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Printf

ouvre Location
ouvre Parsetree

(* User programs must not use identifiers that start with these prefixes. *)
soit idprefix = "__ocaml_prof_";;
soit modprefix = "OCAML__prof_";;

(* Errors specific to the profiler *)
exception Profiler de string

(* Modes *)
soit instr_fun    = ref faux
et instr_match  = ref faux
et instr_if     = ref faux
et instr_loops  = ref faux
et instr_try    = ref faux

soit cur_point = ref 0
et inchan = ref stdin
et outchan = ref stdout

(* To copy source fragments *)
soit copy_buffer = String.create 256

soit copy_chars_unix nchars =
  soit n = ref nchars dans
  pendant_que !n > 0 faire
    soit m = input !inchan copy_buffer 0 (min !n 256) dans
    si m = 0 alors raise End_of_file;
    output !outchan copy_buffer 0 m;
    n := !n - m
  fait

soit copy_chars_win32 nchars =
  pour _i = 1 à nchars faire
    soit c = input_char !inchan dans
    si c <> '\r' alors output_char !outchan c
  fait

soit copy_chars =
  filtre Sys.os_type avec
    "Win32" | "Cygwin" -> copy_chars_win32
  | _       -> copy_chars_unix

soit copy next =
  affirme (next >= !cur_point);
  seek_in !inchan !cur_point;
  copy_chars (next - !cur_point);
  cur_point := next;
;;

soit prof_counter = ref 0;;

soit instr_mode = ref faux

type insert = Open | Close;;
soit to_insert = ref ([] : (insert * int) list);;

soit insert_action st en =
  to_insert := (Open, st) :: (Close, en) :: !to_insert
;;

(* Producing instrumented code *)
soit add_incr_counter modul (kind,pos) =
   copy pos;
   filtre kind avec
   | Open ->
         fprintf !outchan "(%sProfiling.incr %s%s_cnt %d; "
                 modprefix idprefix modul !prof_counter;
         incr prof_counter;
   | Close -> fprintf !outchan ")";
;;

soit counters = ref (Array.create 0 0)

(* User defined marker *)
soit special_id = ref ""

(* Producing results of profile run *)
soit add_val_counter (kind,pos) =
  si kind = Open alors début
    copy pos;
    fprintf !outchan "(* %s%d *) " !special_id !counters.(!prof_counter);
    incr prof_counter;
  fin
;;

(* ************* rewrite ************* *)

soit insert_profile rw_exp ex =
  soit st = ex.pexp_loc.loc_start.Lexing.pos_cnum
  et en = ex.pexp_loc.loc_end.Lexing.pos_cnum
  et gh = ex.pexp_loc.loc_ghost
  dans
  si gh || st = en alors
    rw_exp vrai ex
  sinon début
    insert_action st en;
    rw_exp faux ex;
  fin
;;


soit pos_len = ref 0

soit init_rewrite modes mod_name =
  cur_point := 0;
  si !instr_mode alors début
    fprintf !outchan "module %sProfiling = Profiling;; " modprefix;
    fprintf !outchan "let %s%s_cnt = Array.create 000000000" idprefix mod_name;
    pos_len := pos_out !outchan;
    fprintf !outchan
            " 0;; Profiling.counters := \
              (\"%s\", (\"%s\", %s%s_cnt)) :: !Profiling.counters;; "
            mod_name modes idprefix mod_name;
  fin

soit final_rewrite add_function =
  to_insert := Sort.list (fonc x y -> snd x < snd y) !to_insert;
  prof_counter := 0;
  List.iter add_function !to_insert;
  copy (in_channel_length !inchan);
  si !instr_mode alors début
    soit len = string_of_int !prof_counter dans
    si String.length len > 9 alors raise (Profiler "too many counters");
    seek_out !outchan (!pos_len - String.length len);
    output_string !outchan len
  fin;
  (* Cannot close because outchan is stdout and Format doesn't like
     a closed stdout.
    close_out !outchan;
  *)
;;

soit rec rewrite_patexp_list iflag l =
  rewrite_exp_list iflag (List.map (fonc x -> x.pvb_expr) l)

et rewrite_cases iflag l =
  List.iter
    (fonc pc ->
      début filtre pc.pc_guard avec
      | None -> ()
      | Some g -> rewrite_exp iflag g
      fin;
      rewrite_exp iflag pc.pc_rhs
    )
    l

et rewrite_labelexp_list iflag l =
  rewrite_exp_list iflag (List.map snd l)

et rewrite_exp_list iflag l =
  List.iter (rewrite_exp iflag) l

et rewrite_exp iflag sexp =
  si iflag alors insert_profile rw_exp sexp
           sinon rw_exp faux sexp

et rw_exp iflag sexp =
  filtre sexp.pexp_desc avec
    Pexp_ident lid -> ()
  | Pexp_constant cst -> ()

  | Pexp_let(_, spat_sexp_list, sbody) ->
    rewrite_patexp_list iflag spat_sexp_list;
    rewrite_exp iflag sbody

  | Pexp_function caselist ->
    si !instr_fun alors
      rewrite_function iflag caselist
    sinon
      rewrite_cases iflag caselist

  | Pexp_fun (_, _, p, e) ->
      soit l = [{pc_lhs=p; pc_guard=None; pc_rhs=e}] dans
      si !instr_fun alors
        rewrite_function iflag l
      sinon
        rewrite_cases iflag l

  | Pexp_match(sarg, caselist) ->
    rewrite_exp iflag sarg;
    si !instr_match && not sexp.pexp_loc.loc_ghost alors
      rewrite_funmatching caselist
    sinon
      rewrite_cases iflag caselist

  | Pexp_try(sbody, caselist) ->
    rewrite_exp iflag sbody;
    si !instr_try && not sexp.pexp_loc.loc_ghost alors
      rewrite_trymatching caselist
    sinon
      rewrite_cases iflag caselist

  | Pexp_apply(sfunct, sargs) ->
    rewrite_exp iflag sfunct;
    rewrite_exp_list iflag (List.map snd sargs)

  | Pexp_tuple sexpl ->
    rewrite_exp_list iflag sexpl

  | Pexp_construct(_, None) -> ()
  | Pexp_construct(_, Some sarg) ->
    rewrite_exp iflag sarg

  | Pexp_variant(_, None) -> ()
  | Pexp_variant(_, Some sarg) ->
    rewrite_exp iflag sarg

  | Pexp_record(lid_sexp_list, None) ->
    rewrite_labelexp_list iflag lid_sexp_list
  | Pexp_record(lid_sexp_list, Some sexp) ->
    rewrite_exp iflag sexp;
    rewrite_labelexp_list iflag lid_sexp_list

  | Pexp_field(sarg, _) ->
    rewrite_exp iflag sarg

  | Pexp_setfield(srecord, _, snewval) ->
    rewrite_exp iflag srecord;
    rewrite_exp iflag snewval

  | Pexp_array(sargl) ->
    rewrite_exp_list iflag sargl

  | Pexp_ifthenelse(scond, sifso, None) ->
      rewrite_exp iflag scond;
      rewrite_ifbody iflag sexp.pexp_loc.loc_ghost sifso
  | Pexp_ifthenelse(scond, sifso, Some sifnot) ->
      rewrite_exp iflag scond;
      rewrite_ifbody iflag sexp.pexp_loc.loc_ghost sifso;
      rewrite_ifbody iflag sexp.pexp_loc.loc_ghost sifnot

  | Pexp_sequence(sexp1, sexp2) ->
    rewrite_exp iflag sexp1;
    rewrite_exp iflag sexp2

  | Pexp_while(scond, sbody) ->
    rewrite_exp iflag scond;
    si !instr_loops && not sexp.pexp_loc.loc_ghost
    alors insert_profile rw_exp sbody
    sinon rewrite_exp iflag sbody

  | Pexp_for(_, slow, shigh, _, sbody) ->
    rewrite_exp iflag slow;
    rewrite_exp iflag shigh;
    si !instr_loops && not sexp.pexp_loc.loc_ghost
    alors insert_profile rw_exp sbody
    sinon rewrite_exp iflag sbody

  | Pexp_constraint(sarg, _) | Pexp_coerce(sarg, _, _) ->
    rewrite_exp iflag sarg

  | Pexp_send (sobj, _) ->
    rewrite_exp iflag sobj

  | Pexp_new _ -> ()

  | Pexp_setinstvar (_, sarg) ->
    rewrite_exp iflag sarg

  | Pexp_override l ->
      List.iter (fonc (_, sexp) -> rewrite_exp iflag sexp) l

  | Pexp_letmodule (_, smod, sexp) ->
      rewrite_mod iflag smod;
      rewrite_exp iflag sexp

  | Pexp_assert (cond) -> rewrite_exp iflag cond

  | Pexp_lazy (expr) -> rewrite_exp iflag expr

  | Pexp_poly (sexp, _) -> rewrite_exp iflag sexp

  | Pexp_object cl ->
      List.iter (rewrite_class_field iflag) cl.pcstr_fields

  | Pexp_newtype (_, sexp) -> rewrite_exp iflag sexp
  | Pexp_open (_ovf, _, e) -> rewrite_exp iflag e
  | Pexp_pack (smod) -> rewrite_mod iflag smod
  | Pexp_extension _ -> ()

et rewrite_ifbody iflag ghost sifbody =
  si !instr_if && not ghost alors
    insert_profile rw_exp sifbody
  sinon
    rewrite_exp iflag sifbody

(* called only when !instr_fun *)
et rewrite_annotate_exp_list l =
  List.iter
    (fonction
     | {pc_guard=Some scond; pc_rhs=sbody} ->
         insert_profile rw_exp scond;
         insert_profile rw_exp sbody;
     | {pc_rhs={pexp_desc = Pexp_constraint(sbody, _)}} (* let f x : t = e *)
        -> insert_profile rw_exp sbody
     | {pc_rhs=sexp} -> insert_profile rw_exp sexp)
    l

et rewrite_function iflag = fonction
  | [{pc_lhs=spat; pc_guard=None;
      pc_rhs={pexp_desc = (Pexp_function _|Pexp_fun _)} tel sexp}] ->
        rewrite_exp iflag sexp
  | l -> rewrite_funmatching l

et rewrite_funmatching l =
  rewrite_annotate_exp_list l

et rewrite_trymatching l =
  rewrite_annotate_exp_list l

(* Rewrite a class definition *)

et rewrite_class_field iflag cf =
  filtre cf.pcf_desc avec
    Pcf_inherit (_, cexpr, _)     -> rewrite_class_expr iflag cexpr
  | Pcf_val (_, _, Cfk_concrete (_, sexp))  -> rewrite_exp iflag sexp
  | Pcf_method (_, _,
                Cfk_concrete (_, ({pexp_desc = (Pexp_function _|Pexp_fun _)}
                                    tel sexp))) ->
      rewrite_exp iflag sexp
  | Pcf_method (_, _, Cfk_concrete(_, sexp)) ->
      soit loc = cf.pcf_loc dans
      si !instr_fun && not loc.loc_ghost alors insert_profile rw_exp sexp
      sinon rewrite_exp iflag sexp
  | Pcf_initializer sexp ->
      rewrite_exp iflag sexp
  | Pcf_method (_, _, Cfk_virtual _)
  | Pcf_val (_, _, Cfk_virtual _)
  | Pcf_constraint _  -> ()
  | Pcf_extension _ -> ()

et rewrite_class_expr iflag cexpr =
  filtre cexpr.pcl_desc avec
    Pcl_constr _ -> ()
  | Pcl_structure st ->
      List.iter (rewrite_class_field iflag) st.pcstr_fields
  | Pcl_fun (_, _, _, cexpr) ->
      rewrite_class_expr iflag cexpr
  | Pcl_apply (cexpr, exprs) ->
      rewrite_class_expr iflag cexpr;
      List.iter (rewrite_exp iflag) (List.map snd exprs)
  | Pcl_let (_, spat_sexp_list, cexpr) ->
      rewrite_patexp_list iflag spat_sexp_list;
      rewrite_class_expr iflag cexpr
  | Pcl_constraint (cexpr, _) ->
      rewrite_class_expr iflag cexpr
  | Pcl_extension _ -> ()

et rewrite_class_declaration iflag cl =
  rewrite_class_expr iflag cl.pci_expr

(* Rewrite a module expression or structure expression *)

et rewrite_mod iflag smod =
  filtre smod.pmod_desc avec
    Pmod_ident lid -> ()
  | Pmod_structure sstr -> List.iter (rewrite_str_item iflag) sstr
  | Pmod_functor(param, smty, sbody) -> rewrite_mod iflag sbody
  | Pmod_apply(smod1, smod2) -> rewrite_mod iflag smod1; rewrite_mod iflag smod2
  | Pmod_constraint(smod, smty) -> rewrite_mod iflag smod
  | Pmod_unpack(sexp) -> rewrite_exp iflag sexp
  | Pmod_extension _ -> ()

et rewrite_str_item iflag item =
  filtre item.pstr_desc avec
    Pstr_eval (exp, _attrs) -> rewrite_exp iflag exp
  | Pstr_value(_, exps)
     -> List.iter (fonc x -> rewrite_exp iflag x.pvb_expr) exps
  | Pstr_module x -> rewrite_mod iflag x.pmb_expr
        (* todo: Pstr_recmodule?? *)
  | Pstr_class classes -> List.iter (rewrite_class_declaration iflag) classes
  | _ -> ()

(* Rewrite a .ml file *)
soit rewrite_file srcfile add_function =
  inchan := open_in_bin srcfile;
  soit lb = Lexing.from_channel !inchan dans
  Location.input_name := srcfile;
  Location.init lb srcfile;
  List.iter (rewrite_str_item faux) (Parse.implementation lb);
  final_rewrite add_function;
  close_in !inchan

(* Copy a non-.ml file without change *)
soit null_rewrite srcfile =
  inchan := open_in_bin srcfile;
  copy (in_channel_length !inchan);
  close_in !inchan
;;

(* Setting flags from saved config *)
soit set_flags s =
  pour i = 0 à String.length s - 1 faire
    filtre String.get s i avec
      'f' -> instr_fun := vrai
    | 'm' -> instr_match := vrai
    | 'i' -> instr_if := vrai
    | 'l' -> instr_loops := vrai
    | 't' -> instr_try := vrai
    | 'a' -> instr_fun := vrai; instr_match := vrai;
             instr_if := vrai; instr_loops := vrai;
             instr_try := vrai
    | _ -> ()
    fait

(* Command-line options *)

soit modes = ref "fm"
soit dumpfile = ref "ocamlprof.dump"

(* Process a file *)

soit process_intf_file filename = null_rewrite filename;;

soit process_impl_file filename =
   soit modname = Filename.basename(Filename.chop_extension filename) dans
       (* FIXME should let modname = String.capitalize modname *)
   si !instr_mode alors début
     (* Instrumentation mode *)
     set_flags !modes;
     init_rewrite !modes modname;
     rewrite_file filename (add_incr_counter modname);
   fin sinon début
     (* Results mode *)
     soit ic = open_in_bin !dumpfile dans
     soit allcounters =
       (input_value ic : (string * (string * int array)) list) dans
     close_in ic;
     soit (modes, cv) =
       essaie
         List.assoc modname allcounters
       avec Not_found ->
         raise(Profiler("Module " ^ modname ^ " not used in this profile."))
     dans
     counters := cv;
     set_flags modes;
     init_rewrite modes modname;
     rewrite_file filename add_val_counter;
   fin
;;

soit process_anon_file filename =
  si Filename.check_suffix filename ".ml" alors
    process_impl_file filename
  sinon
    process_intf_file filename
;;

(* Main function *)

ouvre Format

soit usage = "Usage: ocamlprof <options> <files>\noptions are:"

soit print_version () =
  printf "ocamlprof, version %s@." Sys.ocaml_version;
  exit 0;
;;

soit print_version_num () =
  printf "%s@." Sys.ocaml_version;
  exit 0;
;;

soit main () =
  essaie
    Warnings.parse_options faux "a";
    Arg.parse [
       "-f", Arg.String (fonc s -> dumpfile := s),
             "<file>     Use <file> as dump file (default ocamlprof.dump)";
       "-F", Arg.String (fonc s -> special_id := s),
             "<s>        Insert string <s> with the counts";
       "-impl", Arg.String process_impl_file,
                "<file>  Process <file> as a .ml file";
       "-instrument", Arg.Set instr_mode, "  (undocumented)";
       "-intf", Arg.String process_intf_file,
                "<file>  Process <file> as a .mli file";
       "-m", Arg.String (fonc s -> modes := s), "<flags>    (undocumented)";
       "-version", Arg.Unit print_version,
                   "     Print version and exit";
       "-vnum", Arg.Unit print_version_num,
                "        Print version number and exit";
      ] process_anon_file usage;
    exit 0
  avec
  | Profiler msg ->
      fprintf Format.err_formatter "@[%s@]@." msg;
      exit 2
  | exn ->
      Location.report_exception Format.err_formatter exn

soit _ = main ()
