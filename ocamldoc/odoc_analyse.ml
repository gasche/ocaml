(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Analysis of source files. This module is strongly inspired from
    driver/main.ml :-) *)

soit print_DEBUG s = print_string s ; print_newline ()

ouvre Config
ouvre Clflags
ouvre Misc
ouvre Format
ouvre Typedtree


(** Initialize the search path.
   The current directory is always searched first,
   then the directories specified with the -I option (in command-line order),
   then the standard library directory. *)
soit init_path () =
  load_path :=
    "" :: List.rev (Config.standard_library :: !Clflags.include_dirs);
  Env.reset_cache ()

(** Return the initial environment in which compilation proceeds. *)
soit initial_env () =
  essaie
    si !Clflags.nopervasives
    alors Env.initial
    sinon Env.open_pers_signature "Pervasives" Env.initial
  avec Not_found ->
    fatal_error "impossible d'ouvrir pervasives.cmi"

(** Optionally preprocess a source file *)
soit preprocess sourcefile =
  essaie
    Pparse.preprocess sourcefile
  avec Pparse.Error err ->
    Format.eprintf "Erreur de prétraitement@.%a@."
      Pparse.report_error err;
    exit 2

soit (++) x f = f x

(** Analysis of an implementation file. Returns (Some typedtree) if
   no error occured, else None and an error message is printed.*)
soit process_implementation_file ppf sourcefile =
  init_path ();
  soit prefixname = Filename.chop_extension sourcefile dans
  soit modulename = String.capitalize(Filename.basename prefixname) dans
  Env.set_unit_name modulename;
  soit inputfile = preprocess sourcefile dans
  soit env = initial_env () dans
  essaie
    soit parsetree = Pparse.file Format.err_formatter inputfile Parse.implementation ast_impl_magic_number dans
    soit typedtree =
      Typemod.type_implementation
        sourcefile prefixname modulename env parsetree
    dans
    (Some (parsetree, typedtree), inputfile)
  avec
    e ->
      filtre e avec
        Syntaxerr.Error err ->
          fprintf Format.err_formatter "@[%a@]@."
            Syntaxerr.report_error err;
          None, inputfile
      | Failure s ->
          prerr_endline s;
          incr Odoc_global.errors ;
          None, inputfile
      | e ->
          raise e

(** Analysis of an interface file. Returns (Some signature) if
   no error occured, else None and an error message is printed.*)
soit process_interface_file ppf sourcefile =
  init_path ();
  soit prefixname = Filename.chop_extension sourcefile dans
  soit modulename = String.capitalize(Filename.basename prefixname) dans
  Env.set_unit_name modulename;
  soit inputfile = preprocess sourcefile dans
  soit ast = Pparse.file Format.err_formatter inputfile Parse.interface ast_intf_magic_number dans
  soit sg = Typemod.transl_signature (initial_env()) ast dans
  Warnings.check_fatal ();
  (ast, sg, inputfile)

(** The module used to analyse the parsetree and signature of an implementation file.*)
module Ast_analyser = Odoc_ast.Analyser (Odoc_comments.Basic_info_retriever)

(** The module used to analyse the parse tree and typed tree of an interface file.*)
module Sig_analyser = Odoc_sig.Analyser (Odoc_comments.Basic_info_retriever)

(** Handle an error. *)

soit process_error exn =
  filtre Location.error_of_exn exn avec
  | Some err ->
      fprintf Format.err_formatter "@[%a@]@." Location.report_error err
  | None ->
      fprintf Format.err_formatter
        "Erreur de compilation(%s). Utilisez le compilateur Chamelle pour obtenir plus de détails.@."
        (Printexc.to_string exn)

(** Process the given file, according to its extension. Return the Module.t created, if any.*)
soit process_file ppf sourcefile =
  si !Odoc_global.verbose alors
    (
     soit f = filtre sourcefile avec
       Odoc_global.Impl_file f
     | Odoc_global.Intf_file f -> f
     | Odoc_global.Text_file f -> f
     dans
     print_string (Odoc_messages.analysing f) ;
     print_newline ();
    );
  filtre sourcefile avec
    Odoc_global.Impl_file file ->
      (
       Location.input_name := file;
       essaie
         soit (parsetree_typedtree_opt, input_file) = process_implementation_file ppf file dans
         filtre parsetree_typedtree_opt avec
           None ->
             None
         | Some (parsetree, typedtree) ->
             soit file_module = Ast_analyser.analyse_typed_tree file
                 !Location.input_name parsetree typedtree
             dans
             file_module.Odoc_module.m_top_deps <- Odoc_dep.impl_dependencies parsetree ;

             si !Odoc_global.verbose alors
               (
                print_string Odoc_messages.ok;
                print_newline ()
               );
             Pparse.remove_preprocessed input_file;
             Some file_module
       avec
       | Sys_error s
       | Failure s ->
           prerr_endline s ;
           incr Odoc_global.errors ;
           None
       | e ->
           process_error e ;
           incr Odoc_global.errors ;
           None
      )
  | Odoc_global.Intf_file file ->
      (
       Location.input_name := file;
       essaie
         soit (ast, signat, input_file) = process_interface_file ppf file dans
         soit file_module = Sig_analyser.analyse_signature file
             !Location.input_name ast signat.sig_type
         dans

         file_module.Odoc_module.m_top_deps <- Odoc_dep.intf_dependencies ast ;

         si !Odoc_global.verbose alors
           (
            print_string Odoc_messages.ok;
            print_newline ()
           );
         Pparse.remove_preprocessed input_file;
         Some file_module
       avec
       | Sys_error s
       | Failure s ->
           prerr_endline s;
           incr Odoc_global.errors ;
           None
       | e ->
           process_error e ;
           incr Odoc_global.errors ;
           None
      )
  | Odoc_global.Text_file file ->
      Location.input_name := file;
      essaie
        soit mod_name =
          soit s =
            essaie Filename.chop_extension file
            avec _ -> file
          dans
          String.capitalize (Filename.basename s)
        dans
        soit txt =
          essaie Odoc_text.Texter.text_of_string (Odoc_misc.input_file_as_string file)
          avec Odoc_text.Text_syntax (l, c, s) ->
            raise (Failure (Odoc_messages.text_parse_error l c s))
        dans
        soit m =
          {
            Odoc_module.m_name = mod_name ;
            Odoc_module.m_type = Types.Mty_signature [] ;
            Odoc_module.m_info = None ;
            Odoc_module.m_is_interface = vrai ;
            Odoc_module.m_file = file ;
            Odoc_module.m_kind = Odoc_module.Module_struct
              [Odoc_module.Element_module_comment txt] ;
            Odoc_module.m_loc =
              { Odoc_types.loc_impl = None ;
                Odoc_types.loc_inter = Some (Location.in_file file) } ;
            Odoc_module.m_top_deps = [] ;
            Odoc_module.m_code = None ;
            Odoc_module.m_code_intf = None ;
            Odoc_module.m_text_only = vrai ;
          }
        dans
        Some m
      avec
       | Sys_error s
       | Failure s ->
           prerr_endline s;
           incr Odoc_global.errors ;
           None
       | e ->
           process_error e ;
           incr Odoc_global.errors ;
           None

(** Remove the class elements between the stop special comments. *)
soit rec remove_class_elements_between_stop keep eles =
  filtre eles avec
    [] -> []
  | ele :: q ->
      filtre ele avec
        Odoc_class.Class_comment [ Odoc_types.Raw "/*" ] ->
          remove_class_elements_between_stop (not keep) q
      | Odoc_class.Class_attribute _
      | Odoc_class.Class_method _
      | Odoc_class.Class_comment _ ->
          si keep alors
            ele :: (remove_class_elements_between_stop keep q)
          sinon
            remove_class_elements_between_stop keep q

(** Remove the class elements between the stop special comments in a class kind. *)
soit rec remove_class_elements_between_stop_in_class_kind k =
  filtre k avec
    Odoc_class.Class_structure (inher, l) ->
      Odoc_class.Class_structure (inher, remove_class_elements_between_stop vrai l)
  | Odoc_class.Class_apply _ -> k
  | Odoc_class.Class_constr _ -> k
  | Odoc_class.Class_constraint (k1, ctk) ->
      Odoc_class.Class_constraint (remove_class_elements_between_stop_in_class_kind k1,
                        remove_class_elements_between_stop_in_class_type_kind ctk)

(** Remove the class elements beetween the stop special comments in a class type kind. *)
et remove_class_elements_between_stop_in_class_type_kind tk =
  filtre tk avec
    Odoc_class.Class_signature (inher, l) ->
      Odoc_class.Class_signature (inher, remove_class_elements_between_stop vrai l)
  | Odoc_class.Class_type _ -> tk


(** Remove the module elements between the stop special comments. *)
soit rec remove_module_elements_between_stop keep eles =
  soit f = remove_module_elements_between_stop dans
  filtre eles avec
    [] -> []
  | ele :: q ->
      filtre ele avec
        Odoc_module.Element_module_comment [ Odoc_types.Raw "/*" ] ->
          f (not keep) q
      | Odoc_module.Element_module_comment _ ->
          si keep alors
            ele :: (f keep q)
          sinon
            f keep q
      | Odoc_module.Element_module m ->
          si keep alors
            (
             m.Odoc_module.m_kind <- remove_module_elements_between_stop_in_module_kind m.Odoc_module.m_kind ;
             (Odoc_module.Element_module m) :: (f keep q)
            )
          sinon
            f keep q
      | Odoc_module.Element_module_type mt ->
          si keep alors
            (
             mt.Odoc_module.mt_kind <- Odoc_misc.apply_opt
                 remove_module_elements_between_stop_in_module_type_kind mt.Odoc_module.mt_kind ;
             (Odoc_module.Element_module_type mt) :: (f keep q)
            )
          sinon
            f keep q
      | Odoc_module.Element_included_module _ ->
          si keep alors
            ele :: (f keep q)
          sinon
            f keep q
      | Odoc_module.Element_class c ->
          si keep alors
            (
             c.Odoc_class.cl_kind <- remove_class_elements_between_stop_in_class_kind c.Odoc_class.cl_kind ;
             (Odoc_module.Element_class c) :: (f keep q)
            )
          sinon
            f keep q
      | Odoc_module.Element_class_type ct ->
          si keep alors
            (
             ct.Odoc_class.clt_kind <- remove_class_elements_between_stop_in_class_type_kind ct.Odoc_class.clt_kind ;
             (Odoc_module.Element_class_type ct) :: (f keep q)
            )
          sinon
            f keep q
      | Odoc_module.Element_value _
      | Odoc_module.Element_exception _
      | Odoc_module.Element_type _ ->
          si keep alors
            ele :: (f keep q)
          sinon
            f keep q


(** Remove the module elements between the stop special comments, in the given module kind. *)
et remove_module_elements_between_stop_in_module_kind k =
  filtre k avec
  | Odoc_module.Module_struct l -> Odoc_module.Module_struct (remove_module_elements_between_stop vrai l)
  | Odoc_module.Module_alias _ -> k
  | Odoc_module.Module_functor (params, k2)  ->
      Odoc_module.Module_functor (params, remove_module_elements_between_stop_in_module_kind k2)
  | Odoc_module.Module_apply (k1, k2) ->
      Odoc_module.Module_apply (remove_module_elements_between_stop_in_module_kind k1,
                    remove_module_elements_between_stop_in_module_kind k2)
  | Odoc_module.Module_with (mtkind, s) ->
      Odoc_module.Module_with (remove_module_elements_between_stop_in_module_type_kind mtkind, s)
  | Odoc_module.Module_constraint (k2, mtkind) ->
      Odoc_module.Module_constraint (remove_module_elements_between_stop_in_module_kind k2,
                         remove_module_elements_between_stop_in_module_type_kind mtkind)
  | Odoc_module.Module_typeof _ -> k
  | Odoc_module.Module_unpack _ -> k

(** Remove the module elements between the stop special comment, in the given module type kind. *)
et remove_module_elements_between_stop_in_module_type_kind tk =
  filtre tk avec
  | Odoc_module.Module_type_struct l -> Odoc_module.Module_type_struct (remove_module_elements_between_stop vrai l)
  | Odoc_module.Module_type_functor (params, tk2) ->
      Odoc_module.Module_type_functor (params, remove_module_elements_between_stop_in_module_type_kind tk2)
  | Odoc_module.Module_type_alias _ -> tk
  | Odoc_module.Module_type_with (tk2, s) ->
      Odoc_module.Module_type_with (remove_module_elements_between_stop_in_module_type_kind tk2, s)
  | Odoc_module.Module_type_typeof _ -> tk

(** Remove elements between the stop special comment. *)
soit remove_elements_between_stop module_list =
  List.map
    (fonc m ->
      m.Odoc_module.m_kind <- remove_module_elements_between_stop_in_module_kind m.Odoc_module.m_kind;
      m
    )
    module_list

(** This function builds the modules from the given list of source files. *)
soit analyse_files ?(init=[]) files =
  soit modules_pre =
    init @
    (List.fold_left
       (fonc acc -> fonc file ->
         essaie
           filtre process_file Format.err_formatter file avec
             None ->
               acc
           | Some m ->
               acc @ [ m ]
         avec
           Failure s ->
             prerr_endline s ;
             incr Odoc_global.errors ;
             acc
       )
       []
       files
    )
  dans
  (* Remove elements between the stop special comments, if needed. *)
  soit modules =
    si !Odoc_global.no_stop alors
      modules_pre
    sinon
      remove_elements_between_stop modules_pre
  dans


  si !Odoc_global.verbose alors
    (
     print_string Odoc_messages.merging;
     print_newline ()
    );
  soit merged_modules = Odoc_merge.merge !Odoc_global.merge_options modules dans
  si !Odoc_global.verbose alors
    (
     print_string Odoc_messages.ok;
     print_newline ();
    );
  soit modules_list =
    (List.fold_left
       (fonc acc -> fonc m -> acc @ (Odoc_module.module_all_submodules ~trans: faux m))
       merged_modules
       merged_modules
    )
  dans
  si !Odoc_global.verbose alors
    (
     print_string Odoc_messages.cross_referencing;
     print_newline ()
    );
  soit _ = Odoc_cross.associate modules_list dans

  si !Odoc_global.verbose alors
    (
     print_string Odoc_messages.ok;
     print_newline ();
    );

  si !Odoc_global.sort_modules alors
    Sort.list (fonc m1 -> fonc m2 -> m1.Odoc_module.m_name < m2.Odoc_module.m_name) merged_modules
  sinon
    merged_modules

soit dump_modules file (modules : Odoc_module.t_module list) =
  essaie
    soit chanout = open_out_bin file dans
    soit dump = Odoc_types.make_dump modules dans
    output_value chanout dump;
    close_out chanout
  avec
    Sys_error s ->
      raise (Failure s)

soit load_modules file =
  essaie
    soit chanin = open_in_bin file dans
    soit dump = input_value chanin dans
    close_in chanin ;
    soit (l : Odoc_module.t_module list) = Odoc_types.open_dump dump dans
    l
  avec
    Sys_error s ->
      raise (Failure s)
