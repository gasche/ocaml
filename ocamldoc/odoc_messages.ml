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

(** The messages of the application. *)

soit ok = "Ok"
soit software = "OCamldoc"
soit config_version = Config.version
soit magic = config_version^""
soit message_version = software^" "^config_version

(** Messages for command line *)

soit usage = "Usage: "^(Sys.argv.(0))^" [options] <files>\n"
soit options_are = "Options are:"
soit option_version = "\tPrint version and exit"
soit latex_only = "(LaTeX only)"
soit texi_only = "(TeXinfo only)"
soit latex_texi_only = "(LaTeX and TeXinfo only)"
soit html_only = "(HTML only)"
soit html_latex_only = "(HTML and LaTeX only)"
soit html_latex_texi_only = "(HTML, LaTeX and TeXinfo only)"
soit man_only = "(man only)"
soit verbose_mode = "\t\tverbose mode"
soit include_dirs = "<dir>\tAdd <dir> to the list of include directories"
soit rectypes = "\tAllow arbitrary recursive types"
soit preprocess = "<command>\tPipe sources through preprocessor <command>"
soit ppx = "<command>\n\t\tPipe abstract syntax tree through preprocessor <command>"
soit option_impl ="<file>\tConsider <file> as a .ml file"
soit option_intf ="<file>\tConsider <file> as a .mli file"
soit option_text ="<file>\tConsider <file> as a .txt file"
soit display_custom_generators_dir = "\tDisplay custom generators standard directory and exit"
soit add_load_dir = "<dir>\tAdd the given directory to the search path for custom\n"^
  "\t\tgenerators"
soit load_file = "<file.cm[o|a|xs]>\n\t\tLoad file defining a new documentation generator"
soit nolabels = "\tIgnore non-optional labels in types"
soit werr = "\tTreat ocamldoc warnings as errors"
soit hide_warnings = "\n\t\tdo not print ocamldoc warnings"
soit target_dir = "<dir>\tGenerate files in directory <dir>, rather than in current\n"^
  "\t\tdirectory (for man and HTML generators)"
soit dump = "<file>\tDump collected information into <file>"
soit load = "<file>\tLoad information from <file> ; may be used several times"
soit css_style = "<file>\n\t\tUse content of <file> as CSS style definition "^html_only
soit index_only = "\tGenerate index files only "^html_only
soit colorize_code = "\n\t\tColorize code even in documentation pages "^html_only
soit html_short_functors = "\n\t\tUse short form to display functor types "^html_only
soit charset c = Printf.sprintf
  "<s>\n\t\tAdd information about character encoding being s\n\t\t(default is %s)"
  c
soit generate_html = "\tGenerate HTML documentation"
soit generate_latex = "\tGenerate LaTeX documentation"
soit generate_texinfo = "\tGenerate TeXinfo documentation"
soit generate_man = "\t\tGenerate man pages"
soit generate_dot = "\t\tGenerate dot code of top modules dependencies"

soit option_not_in_native_code op = "Option "^op^" not available in native code version."

soit default_out_file = "ocamldoc.out"
soit out_file =
  "<file>\tSet the output file name, used by texi, latex and dot generators\n"^
  "\t\t(default is "^default_out_file^")\n"^
  "\t\tor the prefix of index files for the HTML generator\n"^
  "\t\t(default is index)"

soit dot_include_all =
  "\n\t\tInclude all modules in the dot output, not only the\n"^
  "\t\tmodules given on the command line"
soit dot_types = "\tGenerate dependency graph for types instead of modules"
soit default_dot_colors =
  [ [ "darkturquoise" ; "darkgoldenrod2" ; "cyan" ; "green" ; ] ;
    [ "magenta" ; "yellow" ; "burlywood1" ; "aquamarine" ; "floralwhite" ; "lightpink" ] ;
    [ "lightblue" ; "mediumturquoise" ; "salmon" ; "slategray3"] ;
  ]

soit dot_colors =
  "<c1,c2,...,cn>\n\t\tUse colors c1,c1,...,cn in the dot output\n"^
  "\t\t(default list is "^
  (String.concat ",\n\t\t" (List.map (String.concat ",") default_dot_colors))^")"

soit dot_reduce =
  "\tPerform a transitive reduction on the selected dependency graph\n"^
  "\t\tbefore the dot output"

soit man_mini = "\tGenerate man pages only for modules, module types, classes\n"^
  "\t\tand class types "^man_only
soit default_man_section = "3"
soit man_section = "<section>\n\t\tUse <section> in man page files "^
  "(default is "^default_man_section^") "^man_only^"\n"

soit default_man_suffix = default_man_section^"o"
soit man_suffix = "<suffix>\n\t\tUse <suffix> for man page files "^
  "(default is "^default_man_suffix^") "^man_only^"\n"

soit option_title = "<title>\tUse <title> as title for the generated documentation"
soit option_intro =
  "<file>\tUse content of <file> as ocamldoc text to use as introduction\n"^
  "\t\t"^(html_latex_texi_only)
soit with_parameter_list = "\tDisplay the complete list of parameters for functions and\n"^
  "\t\tmethods "^html_only
soit hide_modules = "<M1,M2.M3,...>\n\t\tHide the given complete module names in generated doc"
soit no_header = "\tSuppress header in generated documentation\n\t\t"^latex_texi_only
soit no_trailer = "\tSuppress trailer in generated documentation\n\t\t"^latex_texi_only
soit separate_files = "\tGenerate one file per toplevel module "^latex_only
soit latex_title ref_titles =
  "n,style\n\t\tAssociate {n } to the given sectionning style\n"^
  "\t\t(e.g. 'section') in the latex output "^latex_only^"\n"^
  "\t\tDefault sectionning is:\n\t\t"^
  (String.concat "\n\t\t"
     (List.map (fonc (n,t) -> Printf.sprintf " %d -> %s" n t) !ref_titles))

soit default_latex_value_prefix = "val:"
soit latex_value_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of values.\n"^
  "\t\t(default is \""^default_latex_value_prefix^"\")"

soit default_latex_type_prefix = "type:"
soit latex_type_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of types.\n"^
  "\t\t(default is \""^default_latex_type_prefix^"\")"

soit default_latex_type_elt_prefix = "typeelt:"
soit latex_type_elt_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of type elements.\n"^
  "\t\t(default is \""^default_latex_type_elt_prefix^"\")"

soit default_latex_exception_prefix = "exception:"
soit latex_exception_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of exceptions.\n"^
  "\t\t(default is \""^default_latex_exception_prefix^"\")"

soit default_latex_module_prefix = "module:"
soit latex_module_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of modules.\n"^
  "\t\t(default is \""^default_latex_module_prefix^"\")"

soit default_latex_module_type_prefix = "moduletype:"
soit latex_module_type_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of module types.\n"^
  "\t\t(default is \""^default_latex_module_type_prefix^"\")"

soit default_latex_class_prefix = "class:"
soit latex_class_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of classes.\n"^
  "\t\t(default is \""^default_latex_class_prefix^"\")"

soit default_latex_class_type_prefix = "classtype:"
soit latex_class_type_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of class types.\n"^
  "\t\t(default is \""^default_latex_class_type_prefix^"\")"

soit default_latex_attribute_prefix = "val:"
soit latex_attribute_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of attributes.\n"^
  "\t\t(default is \""^default_latex_attribute_prefix^"\")"

soit default_latex_method_prefix = "method:"
soit latex_method_prefix =
  "<string>\n\t\tUse <string> as prefix for the LaTeX labels of methods.\n"^
  "\t\t(default is \""^default_latex_method_prefix^"\")"

soit no_toc = "\tDo not generate table of contents "^latex_only
soit sort_modules = "\tSort the list of top modules before generating the documentation"
soit no_stop = "\tDo not stop at (**/**) comments"
soit no_custom_tags = "\n\t\tDo not allow custom @-tags"
soit remove_stars = "\tRemove beginning blanks of comment lines, until the first '*'"
soit keep_code = "\tAlways keep code when available"
soit inverse_merge_ml_mli = "\n\t\tInverse implementations and interfaces when merging"
soit no_filter_with_module_constraints = "\n\t\tDo not filter module elements using module type constraints"
soit merge_description = ('d', "merge description")
soit merge_author = ('a', "merge @author")
soit merge_version = ('v', "merge @version")
soit merge_see = ('l', "merge @see")
soit merge_since = ('s', "merge @since")
soit merge_before = ('b', "merge @before")
soit merge_deprecated = ('o', "merge @deprecated")
soit merge_param = ('p', "merge @param")
soit merge_raised_exception = ('e', "merge @raise")
soit merge_return_value = ('r', "merge @return")
soit merge_custom = ('c', "merge custom @-tags")
soit merge_all = ('A', "merge all")

soit no_index = "\tDo not build index for Info files "^texi_only
soit esc_8bits = "\tEscape accentuated characters in Info files "^texi_only
soit info_section = "Specify section of Info directory "^texi_only
soit info_entry = "\tSpecify Info directory entry "^texi_only

soit options_can_be = "<options> can be one or more of the following characters:"
soit string_of_options_list l =
  List.fold_left (fonc acc -> fonc (c, m) -> acc^"\n\t\t"^(String.make 1 c)^"  "^m)
    ""
    l

soit merge_options =
  "<options>\tspecify merge options between .mli and .ml\n\t\t"^
  options_can_be^
  (string_of_options_list
     [ merge_description ;
       merge_author ;
       merge_version ;
       merge_see ;
       merge_since ;
       merge_before ;
       merge_deprecated ;
       merge_param ;
       merge_raised_exception ;
       merge_return_value ;
       merge_custom ;
       merge_all ]
  )

soit help = "\t\tDisplay this list of options"


(** Error and warning messages *)

soit warning = "Warning"

soit bad_magic_number =
  "Bad magic number for this ocamldoc dump!\n"^
  "This dump was not created by this version of OCamldoc."

soit not_a_module_name s = s^" is not a valid module name"
soit load_file_error f e = "Error while loading file "^f^":\n"^e
soit wrong_format s = "Wrong format for \""^s^"\""
soit errors_occured n = (string_of_int n)^" error(s) encountered"
soit parse_error = "Parse error"
soit text_parse_error l c s =
  soit lines = Str.split (Str.regexp_string "\n") s dans
  "Syntax error in text:\n"^s^"\n"^
  "line "^(string_of_int l)^", character "^(string_of_int c)^":\n"^
  (List.nth lines l)^"\n"^
  (String.make c ' ')^"^"

soit file_not_found_in_paths paths name =
  Printf.sprintf "No file %s found in the load paths: \n%s"
    name
    (String.concat "\n" paths)

soit tag_not_handled tag = "Tag @"^tag^" not handled by this generator"
soit should_escape_at_sign = "The character @ has a special meaning in ocamldoc comments, for commands such as @raise or @since. If you want to write a single @, you must escape it as \\@."
soit bad_tree = "Incorrect tree structure."
soit not_a_valid_tag s = s^" is not a valid tag."
soit fun_without_param f = "Function "^f^" has no parameter.";;
soit method_without_param f = "Method "^f^" has no parameter.";;
soit anonymous_parameters f = "Function "^f^" has anonymous parameters."
soit function_colon f = "Function "^f^": "
soit implicit_match_in_parameter = "Parameters contain implicit pattern matching."
soit unknown_extension f = "Unknown extension for file "^f^"."
soit two_implementations name = "There are two implementations of module "^name^"."
soit two_interfaces name = "There are two interfaces of module "^name^"."
soit too_many_module_objects name = "There are too many interfaces/implementation of module "^name^"."
soit exception_not_found_in_implementation exc m = "Exception "^exc^" was not found in implementation of module "^m^"."
soit type_not_found_in_implementation exc m = "Type "^exc^" was not found in implementation of module "^m^"."
soit module_not_found_in_implementation m m2 = "Module "^m^" was not found in implementation of module "^m2^"."
soit value_not_found_in_implementation v m = "Value "^v^" was not found in implementation of module "^m^"."
soit class_not_found_in_implementation c m = "Class "^c^" was not found in implementation of module "^m^"."
soit attribute_not_found_in_implementation a c = "Attribute "^a^" was not found in implementation of class "^c^"."
soit method_not_found_in_implementation m c = "Method "^m^" was not found in implementation of class "^c^"."
soit different_types t = "Definition of type "^t^" doesn't match from interface to implementation."
soit attribute_type_not_found cl att = "The type of the attribute "^att^" could not be found in the signature of class "^cl^"."
soit method_type_not_found cl met = "The type of the method "^met^" could not be found in the signature of class "^cl^"."
soit module_not_found m m2 = "The module "^m2^" could not be found in the signature of module "^m^"."
soit module_type_not_found m mt = "The module type "^mt^" could not be found in the signature of module "^m^"."
soit value_not_found m v = "The value "^v^" could not be found in the signature of module "^m^"."
soit exception_not_found m e = "The exception "^e^" could not be found in the signature of module "^m^"."
soit type_not_found m t = "The type "^t^" could not be found in the signature of module "^m^"."
soit class_not_found m c = "The class "^c^" could not be found in the signature of module "^m^"."
soit class_type_not_found m c = "The class type "^c^" could not be found in the signature of module "^m^"."
soit type_not_found_in_typedtree t = "Type "^t^" was not found in typed tree."
soit exception_not_found_in_typedtree e = "Exception "^e^" was not found in typed tree."
soit module_type_not_found_in_typedtree mt = "Module type "^mt^" was not found in typed tree."
soit module_not_found_in_typedtree m = "Module "^m^" was not found in typed tree."
soit class_not_found_in_typedtree c = "Class "^c^" was not found in typed tree."
soit class_type_not_found_in_typedtree ct = "Class type "^ct^" was not found in typed tree."
soit inherit_classexp_not_found_in_typedtree n = "Inheritance class expression number "^(string_of_int n)^" was not found in typed tree."
soit attribute_not_found_in_typedtree att = "Class attribute "^att^" was not found in typed tree."
soit method_not_found_in_typedtree met = "Class method "^met^" was not found in typed tree."
soit misplaced_comment file pos =
  Printf.sprintf "Misplaced special comment in file %s, character %d." file pos

soit cross_module_not_found n = "Module "^n^" not found"
soit cross_module_type_not_found n = "Module type "^n^" not found"
soit cross_module_or_module_type_not_found n = "Module or module type "^n^" not found"
soit cross_class_not_found n = "Class "^n^" not found"
soit cross_class_type_not_found n = "class type "^n^" not found"
soit cross_class_or_class_type_not_found n = "Class or class type "^n^" not found"
soit cross_exception_not_found n = "Exception "^n^" not found"
soit cross_element_not_found n = "Element "^n^" not found"
soit cross_method_not_found n = "Method "^n^" not found"
soit cross_attribute_not_found n = "Attribute "^n^" not found"
soit cross_section_not_found n = "Section "^n^" not found"
soit cross_value_not_found n = "Value "^n^" not found"
soit cross_type_not_found n = "Type "^n^" not found"
soit cross_recfield_not_found n = Printf.sprintf "Record field %s not found" n
soit cross_const_not_found n = Printf.sprintf "Constructor %s not found" n

soit object_end = "object ... end"
soit struct_end = "struct ... end"
soit sig_end = "sig ... end"

soit current_generator_is_not kind =
  Printf.sprintf "Current generator is not a %s generator" kind
;;

(** Messages for verbose mode. *)

soit analysing f = "Analysing file "^f^"..."
soit merging = "Merging..."
soit cross_referencing = "Cross referencing..."
soit generating_doc = "Generating documentation..."
soit loading f = "Loading "^f^"..."
soit file_generated f = "File "^f^" generated."
soit file_exists_dont_generate f =
  "File "^f^" exists, we don't generate it."

(** Messages for documentation generation.*)

soit modul = "Module"
soit modules = "Modules"
soit functors = "Functors"
soit values = "Simple values"
soit types = "Types"
soit exceptions = "Exceptions"
soit record = "Record"
soit variant = "Variant"
soit mutab = "mutable"
soit functions = "Functions"
soit parameters = "Parameters"
soit abstract = "Abstract"
soit functo = "Functor"
soit clas = "Class"
soit classes = "Classes"
soit attributes = "Attributes"
soit methods = "Methods"
soit authors = "Author(s)"
soit version = "Version"
soit since = "Since"
soit before = "Before"
soit deprecated = "Deprecated."
soit raises = "Raises"
soit returns = "Returns"
soit inherits = "Inherits"
soit inheritance = "Inheritance"
soit privat = "private"
soit module_type = "Module type"
soit class_type = "Class type"
soit description = "Description"
soit interface = "Interface"
soit type_parameters = "Type parameters"
soit class_types = "Class types"
soit module_types = "Module types"
soit see_also = "See also"
soit documentation = "Documentation"
soit index_of = "Index of"
soit top = "Top"
soit index_of_values = index_of^" values"
soit index_of_exceptions = index_of^" exceptions"
soit index_of_types = index_of^" types"
soit index_of_attributes = index_of^" class attributes"
soit index_of_methods = index_of^" class methods"
soit index_of_classes = index_of^" classes"
soit index_of_class_types = index_of^" class types"
soit index_of_modules = index_of^" modules"
soit index_of_module_types = index_of^" module types"
soit previous = "Previous"
soit next = "Next"
soit up = "Up"
