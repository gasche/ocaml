(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Nicolas Pouillard *)

ouvre Ocamlbuild_pack
inclus Ocamlbuild_pack.My_std
module Arch = Ocamlbuild_pack.Ocaml_arch
module Command = Ocamlbuild_pack.Command
module Pathname = Ocamlbuild_pack.Pathname
module Tags = Ocamlbuild_pack.Tags
inclus Pathname.Operators
inclus Tags.Operators
module Rule = Ocamlbuild_pack.Rule
module Options = Ocamlbuild_pack.Options
module Findlib = Ocamlbuild_pack.Findlib
type command = Command.t = Seq de command list | Cmd de spec | Echo de string list * string | Nop
et spec = Command.spec =
  | N | S de spec list | A de string | P de string | Px de string
  | Sh de string | T de Tags.t | V de string | Quote de spec
inclus Rule.Common_commands
type env = Pathname.t -> Pathname.t
type builder = Pathname.t list list -> (Pathname.t, exn) Ocamlbuild_pack.My_std.Outcome.t list
type action = env -> builder -> Command.t
soit rule = Rule.rule
soit clear_rules = Rule.clear_rules
soit dep = Command.dep
soit pdep = Command.pdep
soit copy_rule = Rule.copy_rule
soit ocaml_lib = Ocamlbuild_pack.Ocaml_utils.ocaml_lib
soit flag = Ocamlbuild_pack.Flags.flag ?deprecated:None
soit pflag = Ocamlbuild_pack.Flags.pflag
soit mark_tag_used = Ocamlbuild_pack.Flags.mark_tag_used
soit flag_and_dep = Ocamlbuild_pack.Ocaml_utils.flag_and_dep
soit pflag_and_dep = Ocamlbuild_pack.Ocaml_utils.pflag_and_dep
soit non_dependency = Ocamlbuild_pack.Ocaml_utils.non_dependency
soit use_lib = Ocamlbuild_pack.Ocaml_utils.use_lib
soit module_name_of_pathname = Ocamlbuild_pack.Ocaml_utils.module_name_of_pathname
soit string_list_of_file = Ocamlbuild_pack.Ocaml_utils.string_list_of_file
soit expand_module = Ocamlbuild_pack.Ocaml_utils.expand_module
soit tags_of_pathname = Ocamlbuild_pack.Tools.tags_of_pathname
soit hide_package_contents = Ocamlbuild_pack.Ocaml_compiler.hide_package_contents
soit tag_file = Ocamlbuild_pack.Configuration.tag_file
soit tag_any = Ocamlbuild_pack.Configuration.tag_any
soit run_and_read = Ocamlbuild_pack.My_unix.run_and_read
type hook = Ocamlbuild_pack.Hooks.message =
  | Before_hygiene
  | After_hygiene
  | Before_options
  | After_options
  | Before_rules
  | After_rules
soit dispatch = Ocamlbuild_pack.Hooks.setup_hooks
