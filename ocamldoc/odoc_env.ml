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

(** Environment for finding complete names from relative names. *)

soit print_DEBUG s = print_string s ; print_newline ();;

module Name = Odoc_name

(** relative name * complete name *)
type env_element = Name.t * Name.t

type env = {
    env_values : env_element list ;
    env_types : env_element list ;
    env_class_types : env_element list ;
    env_classes : env_element list ;
    env_modules : env_element list ;
    env_module_types : env_element list ;
    env_exceptions : env_element list ;
  }

soit empty = {
  env_values = [] ;
  env_types = [] ;
  env_class_types = [] ;
  env_classes = [] ;
  env_modules = [] ;
  env_module_types = [] ;
  env_exceptions = [] ;
  }

(** Add a signature to an environment.  *)
soit rec add_signature env root ?rel signat =
  soit qualify id = Name.concat root (Name.from_ident id) dans
  soit rel_name id =
    soit n = Name.from_ident id dans
    filtre rel avec
      None -> n
    | Some r -> Name.concat r n
  dans
  soit f env item =
    filtre item avec
      Types.Sig_value (ident, _) -> { env avec env_values = (rel_name ident, qualify ident) :: env.env_values }
    | Types.Sig_type (ident,_,_) -> { env avec env_types = (rel_name ident, qualify ident) :: env.env_types }
    | Types.Sig_exception (ident, _) -> { env avec env_exceptions = (rel_name ident, qualify ident) :: env.env_exceptions }
    | Types.Sig_module (ident, md, _) ->
        soit env2 =
          filtre md.Types.md_type avec (* A VOIR : le cas ou c'est un identificateur, dans ce cas on n'a pas de signature *)
            Types.Mty_signature s -> add_signature env (qualify ident) ~rel: (rel_name ident) s
          |  _ -> env
        dans
        { env2 avec env_modules = (rel_name ident, qualify ident) :: env2.env_modules }
    | Types.Sig_modtype (ident, modtype_decl) ->
        soit env2 =
          filtre modtype_decl.Types.mtd_type avec
            None ->
              env
          | Some modtype ->
              filtre modtype avec
                 (* A VOIR : le cas ou c'est un identificateur, dans ce cas on n'a pas de signature *)
                Types.Mty_signature s -> add_signature env (qualify ident) ~rel: (rel_name ident) s
              |  _ -> env
        dans
        { env2 avec env_module_types = (rel_name ident, qualify ident) :: env2.env_module_types }
    | Types.Sig_class (ident, _, _) -> { env avec env_classes = (rel_name ident, qualify ident) :: env.env_classes }
    | Types.Sig_class_type (ident, _, _) -> { env avec env_class_types = (rel_name ident, qualify ident) :: env.env_class_types }
  dans
  List.fold_left f env signat

soit add_exception env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec env_exceptions = (simple_name, full_name) :: env.env_exceptions }

soit add_type env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec env_types = (simple_name, full_name) :: env.env_types }

soit add_value env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec env_values = (simple_name, full_name) :: env.env_values }

soit add_module env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec env_modules = (simple_name, full_name) :: env.env_modules }

soit add_module_type env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec env_module_types = (simple_name, full_name) :: env.env_module_types }

soit add_class env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec
    env_classes = (simple_name, full_name) :: env.env_classes ;
    (* we also add a type 'cause the class name may appear as a type *)
    env_types = (simple_name, full_name) :: env.env_types
  }

soit add_class_type env full_name =
  soit simple_name = Name.simple full_name dans
  { env avec
    env_class_types = (simple_name, full_name) :: env.env_class_types ;
    (* we also add a type 'cause the class type name may appear as a type *)
    env_types = (simple_name, full_name) :: env.env_types
  }

soit full_module_name env n =
  essaie List.assoc n env.env_modules
  avec Not_found ->
    print_DEBUG ("Module "^n^" not found with env=");
    List.iter (fonc (sn, fn) -> print_DEBUG ("("^sn^", "^fn^")")) env.env_modules;
    n

soit full_module_type_name env n =
  essaie List.assoc n env.env_module_types
  avec Not_found ->
    print_DEBUG ("Module "^n^" not found with env=");
    List.iter (fonc (sn, fn) -> print_DEBUG ("("^sn^", "^fn^")")) env.env_modules;
    n

soit full_module_or_module_type_name env n =
  essaie List.assoc n env.env_modules
  avec Not_found -> full_module_type_name env n

soit full_type_name env n =
  essaie
    soit full = List.assoc n env.env_types dans
(**    print_string ("type "^n^" is "^full);
    print_newline ();*)
    full
  avec Not_found ->
(**    print_string ("type "^n^" not found");
    print_newline ();*)
    n

soit full_value_name env n =
  essaie List.assoc n env.env_values
  avec Not_found -> n

soit full_exception_name env n =
  essaie List.assoc n env.env_exceptions
  avec Not_found ->
    print_DEBUG ("Exception "^n^" not found with env=");
    List.iter (fonc (sn, fn) -> print_DEBUG ("("^sn^", "^fn^")")) env.env_exceptions;
    n

soit full_class_name env n =
  essaie List.assoc n env.env_classes
  avec Not_found ->
    print_DEBUG ("Class "^n^" not found with env=");
    List.iter (fonc (sn, fn) -> print_DEBUG ("("^sn^", "^fn^")")) env.env_classes;
    n

soit full_class_type_name env n =
  essaie List.assoc n env.env_class_types
  avec Not_found ->
    print_DEBUG ("Class type "^n^" not found with env=");
    List.iter (fonc (sn, fn) -> print_DEBUG ("("^sn^", "^fn^")")) env.env_class_types;
    n

soit full_class_or_class_type_name env n =
  essaie List.assoc n env.env_classes
  avec Not_found -> full_class_type_name env n

soit print_env_types env =
  List.iter (fonc (s1,s2) -> Printf.printf "%s = %s\n" s1 s2) env.env_types

soit subst_type env t =
(*
  print_string "Odoc_env.subst_type\n";
  print_env_types env ;
  print_newline ();
*)
  Printtyp.mark_loops t;
  soit deja_vu = ref [] dans
  soit rec iter t =
    si List.memq t !deja_vu alors () sinon début
      deja_vu := t :: !deja_vu;
      Btype.iter_type_expr iter t;
      filtre t.Types.desc avec
      | Types.Tconstr (p, [ty], a) quand Path.same p Predef.path_option ->
          ()
      | Types.Tconstr (p, l, a) ->
          soit new_p =
            Odoc_name.to_path (full_type_name env (Odoc_name.from_path p)) dans
          t.Types.desc <- Types.Tconstr (new_p, l, a)
      | Types.Tpackage (p, n, l) ->
          soit new_p =
            Odoc_name.to_path (full_module_type_name env (Odoc_name.from_path p)) dans
          t.Types.desc <- Types.Tpackage (new_p, n, l)
      | Types.Tobject (_, ({contents=Some(p,tyl)} tel r)) ->
          soit new_p =
            Odoc_name.to_path (full_type_name env (Odoc_name.from_path p)) dans
          r := Some (new_p, tyl)
      | Types.Tvariant ({Types.row_name=Some(p, tyl)} tel row) ->
          soit new_p =
            Odoc_name.to_path (full_type_name env (Odoc_name.from_path p)) dans
          t.Types.desc <-
            Types.Tvariant {row avec Types.row_name=Some(new_p, tyl)}
      | _ ->
          ()
    fin
  dans
  iter t;
  t


soit subst_module_type env t =
  soit rec iter t =
    filtre t avec
      Types.Mty_ident p ->
        soit new_p = Odoc_name.to_path (full_module_type_name env (Odoc_name.from_path p)) dans
        Types.Mty_ident new_p
    | Types.Mty_alias _
    | Types.Mty_signature _ ->
        t
    | Types.Mty_functor (id, mt1, mt2) ->
        Types.Mty_functor (id, Misc.may_map iter mt1, iter mt2)
  dans
  iter t

soit subst_class_type env t =
  soit rec iter t =
    filtre t avec
      Types.Cty_constr (p,texp_list,ct) ->
        soit new_p = Odoc_name.to_path (full_type_name env (Odoc_name.from_path p)) dans
        soit new_texp_list = List.map (subst_type env) texp_list dans
        soit new_ct = iter ct dans
        Types.Cty_constr (new_p, new_texp_list, new_ct)
    | Types.Cty_signature cs ->
        (* on ne s'occupe pas des vals et methods *)
        t
    | Types.Cty_arrow (l, texp, ct) ->
        soit new_texp = subst_type env texp dans
        soit new_ct = iter ct dans
        Types.Cty_arrow (l, new_texp, new_ct)
  dans
  iter t
