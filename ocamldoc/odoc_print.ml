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

ouvre Format

soit new_fmt () =
  soit buf = Buffer.create 512 dans
  soit fmt = formatter_of_buffer buf dans
  soit flush () =
    pp_print_flush fmt ();
    soit s = Buffer.contents buf dans
    Buffer.reset buf ;
    s
  dans
  (fmt, flush)

soit (type_fmt, flush_type_fmt) = new_fmt ()
soit _ =
  soit (out, flush, outnewline, outspace) =
    pp_get_all_formatter_output_functions type_fmt ()
  dans
  pp_set_all_formatter_output_functions type_fmt
    ~out ~flush
    ~newline: (fonc () -> out "\n  " 0 3)
    ~spaces: outspace

soit (modtype_fmt, flush_modtype_fmt) = new_fmt ()




soit string_of_type_expr t =
  Printtyp.mark_loops t;
  Printtyp.type_scheme_max ~b_reset_names: faux type_fmt t;
  flush_type_fmt ()

exception Use_code de string

(** Return the given module type where methods and vals have been removed
   from the signatures. Used when we don't want to print a too long module type.
   @param code when the code is given, we raise the [Use_code] exception is we
   encouter a signature, to that the calling function can use the code rather
   than the "emptied" type.
*)
soit simpl_module_type ?code t =
  soit rec iter t =
    filtre t avec
      Types.Mty_ident p -> t
    | Types.Mty_alias p -> t
    | Types.Mty_signature _ ->
        (
         filtre code avec
           None -> Types.Mty_signature []
         | Some s -> raise (Use_code s)
        )
    | Types.Mty_functor (id, mt1, mt2) ->
        Types.Mty_functor (id, Misc.may_map iter mt1, iter mt2)
  dans
  iter t

soit string_of_module_type ?code ?(complete=faux) t =
  essaie
    soit t2 = si complete alors t sinon simpl_module_type ?code t dans
    Printtyp.modtype modtype_fmt t2;
    flush_modtype_fmt ()
  avec
    Use_code s -> s

(** Return the given class type where methods and vals have been removed
   from the signatures. Used when we don't want to print a too long class type.*)
soit simpl_class_type t =
  soit rec iter t =
    filtre t avec
      Types.Cty_constr (p,texp_list,ct) -> t
    | Types.Cty_signature cs ->
        (* on vire les vals et methods pour ne pas qu'elles soient imprimees
           quand on affichera le type *)
        soit tnil = { Types.desc = Types.Tnil ; Types.level = 0; Types.id = 0 } dans
        Types.Cty_signature { Types.csig_self = { cs.Types.csig_self avec
                                                  Types.desc = Types.Tobject (tnil, ref None) };
                              csig_vars = Types.Vars.empty ;
                              csig_concr = Types.Concr.empty ;
                              csig_inher = []
                             }
    | Types.Cty_arrow (l, texp, ct) ->
        soit new_ct = iter ct dans
        Types.Cty_arrow (l, texp, new_ct)
  dans
  iter t

soit string_of_class_type ?(complete=faux) t =
  soit t2 = si complete alors t sinon simpl_class_type t dans
  (* A VOIR : ma propre version de Printtyp.class_type pour ne pas faire reset_names *)
  Printtyp.class_type modtype_fmt t2;
  flush_modtype_fmt ()
