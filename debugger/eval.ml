(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Misc
ouvre Path
ouvre Instruct
ouvre Types
ouvre Parser_aux

type error =
    Unbound_identifier de Ident.t
  | Not_initialized_yet de Path.t
  | Unbound_long_identifier de Longident.t
  | Unknown_name de int
  | Tuple_index de type_expr * int * int
  | Array_index de int * int
  | List_index de int * int
  | String_index de string * int * int
  | Wrong_item_type de type_expr * int
  | Wrong_label de type_expr * string
  | Not_a_record de type_expr
  | No_result

exception Error de error

soit abstract_type =
  Btype.newgenty (Tconstr (Pident (Ident.create "<abstr>"), [], ref Mnil))

soit rec path event = fonction
    Pident id ->
      si Ident.global id alors
        essaie
          Debugcom.Remote_value.global (Symtable.get_global_position id)
        avec Symtable.Error _ -> raise(Error(Unbound_identifier id))
      sinon
        début filtre event avec
          Some ev ->
            début essaie
              soit pos = Ident.find_same id ev.ev_compenv.ce_stack dans
              Debugcom.Remote_value.local (ev.ev_stacksize - pos)
            avec Not_found ->
            essaie
              soit pos = Ident.find_same id ev.ev_compenv.ce_heap dans
              Debugcom.Remote_value.from_environment pos
            avec Not_found ->
              raise(Error(Unbound_identifier id))
            fin
        | None ->
            raise(Error(Unbound_identifier id))
        fin
  | Pdot(root, fieldname, pos) ->
      soit v = path event root dans
      si not (Debugcom.Remote_value.is_block v) alors
        raise(Error(Not_initialized_yet root));
      Debugcom.Remote_value.field v pos
  | Papply(p1, p2) ->
      fatal_error "Eval.path: Papply"

soit rec expression event env = fonction
    E_ident lid ->
      début essaie
        soit (p, valdesc) = Env.lookup_value lid env dans
        (début filtre valdesc.val_kind avec
           Val_ivar (_, cl_num) ->
             soit (p0, _) =
               Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
             dans
             soit v = path event p0 dans
             soit i = path event p dans
             Debugcom.Remote_value.field v (Debugcom.Remote_value.obj i)
         | _ ->
             path event p
         fin,
         Ctype.correct_levels valdesc.val_type)
      avec Not_found ->
        raise(Error(Unbound_long_identifier lid))
      fin
  | E_result ->
      début filtre event avec
        Some {ev_kind = Event_after ty; ev_typsubst = subst}
        quand !Frames.current_frame = 0 ->
          (Debugcom.Remote_value.accu(), Subst.type_expr subst ty)
      | _ ->
          raise(Error(No_result))
      fin
  | E_name n ->
      début essaie
        Printval.find_named_value n
      avec Not_found ->
        raise(Error(Unknown_name n))
      fin
  | E_item(arg, n) ->
      soit (v, ty) = expression event env arg dans
      début filtre (Ctype.repr(Ctype.expand_head_opt env ty)).desc avec
        Ttuple ty_list ->
          si n < 1 || n > List.length ty_list
          alors raise(Error(Tuple_index(ty, List.length ty_list, n)))
          sinon (Debugcom.Remote_value.field v (n-1), List.nth ty_list (n-1))
      | Tconstr(path, [ty_arg], _) quand Path.same path Predef.path_array ->
          soit size = Debugcom.Remote_value.size v dans
          si n >= size
          alors raise(Error(Array_index(size, n)))
          sinon (Debugcom.Remote_value.field v n, ty_arg)
      | Tconstr(path, [ty_arg], _) quand Path.same path Predef.path_list ->
          soit rec nth pos v =
            si not (Debugcom.Remote_value.is_block v) alors
              raise(Error(List_index(pos, n)))
            sinon si pos = n alors
              (Debugcom.Remote_value.field v 0, ty_arg)
            sinon
              nth (pos + 1) (Debugcom.Remote_value.field v 1)
          dans nth 0 v
      | Tconstr(path, [], _) quand Path.same path Predef.path_string ->
          soit s = (Debugcom.Remote_value.obj v : string) dans
          si n >= String.length s
          alors raise(Error(String_index(s, String.length s, n)))
          sinon (Debugcom.Remote_value.of_int(Char.code s.[n]),
                Predef.type_char)
      | _ ->
          raise(Error(Wrong_item_type(ty, n)))
      fin
  | E_field(arg, lbl) ->
      soit (v, ty) = expression event env arg dans
      début filtre (Ctype.repr(Ctype.expand_head_opt env ty)).desc avec
        Tconstr(path, args, _) ->
          soit tydesc = Env.find_type path env dans
          début filtre tydesc.type_kind avec
            Type_record(lbl_list, repr) ->
              soit (pos, ty_res) =
                find_label lbl env ty path tydesc 0 lbl_list dans
              (Debugcom.Remote_value.field v pos, ty_res)
          | _ -> raise(Error(Not_a_record ty))
          fin
      | _ -> raise(Error(Not_a_record ty))
      fin

et find_label lbl env ty path tydesc pos = fonction
    [] ->
      raise(Error(Wrong_label(ty, lbl)))
  | {ld_id; ld_type} :: rem ->
      si Ident.name ld_id = lbl alors début
        soit ty_res =
          Btype.newgenty(Tconstr(path, tydesc.type_params, ref Mnil))
        dans
        (pos,
         essaie Ctype.apply env [ty_res] ld_type [ty] avec Ctype.Cannot_apply ->
           abstract_type)
      fin sinon
        find_label lbl env ty path tydesc (pos + 1) rem

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Unbound_identifier id ->
      fprintf ppf "@[Unbound identifier %s@]@." (Ident.name id)
  | Not_initialized_yet path ->
      fprintf ppf
        "@[The module path %a is not yet initialized.@ \
           Please run program forward@ \
           until its initialization code is executed.@]@."
      Printtyp.path path
  | Unbound_long_identifier lid ->
      fprintf ppf "@[Unbound identifier %a@]@." Printtyp.longident lid
  | Unknown_name n ->
      fprintf ppf "@[Unknown value name $%i@]@." n
  | Tuple_index(ty, len, pos) ->
      Printtyp.reset_and_mark_loops ty;
      fprintf ppf
        "@[Cannot extract field number %i from a %i-tuple of type@ %a@]@."
        pos len Printtyp.type_expr ty
  | Array_index(len, pos) ->
      fprintf ppf
        "@[Cannot extract element number %i from an array of length %i@]@."
        pos len
  | List_index(len, pos) ->
      fprintf ppf
        "@[Cannot extract element number %i from a list of length %i@]@."
        pos len
  | String_index(s, len, pos) ->
      fprintf ppf
        "@[Cannot extract character number %i@ \
           from the following string of length %i:@ %S@]@."
        pos len s
  | Wrong_item_type(ty, pos) ->
      fprintf ppf
        "@[Cannot extract item number %i from a value of type@ %a@]@."
        pos Printtyp.type_expr ty
  | Wrong_label(ty, lbl) ->
      fprintf ppf
        "@[The record type@ %a@ has no label named %s@]@."
        Printtyp.type_expr ty lbl
  | Not_a_record ty ->
      fprintf ppf
        "@[The type@ %a@ is not a record type@]@." Printtyp.type_expr ty
  | No_result ->
      fprintf ppf "@[No result available at current program event@]@."
