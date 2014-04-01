(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(* Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt*)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* To print values *)

ouvre Misc
ouvre Format
ouvre Longident
ouvre Path
ouvre Types
ouvre Outcometree

module type OBJ =
  sig
    type t
    val obj : t -> 'a
    val is_block : t -> bool
    val tag : t -> int
    val size : t -> int
    val field : t -> int -> t
  fin

module type EVALPATH =
  sig
    type valu
    val eval_path: Env.t -> Path.t -> valu
    exception Error
    val same_value: valu -> valu -> bool
  fin

module type S =
  sig
    type t
    val install_printer :
          Path.t -> Types.type_expr -> (formatter -> t -> unit) -> unit
    val remove_printer : Path.t -> unit
    val outval_of_untyped_exception : t -> Outcometree.out_value
    val outval_of_value :
          int -> int ->
          (int -> t -> Types.type_expr -> Outcometree.out_value option) ->
          Env.t -> t -> type_expr -> Outcometree.out_value
  fin

module Make(O : OBJ)(EVP : EVALPATH avec type valu = O.t) = struct

    type t = O.t

    (* Given an exception value, we cannot recover its type,
       hence we cannot print its arguments in general.
       Here, we do a feeble attempt to print
       integer, string and float arguments... *)
    soit outval_of_untyped_exception_args obj start_offset =
      si O.size obj > start_offset alors début
        soit list = ref [] dans
        pour i = start_offset à O.size obj - 1 faire
          soit arg = O.field obj i dans
          si not (O.is_block arg) alors
            list := Oval_int (O.obj arg : int) :: !list
               (* Note: this could be a char or a constant constructor... *)
          sinon si O.tag arg = Obj.string_tag alors
            list :=
              Oval_string (String.escaped (O.obj arg : string)) :: !list
          sinon si O.tag arg = Obj.double_tag alors
            list := Oval_float (O.obj arg : float) :: !list
          sinon
            list := Oval_constr (Oide_ident "_", []) :: !list
        fait;
        List.rev !list
      fin
      sinon []

    soit outval_of_untyped_exception bucket =
      si O.tag bucket <> 0 alors
        Oval_constr (Oide_ident (O.obj (O.field bucket 0) : string), [])
      sinon
      soit name = (O.obj(O.field(O.field bucket 0) 0) : string) dans
      soit args =
        si (name = "Match_failure"
            || name = "Assert_failure"
            || name = "Undefined_recursive_module")
        && O.size bucket = 2
        && O.tag(O.field bucket 1) = 0
        alors outval_of_untyped_exception_args (O.field bucket 1) 0
        sinon outval_of_untyped_exception_args bucket 1 dans
      Oval_constr (Oide_ident name, args)

    (* The user-defined printers. Also used for some builtin types. *)

    soit printers = ref ([
      Pident(Ident.create "print_int"), Predef.type_int,
        (fonc x -> Oval_int (O.obj x : int));
      Pident(Ident.create "print_float"), Predef.type_float,
        (fonc x -> Oval_float (O.obj x : float));
      Pident(Ident.create "print_char"), Predef.type_char,
        (fonc x -> Oval_char (O.obj x : char));
      Pident(Ident.create "print_string"), Predef.type_string,
        (fonc x -> Oval_string (O.obj x : string));
      Pident(Ident.create "print_int32"), Predef.type_int32,
        (fonc x -> Oval_int32 (O.obj x : int32));
      Pident(Ident.create "print_nativeint"), Predef.type_nativeint,
        (fonc x -> Oval_nativeint (O.obj x : nativeint));
      Pident(Ident.create "print_int64"), Predef.type_int64,
        (fonc x -> Oval_int64 (O.obj x : int64))
    ] : (Path.t * type_expr * (O.t -> Outcometree.out_value)) list)

    soit install_printer path ty fn =
      soit print_val ppf obj =
        essaie fn ppf obj avec
        | exn ->
           fprintf ppf "<printer %a raised an exception>" Printtyp.path path dans
      soit printer obj = Oval_printer (fonc ppf -> print_val ppf obj) dans
      printers := (path, ty, printer) :: !printers

    soit remove_printer path =
      soit rec remove = fonction
      | [] -> raise Not_found
      | (p, ty, fn tel printer) :: rem ->
          si Path.same p path alors rem sinon printer :: remove rem dans
      printers := remove !printers

    soit find_printer env ty =
      soit rec find = fonction
      | [] -> raise Not_found
      | (name, sch, printer) :: remainder ->
          si Ctype.moregeneral env faux sch ty
          alors printer
          sinon find remainder
      dans find !printers

    (* Print a constructor or label, giving it the same prefix as the type
       it comes from. Attempt to omit the prefix if the type comes from
       a module that has been opened. *)

    soit tree_of_qualified lookup_fun env ty_path name =
      filtre ty_path avec
      | Pident id ->
          Oide_ident name
      | Pdot(p, s, pos) ->
          si essaie
               filtre (lookup_fun (Lident name) env).desc avec
               | Tconstr(ty_path', _, _) -> Path.same ty_path ty_path'
               | _ -> faux
             avec Not_found -> faux
          alors Oide_ident name
          sinon Oide_dot (Printtyp.tree_of_path p, name)
      | Papply(p1, p2) ->
          Printtyp.tree_of_path ty_path

    soit tree_of_constr =
      tree_of_qualified
        (fonc lid env -> (Env.lookup_constructor lid env).cstr_res)

    et tree_of_label =
      tree_of_qualified (fonc lid env -> (Env.lookup_label lid env).lbl_res)

    (* An abstract type *)

    soit abstract_type =
      Ctype.newty (Tconstr (Pident (Ident.create "abstract"), [], ref Mnil))

    (* The main printing function *)

    soit outval_of_value max_steps max_depth check_depth env obj ty =

      soit printer_steps = ref max_steps dans

      soit rec tree_of_val depth obj ty =
        decr printer_steps;
        si !printer_steps < 0 || depth < 0 alors Oval_ellipsis
        sinon début
        essaie
          find_printer env ty obj
        avec Not_found ->
          filtre (Ctype.repr ty).desc avec
          | Tvar _ | Tunivar _ ->
              Oval_stuff "<poly>"
          | Tarrow(_, ty1, ty2, _) ->
              Oval_stuff "<fun>"
          | Ttuple(ty_list) ->
              Oval_tuple (tree_of_val_list 0 depth obj ty_list)
          | Tconstr(path, [], _) quand Path.same path Predef.path_exn ->
              tree_of_exception depth obj
          | Tconstr(path, [ty_arg], _)
            quand Path.same path Predef.path_list ->
              si O.is_block obj alors
                filtre check_depth depth obj ty avec
                  Some x -> x
                | None ->
                    soit rec tree_of_conses tree_list obj =
                      si !printer_steps < 0 || depth < 0 alors
                        Oval_ellipsis :: tree_list
                      sinon si O.is_block obj alors
                        soit tree =
                          tree_of_val (depth - 1) (O.field obj 0) ty_arg dans
                        soit next_obj = O.field obj 1 dans
                        tree_of_conses (tree :: tree_list) next_obj
                      sinon tree_list
                    dans
                    Oval_list (List.rev (tree_of_conses [] obj))
              sinon
                Oval_list []
          | Tconstr(path, [ty_arg], _)
            quand Path.same path Predef.path_array ->
              soit length = O.size obj dans
              si length > 0 alors
                filtre check_depth depth obj ty avec
                  Some x -> x
                | None ->
                    soit rec tree_of_items tree_list i =
                      si !printer_steps < 0 || depth < 0 alors
                        Oval_ellipsis :: tree_list
                      sinon si i < length alors
                        soit tree =
                          tree_of_val (depth - 1) (O.field obj i) ty_arg dans
                        tree_of_items (tree :: tree_list) (i + 1)
                      sinon tree_list
                    dans
                    Oval_array (List.rev (tree_of_items [] 0))
              sinon
                Oval_array []
          | Tconstr (path, [ty_arg], _)
            quand Path.same path Predef.path_lazy_t ->
              si Lazy.lazy_is_val (O.obj obj)
              alors soit v = tree_of_val depth (Lazy.force (O.obj obj)) ty_arg dans
                   Oval_constr (Oide_ident "lazy", [v])
              sinon Oval_stuff "<lazy>"
          | Tconstr(path, ty_list, _) ->
              début essaie
                soit decl = Env.find_type path env dans
                filtre decl avec
                | {type_kind = Type_abstract; type_manifest = None} ->
                    Oval_stuff "<abstr>"
                | {type_kind = Type_abstract; type_manifest = Some body} ->
                    tree_of_val depth obj
                      (essaie Ctype.apply env decl.type_params body ty_list avec
                         Ctype.Cannot_apply -> abstract_type)
                | {type_kind = Type_variant constr_list} ->
                    soit tag =
                      si O.is_block obj
                      alors Cstr_block(O.tag obj)
                      sinon Cstr_constant(O.obj obj) dans
                    soit {cd_id;cd_args;cd_res} =
                      Datarepr.find_constr_by_tag tag constr_list dans
                    soit type_params =
                      filtre cd_res avec
                        Some t ->
                          début filtre (Ctype.repr t).desc avec
                            Tconstr (_,params,_) ->
                              params
                          | _ -> affirme faux fin
                      | None -> decl.type_params
                    dans
                    soit ty_args =
                      List.map
                        (fonction ty ->
                           essaie Ctype.apply env type_params ty ty_list avec
                             Ctype.Cannot_apply -> abstract_type)
                        cd_args dans
                    tree_of_constr_with_args (tree_of_constr env path)
                                 (Ident.name cd_id) 0 depth obj ty_args
                | {type_kind = Type_record(lbl_list, rep)} ->
                    début filtre check_depth depth obj ty avec
                      Some x -> x
                    | None ->
                        soit rec tree_of_fields pos = fonction
                          | [] -> []
                          | {ld_id; ld_type} :: remainder ->
                              soit ty_arg =
                                essaie
                                  Ctype.apply env decl.type_params ld_type
                                    ty_list
                                avec
                                  Ctype.Cannot_apply -> abstract_type dans
                              soit name = Ident.name ld_id dans
                              (* PR#5722: print full module path only
                                 for first record field *)
                              soit lid =
                                si pos = 0 alors tree_of_label env path name
                                sinon Oide_ident name
                              et v =
                                tree_of_val (depth - 1) (O.field obj pos)
                                  ty_arg
                              dans
                              (lid, v) :: tree_of_fields (pos + 1) remainder
                        dans
                        Oval_record (tree_of_fields 0 lbl_list)
                    fin
              avec
                Not_found ->                (* raised by Env.find_type *)
                  Oval_stuff "<abstr>"
              | Datarepr.Constr_not_found -> (* raised by find_constr_by_tag *)
                  Oval_stuff "<unknown constructor>"
              fin
          | Tvariant row ->
              soit row = Btype.row_repr row dans
              si O.is_block obj alors
                soit tag : int = O.obj (O.field obj 0) dans
                soit rec find = fonction
                  | (l, f) :: fields ->
                      si Btype.hash_variant l = tag alors
                        filtre Btype.row_field_repr f avec
                        | Rpresent(Some ty) | Reither(_,[ty],_,_) ->
                            soit args =
                              tree_of_val (depth - 1) (O.field obj 1) ty dans
                            Oval_variant (l, Some args)
                        | _ -> find fields
                      sinon find fields
                  | [] -> Oval_stuff "<variant>" dans
                find row.row_fields
              sinon
                soit tag : int = O.obj obj dans
                soit rec find = fonction
                  | (l, _) :: fields ->
                      si Btype.hash_variant l = tag alors
                        Oval_variant (l, None)
                      sinon find fields
                  | [] -> Oval_stuff "<variant>" dans
                find row.row_fields
          | Tobject (_, _) ->
              Oval_stuff "<obj>"
          | Tsubst ty ->
              tree_of_val (depth - 1) obj ty
          | Tfield(_, _, _, _) | Tnil | Tlink _ ->
              fatal_error "Printval.outval_of_value"
          | Tpoly (ty, _) ->
              tree_of_val (depth - 1) obj ty
          | Tpackage _ ->
              Oval_stuff "<module>"
        fin

      et tree_of_val_list start depth obj ty_list =
        soit rec tree_list i = fonction
          | [] -> []
          | ty :: ty_list ->
              soit tree = tree_of_val (depth - 1) (O.field obj i) ty dans
              tree :: tree_list (i + 1) ty_list dans
      tree_list start ty_list

      et tree_of_constr_with_args
             tree_of_cstr cstr_name start depth obj ty_args =
        soit lid = tree_of_cstr cstr_name dans
        soit args = tree_of_val_list start depth obj ty_args dans
        Oval_constr (lid, args)

    et tree_of_exception depth bucket =
      soit slot =
        si O.tag bucket <> 0 alors bucket
        sinon O.field bucket 0
      dans
      soit name = (O.obj(O.field slot 0) : string) dans
      soit lid = Longident.parse name dans
      essaie
        (* Attempt to recover the constructor description for the exn
           from its name *)
        soit cstr = Env.lookup_constructor lid env dans
        soit path =
          filtre cstr.cstr_tag avec
            Cstr_exception (p, _) -> p | _ -> raise Not_found dans
        (* Make sure this is the right exception and not an homonym,
           by evaluating the exception found and comparing with the
           identifier contained in the exception bucket *)
        si not (EVP.same_value slot (EVP.eval_path env path))
        alors raise Not_found;
        tree_of_constr_with_args
           (fonc x -> Oide_ident x) name 1 depth bucket cstr.cstr_args
      avec Not_found | EVP.Error ->
        filtre check_depth depth bucket ty avec
          Some x -> x
        | None -> outval_of_untyped_exception bucket

    dans tree_of_val max_depth obj ty

fin
