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

(** The functions to get a string from different kinds of elements (types, modules, ...). *)

module Name = Odoc_name

soit string_of_variance t (co,cn) =
  si t.Odoc_type.ty_kind = Odoc_type.Type_abstract &&
    t.Odoc_type.ty_manifest = None
  alors
    filtre (co, cn) avec
      (vrai, faux) -> "+"
    | (faux, vrai) -> "-"
    | _ -> ""
  sinon
    ""
soit rec is_arrow_type t =
  filtre t.Types.desc avec
    Types.Tarrow _ -> vrai
  | Types.Tlink t2 | Types.Tsubst t2 -> is_arrow_type t2
  | Types.Ttuple _
  | Types.Tconstr _
  | Types.Tvar _ | Types.Tunivar _ | Types.Tobject _ | Types.Tpoly _
  | Types.Tfield _ | Types.Tnil | Types.Tvariant _ | Types.Tpackage _ -> faux

soit raw_string_of_type_list sep type_list =
  soit buf = Buffer.create 256 dans
  soit fmt = Format.formatter_of_buffer buf dans
  soit rec need_parent t =
    filtre t.Types.desc avec
      Types.Tarrow _ | Types.Ttuple _ -> vrai
    | Types.Tlink t2 | Types.Tsubst t2 -> need_parent t2
    | Types.Tconstr _ ->
        faux
    | Types.Tvar _ | Types.Tunivar _ | Types.Tobject _ | Types.Tpoly _
    | Types.Tfield _ | Types.Tnil | Types.Tvariant _ | Types.Tpackage _ -> faux
  dans
  soit print_one_type variance t =
    Printtyp.mark_loops t;
    si need_parent t alors
      (
       Format.fprintf fmt "(%s" variance;
       Printtyp.type_scheme_max ~b_reset_names: faux fmt t;
       Format.fprintf fmt ")"
      )
    sinon
      (
       Format.fprintf fmt "%s" variance;
       Printtyp.type_scheme_max ~b_reset_names: faux fmt t
      )
  dans
  début filtre type_list avec
    [] -> ()
  | [(variance, ty)] -> print_one_type variance ty
  | (variance, ty) :: tyl ->
      Format.fprintf fmt "@[<hov 2>";
      print_one_type variance ty;
      List.iter
        (fonc (variance, t) ->
          Format.fprintf fmt "@,%s" sep;
          print_one_type variance t
        )
        tyl;
      Format.fprintf fmt "@]"
  fin;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

soit string_of_type_list ?par sep type_list =
  soit par =
    filtre par avec
    | Some b -> b
    | None ->
        filtre type_list avec
          [] | [_] -> faux
        | _ -> vrai
  dans
  Printf.sprintf "%s%s%s"
    (si par alors "(" sinon "")
    (raw_string_of_type_list sep (List.map (fonc t -> ("", t)) type_list))
    (si par alors ")" sinon "")

soit string_of_type_param_list t =
  soit par =
    filtre t.Odoc_type.ty_parameters avec
      [] | [_] -> faux
    | _ -> vrai
  dans
  Printf.sprintf "%s%s%s"
    (si par alors "(" sinon "")
    (raw_string_of_type_list ", "
       (List.map
          (fonc (typ, co, cn) -> (string_of_variance t (co, cn), typ))
          t.Odoc_type.ty_parameters
       )
    )
    (si par alors ")" sinon "")

soit string_of_class_type_param_list l =
  soit par =
    filtre l avec
      [] | [_] -> faux
    | _ -> vrai
  dans
  Printf.sprintf "%s%s%s"
    (si par alors "[" sinon "")
    (raw_string_of_type_list ", "
       (List.map
          (fonc typ -> ("", typ))
          l
       )
    )
    (si par alors "]" sinon "")

soit string_of_class_params c =
  soit b = Buffer.create 256 dans
  soit rec iter = fonction
      Types.Cty_arrow (label, t, ctype) ->
        soit parent = is_arrow_type t dans
        Printf.bprintf b "%s%s%s%s -> "
          (
           filtre label avec
             "" -> ""
           | s -> s^":"
          )
          (si parent alors "(" sinon "")
          (Odoc_print.string_of_type_expr
             (si Odoc_misc.is_optional label alors
               Odoc_misc.remove_option t
             sinon
               t
             )
          )
          (si parent alors ")" sinon "");
        iter ctype
    | Types.Cty_signature _
    | Types.Cty_constr _ -> ()
  dans
  iter c.Odoc_class.cl_type;
  Buffer.contents b

soit bool_of_private = fonction
  | Asttypes.Private -> vrai
  | _ -> faux

soit string_of_type t =
  soit module M = Odoc_type dans
  "type "^
  (String.concat ""
     (List.map
        (fonc (p, co, cn) ->
          (string_of_variance t (co, cn))^
          (Odoc_print.string_of_type_expr p)^" "
        )
        t.M.ty_parameters
     )
  )^
  soit priv = bool_of_private (t.M.ty_private) dans
  (Name.simple t.M.ty_name)^" "^
  (filtre t.M.ty_manifest avec
    None -> ""
  | Some typ ->
     "= " ^ (si priv alors "private " sinon "" ) ^
       (Odoc_print.string_of_type_expr typ)^" "
  )^
  (filtre t.M.ty_kind avec
    M.Type_abstract ->
      ""
  | M.Type_variant l ->
      "="^(si priv alors " private" sinon "")^"\n"^
      (String.concat ""
         (List.map
            (fonc cons ->
              "  | "^cons.M.vc_name^
              (filtre cons.M.vc_args,cons.M.vc_ret avec
              | [], None -> ""
              | l, None ->
                  " of " ^
                  (String.concat " * "
                     (List.map
                        (fonc t -> "("^Odoc_print.string_of_type_expr t^")") l))
              | [], Some r -> " : " ^ Odoc_print.string_of_type_expr r
              | l, Some r ->
                  " : " ^
                  (String.concat " * "
                     (List.map
                        (fonc t -> "("^Odoc_print.string_of_type_expr t^")") l))
                  ^ " -> " ^ Odoc_print.string_of_type_expr r
              )^
              (filtre cons.M.vc_text avec
                None ->
                  ""
              | Some t ->
                  "(* "^(Odoc_misc.string_of_info t)^" *)"
              )^"\n"
            )
            l
         )
      )
  | M.Type_record l ->
      "= "^(si priv alors "private " sinon "")^"{\n"^
      (String.concat ""
         (List.map
            (fonc record ->
              "   "^(si record.M.rf_mutable alors "mutable " sinon "")^
              record.M.rf_name^" : "^
              (Odoc_print.string_of_type_expr record.M.rf_type)^";"^
              (filtre record.M.rf_text avec
                None ->
                  ""
              | Some t ->
                  "(* "^(Odoc_misc.string_of_info t)^" *)"
              )^"\n"
            )
            l
         )
      )^
      "}\n"
  )^
  (filtre t.M.ty_info avec
    None -> ""
  | Some info -> Odoc_misc.string_of_info info)

soit string_of_exception e =
  soit module M = Odoc_exception dans
  "exception "^(Name.simple e.M.ex_name)^
  (filtre e.M.ex_args avec
    [] -> ""
  | _ ->" : "^
      (String.concat " -> "
         (List.map (fonc t -> "("^(Odoc_print.string_of_type_expr t)^")") e.M.ex_args)
      )
  )^
  (filtre e.M.ex_alias avec
    None -> ""
  | Some ea ->
      " = "^
      (filtre ea.M.ea_ex avec
        None -> ea.M.ea_name
      | Some e2 -> e2.M.ex_name
      )
  )^"\n"^
  (filtre e.M.ex_info avec
    None -> ""
  | Some i -> Odoc_misc.string_of_info i)

soit string_of_value v =
  soit module M = Odoc_value dans
  "val "^(Name.simple v.M.val_name)^" : "^
  (Odoc_print.string_of_type_expr v.M.val_type)^"\n"^
  (filtre v.M.val_info avec
    None -> ""
  | Some i -> Odoc_misc.string_of_info i)

soit string_of_attribute a =
  soit module M = Odoc_value dans
  "val "^
  (si a.M.att_virtual alors "virtual " sinon "")^
  (si a.M.att_mutable alors Odoc_messages.mutab^" " sinon "")^
  (Name.simple a.M.att_value.M.val_name)^" : "^
  (Odoc_print.string_of_type_expr a.M.att_value.M.val_type)^"\n"^
  (filtre a.M.att_value.M.val_info avec
    None -> ""
  | Some i -> Odoc_misc.string_of_info i)

soit string_of_method m =
  soit module M = Odoc_value dans
  "method "^
  (si m.M.met_private alors Odoc_messages.privat^" " sinon "")^
  (Name.simple m.M.met_value.M.val_name)^" : "^
  (Odoc_print.string_of_type_expr m.M.met_value.M.val_type)^"\n"^
  (filtre m.M.met_value.M.val_info avec
    None -> ""
  | Some i -> Odoc_misc.string_of_info i)
