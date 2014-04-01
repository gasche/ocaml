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

(* Printing functions *)

ouvre Misc
ouvre Ctype
ouvre Format
ouvre Longident
ouvre Path
ouvre Asttypes
ouvre Types
ouvre Btype
ouvre Outcometree

(* Print a long identifier *)

soit rec longident ppf = fonction
  | Lident s -> pp_print_string ppf s
  | Ldot(p, s) -> fprintf ppf "%a.%s" longident p s
  | Lapply(p1, p2) -> fprintf ppf "%a(%a)" longident p1 longident p2

(* Print an identifier *)

soit unique_names = ref Ident.empty

soit ident_name id =
  essaie Ident.find_same id !unique_names avec Not_found -> Ident.name id

soit add_unique id =
  essaie ignore (Ident.find_same id !unique_names)
  avec Not_found ->
    unique_names := Ident.add id (Ident.unique_toplevel_name id) !unique_names

soit ident ppf id = pp_print_string ppf (ident_name id)

(* Print a path *)

soit ident_pervasive = Ident.create_persistent "Pervasives"

soit rec tree_of_path = fonction
  | Pident id ->
      Oide_ident (ident_name id)
  | Pdot(Pident id, s, pos) quand Ident.same id ident_pervasive ->
      Oide_ident s
  | Pdot(p, s, pos) ->
      Oide_dot (tree_of_path p, s)
  | Papply(p1, p2) ->
      Oide_apply (tree_of_path p1, tree_of_path p2)

soit rec path ppf = fonction
  | Pident id ->
      ident ppf id
  | Pdot(Pident id, s, pos) quand Ident.same id ident_pervasive ->
      pp_print_string ppf s
  | Pdot(p, s, pos) ->
      path ppf p;
      pp_print_char ppf '.';
      pp_print_string ppf s
  | Papply(p1, p2) ->
      fprintf ppf "%a(%a)" path p1 path p2

soit rec string_of_out_ident = fonction
  | Oide_ident s -> s
  | Oide_dot (id, s) -> String.concat "." [string_of_out_ident id; s]
  | Oide_apply (id1, id2) ->
      String.concat ""
        [string_of_out_ident id1; "("; string_of_out_ident id2; ")"]

soit string_of_path p = string_of_out_ident (tree_of_path p)

(* Print a recursive annotation *)

soit tree_of_rec = fonction
  | Trec_not -> Orec_not
  | Trec_first -> Orec_first
  | Trec_next -> Orec_next

(* Print a raw type expression, with sharing *)

soit raw_list pr ppf = fonction
    [] -> fprintf ppf "[]"
  | a :: l ->
      fprintf ppf "@[<1>[%a%t]@]" pr a
        (fonc ppf -> List.iter (fonc x -> fprintf ppf ";@,%a" pr x) l)

soit rec safe_kind_repr v = fonction
    Fvar {contents=Some k}  ->
      si List.memq k v alors "Fvar loop" sinon
      safe_kind_repr (k::v) k
  | Fvar _ -> "Fvar None"
  | Fpresent -> "Fpresent"
  | Fabsent -> "Fabsent"

soit rec safe_commu_repr v = fonction
    Cok -> "Cok"
  | Cunknown -> "Cunknown"
  | Clink r ->
      si List.memq r v alors "Clink loop" sinon
      safe_commu_repr (r::v) !r

soit rec safe_repr v = fonction
    {desc = Tlink t} quand not (List.memq t v) ->
      safe_repr (t::v) t
  | t -> t

soit rec list_of_memo = fonction
    Mnil -> []
  | Mcons (priv, p, t1, t2, rem) -> p :: list_of_memo rem
  | Mlink rem -> list_of_memo !rem

soit print_name ppf = fonction
    None -> fprintf ppf "None"
  | Some name -> fprintf ppf "\"%s\"" name

soit visited = ref []
soit rec raw_type ppf ty =
  soit ty = safe_repr [] ty dans
  si List.memq ty !visited alors fprintf ppf "{id=%d}" ty.id sinon début
    visited := ty :: !visited;
    fprintf ppf "@[<1>{id=%d;level=%d;desc=@,%a}@]" ty.id ty.level
      raw_type_desc ty.desc
  fin
et raw_type_list tl = raw_list raw_type tl
et raw_type_desc ppf = fonction
    Tvar name -> fprintf ppf "Tvar %a" print_name name
  | Tarrow(l,t1,t2,c) ->
      fprintf ppf "@[<hov1>Tarrow(%s,@,%a,@,%a,@,%s)@]"
        l raw_type t1 raw_type t2
        (safe_commu_repr [] c)
  | Ttuple tl ->
      fprintf ppf "@[<1>Ttuple@,%a@]" raw_type_list tl
  | Tconstr (p, tl, abbrev) ->
      fprintf ppf "@[<hov1>Tconstr(@,%a,@,%a,@,%a)@]" path p
        raw_type_list tl
        (raw_list path) (list_of_memo !abbrev)
  | Tobject (t, nm) ->
      fprintf ppf "@[<hov1>Tobject(@,%a,@,@[<1>ref%t@])@]" raw_type t
        (fonc ppf ->
          filtre !nm avec None -> fprintf ppf " None"
          | Some(p,tl) ->
              fprintf ppf "(Some(@,%a,@,%a))" path p raw_type_list tl)
  | Tfield (f, k, t1, t2) ->
      fprintf ppf "@[<hov1>Tfield(@,%s,@,%s,@,%a,@;<0 -1>%a)@]" f
        (safe_kind_repr [] k)
        raw_type t1 raw_type t2
  | Tnil -> fprintf ppf "Tnil"
  | Tlink t -> fprintf ppf "@[<1>Tlink@,%a@]" raw_type t
  | Tsubst t -> fprintf ppf "@[<1>Tsubst@,%a@]" raw_type t
  | Tunivar name -> fprintf ppf "Tunivar %a" print_name name
  | Tpoly (t, tl) ->
      fprintf ppf "@[<hov1>Tpoly(@,%a,@,%a)@]"
        raw_type t
        raw_type_list tl
  | Tvariant row ->
      fprintf ppf
        "@[<hov1>{@[%s@,%a;@]@ @[%s@,%a;@]@ %s%b;@ %s%b;@ @[<1>%s%t@]}@]"
        "row_fields="
        (raw_list (fonc ppf (l, f) ->
          fprintf ppf "@[%s,@ %a@]" l raw_field f))
        row.row_fields
        "row_more=" raw_type row.row_more
        "row_closed=" row.row_closed
        "row_fixed=" row.row_fixed
        "row_name="
        (fonc ppf ->
          filtre row.row_name avec None -> fprintf ppf "None"
          | Some(p,tl) ->
              fprintf ppf "Some(@,%a,@,%a)" path p raw_type_list tl)
  | Tpackage (p, _, tl) ->
      fprintf ppf "@[<hov1>Tpackage(@,%a@,%a)@]" path p
        raw_type_list tl

et raw_field ppf = fonction
    Rpresent None -> fprintf ppf "Rpresent None"
  | Rpresent (Some t) -> fprintf ppf "@[<1>Rpresent(Some@,%a)@]" raw_type t
  | Reither (c,tl,m,e) ->
      fprintf ppf "@[<hov1>Reither(%b,@,%a,@,%b,@,@[<1>ref%t@])@]" c
        raw_type_list tl m
        (fonc ppf ->
          filtre !e avec None -> fprintf ppf " None"
          | Some f -> fprintf ppf "@,@[<1>(%a)@]" raw_field f)
  | Rabsent -> fprintf ppf "Rabsent"

soit raw_type_expr ppf t =
  visited := [];
  raw_type ppf t;
  visited := []

soit () = Btype.print_raw := raw_type_expr

(* Normalize paths *)

type param_subst = Id | Nth de int | Map de int list

soit compose l1 = fonction
  | Id -> Map l1
  | Map l2 -> Map (List.map (List.nth l1) l2)
  | Nth n  -> Nth (List.nth l1 n)

soit apply_subst s1 tyl =
  filtre s1 avec
    Nth n1 -> [List.nth tyl n1]
  | Map l1 -> List.map (List.nth tyl) l1
  | Id -> tyl

type best_path = Paths de Path.t list | Best de Path.t

soit printing_env = ref Env.empty
soit printing_old = ref Env.empty
soit printing_pers = ref Concr.empty
module Path2 = struct
  inclus Path
  soit rec compare p1 p2 =
    (* must ignore position when comparing paths *)
    filtre (p1, p2) avec
      (Pdot(p1, s1, pos1), Pdot(p2, s2, pos2)) ->
        soit c = compare p1 p2 dans
        si c <> 0 alors c sinon String.compare s1 s2
    | (Papply(fun1, arg1), Papply(fun2, arg2)) ->
        soit c = compare fun1 fun2 dans
        si c <> 0 alors c sinon compare arg1 arg2
    | _ -> Pervasives.compare p1 p2
fin
module PathMap = Map.Make(Path2)
soit printing_map = ref (Lazy.lazy_from_val PathMap.empty)

soit same_type t t' = repr t == repr t'

soit rec index l x =
  filtre l avec
    [] -> raise Not_found
  | a :: l -> si x == a alors 0 sinon 1 + index l x

soit rec uniq = fonction
    [] -> vrai
  | a :: l -> not (List.memq a l) && uniq l

soit rec normalize_type_path ?(cache=faux) env p =
  essaie
    soit (params, ty, _) = Env.find_type_expansion p env dans
    soit params = List.map repr params dans
    filtre repr ty avec
      {desc = Tconstr (p1, tyl, _)} ->
        soit tyl = List.map repr tyl dans
        si List.length params = List.length tyl
        && List.for_all2 (==) params tyl
        alors normalize_type_path ~cache env p1
        sinon si cache || List.length params <= List.length tyl
             || not (uniq tyl) alors (p, Id)
        sinon
          soit l1 = List.map (index params) tyl dans
          soit (p2, s2) = normalize_type_path ~cache env p1 dans
          (p2, compose l1 s2)
    | ty ->
        (p, Nth (index params ty))
  avec
    Not_found -> (p, Id)

soit rec path_size = fonction
    Pident id ->
      (soit s = Ident.name id dans si s <> "" && s.[0] = '_' alors 10 sinon 1),
      -Ident.binding_time id
  | Pdot (p, _, _) ->
      soit (l, b) = path_size p dans (1+l, b)
  | Papply (p1, p2) ->
      soit (l, b) = path_size p1 dans
      (l + fst (path_size p2), b)

soit same_printing_env env =
  soit used_pers = Env.used_persistent () dans
  Env.same_types !printing_old env && Concr.equal !printing_pers used_pers

soit set_printing_env env =
  printing_env := si !Clflags.real_paths alors Env.empty sinon env;
  si !printing_env == Env.empty || same_printing_env env alors () sinon
  début
    (* printf "Reset printing_map@."; *)
    printing_old := env;
    printing_pers := Env.used_persistent ();
    printing_map := paresseux début
      (* printf "Recompute printing_map.@."; *)
      soit map = ref PathMap.empty dans
      Env.iter_types
        (fonc p (p', decl) ->
          soit (p1, s1) = normalize_type_path env p' ~cache:vrai dans
          (* Format.eprintf "%a -> %a = %a@." path p path p' path p1 *)
          si s1 = Id alors
          essaie
            soit r = PathMap.find p1 !map dans
            filtre !r avec
              Paths l -> r := Paths (p :: l)
            | Best _  -> affirme faux
          avec Not_found ->
            map := PathMap.add p1 (ref (Paths [p])) !map)
        env;
      !map
    fin
  fin

soit wrap_printing_env env f =
  set_printing_env env;
  try_finally f (fonc () -> set_printing_env Env.empty)

soit is_unambiguous path env =
  soit l = Env.find_shadowed_types path env dans
  List.exists (Path.same path) l || (* concrete paths are ok *)
  filtre l avec
    [] -> vrai
  | p :: rem ->
      (* allow also coherent paths:  *)
      soit normalize p = fst (normalize_type_path ~cache:vrai env p) dans
      soit p' = normalize p dans
      List.for_all (fonc p -> Path.same (normalize p) p') rem ||
      (* also allow repeatedly defining and opening (for toplevel) *)
      soit id = lid_of_path p dans
      List.for_all (fonc p -> lid_of_path p = id) rem &&
      Path.same p (fst (Env.lookup_type id env))

soit rec get_best_path r =
  filtre !r avec
    Best p' -> p'
  | Paths [] -> raise Not_found
  | Paths l ->
      r := Paths [];
      List.iter
        (fonc p ->
          (* Format.eprintf "evaluating %a@." path p; *)
          filtre !r avec
            Best p' quand path_size p >= path_size p' -> ()
          | _ -> si is_unambiguous p !printing_env alors r := Best p)
              (* else Format.eprintf "%a ignored as ambiguous@." path p *)
        l;
      get_best_path r

soit best_type_path p =
  si !Clflags.real_paths || !printing_env == Env.empty
  alors (p, Id)
  sinon
    soit (p', s) = normalize_type_path !printing_env p dans
    soit p'' =
      essaie get_best_path (PathMap.find  p' (Lazy.force !printing_map))
      avec Not_found -> p'
    dans
    (* Format.eprintf "%a = %a -> %a@." path p path p' path p''; *)
    (p'', s)

(* Print a type expression *)

soit names = ref ([] : (type_expr * string) list)
soit name_counter = ref 0
soit named_vars = ref ([] : string list)

soit reset_names () = names := []; name_counter := 0; named_vars := []
soit add_named_var ty =
  filtre ty.desc avec
    Tvar (Some name) | Tunivar (Some name) ->
      si List.mem name !named_vars alors () sinon
      named_vars := name :: !named_vars
  | _ -> ()

soit rec new_name () =
  soit name =
    si !name_counter < 26
    alors String.make 1 (Char.chr(97 + !name_counter))
    sinon String.make 1 (Char.chr(97 + !name_counter mod 26)) ^
           string_of_int(!name_counter / 26) dans
  incr name_counter;
  si List.mem name !named_vars
  || List.exists (fonc (_, name') -> name = name') !names
  alors new_name ()
  sinon name

soit name_of_type t =
  (* We've already been through repr at this stage, so t is our representative
     of the union-find class. *)
  essaie List.assq t !names avec Not_found ->
    soit name =
      filtre t.desc avec
        Tvar (Some name) | Tunivar (Some name) ->
          (* Some part of the type we've already printed has assigned another
           * unification variable to that name. We want to keep the name, so try
           * adding a number until we find a name that's not taken. *)
          soit current_name = ref name dans
          soit i = ref 0 dans
          pendant_que List.exists (fonc (_, name') -> !current_name = name') !names faire
            current_name := name ^ (string_of_int !i);
            i := !i + 1;
          fait;
          !current_name
      | _ ->
          (* No name available, create a new one *)
          new_name ()
    dans
    (* Exception for type declarations *)
    si name <> "_" alors names := (t, name) :: !names;
    name

soit check_name_of_type t = ignore(name_of_type t)

soit remove_names tyl =
  soit tyl = List.map repr tyl dans
  names := List.filter (fonc (ty,_) -> not (List.memq ty tyl)) !names


soit non_gen_mark sch ty =
  si sch && is_Tvar ty && ty.level <> generic_level alors "_" sinon ""

soit print_name_of_type sch ppf t =
  fprintf ppf "'%s%s" (non_gen_mark sch t) (name_of_type t)

soit visited_objects = ref ([] : type_expr list)
soit aliased = ref ([] : type_expr list)
soit delayed = ref ([] : type_expr list)

soit add_delayed t =
  si not (List.memq t !delayed) alors delayed := t :: !delayed

soit is_aliased ty = List.memq (proxy ty) !aliased
soit add_alias ty =
  soit px = proxy ty dans
  si not (is_aliased px) alors début
    aliased := px :: !aliased;
    add_named_var px
  fin

soit aliasable ty =
  filtre ty.desc avec
    Tvar _ | Tunivar _ | Tpoly _ -> faux
  | Tconstr (p, _, _) ->
      (filtre best_type_path p avec (_, Nth _) -> faux | _ -> vrai)
  | _ -> vrai

soit namable_row row =
  row.row_name <> None &&
  List.for_all
    (fonc (_, f) ->
       filtre row_field_repr f avec
       | Reither(c, l, _, _) ->
           row.row_closed && si c alors l = [] sinon List.length l = 1
       | _ -> vrai)
    row.row_fields

soit rec mark_loops_rec visited ty =
  soit ty = repr ty dans
  soit px = proxy ty dans
  si List.memq px visited && aliasable ty alors add_alias px sinon
    soit visited = px :: visited dans
    filtre ty.desc avec
    | Tvar _ -> add_named_var ty
    | Tarrow(_, ty1, ty2, _) ->
        mark_loops_rec visited ty1; mark_loops_rec visited ty2
    | Ttuple tyl -> List.iter (mark_loops_rec visited) tyl
    | Tconstr(p, tyl, _) ->
        soit (p', s) = best_type_path p dans
        List.iter (mark_loops_rec visited) (apply_subst s tyl)
    | Tpackage (_, _, tyl) ->
        List.iter (mark_loops_rec visited) tyl
    | Tvariant row ->
        si List.memq px !visited_objects alors add_alias px sinon
         début
          soit row = row_repr row dans
          si not (static_row row) alors
            visited_objects := px :: !visited_objects;
          filtre row.row_name avec
          | Some(p, tyl) quand namable_row row ->
              List.iter (mark_loops_rec visited) tyl
          | _ ->
              iter_row (mark_loops_rec visited) row
         fin
    | Tobject (fi, nm) ->
        si List.memq px !visited_objects alors add_alias px sinon
         début
          si opened_object ty alors
            visited_objects := px :: !visited_objects;
          début filtre !nm avec
          | None ->
              soit fields, _ = flatten_fields fi dans
              List.iter
                (fonc (_, kind, ty) ->
                  si field_kind_repr kind = Fpresent alors
                    mark_loops_rec visited ty)
                fields
          | Some (_, l) ->
              List.iter (mark_loops_rec visited) (List.tl l)
          fin
        fin
    | Tfield(_, kind, ty1, ty2) quand field_kind_repr kind = Fpresent ->
        mark_loops_rec visited ty1; mark_loops_rec visited ty2
    | Tfield(_, _, _, ty2) ->
        mark_loops_rec visited ty2
    | Tnil -> ()
    | Tsubst ty -> mark_loops_rec visited ty
    | Tlink _ -> fatal_error "Printtyp.mark_loops_rec (2)"
    | Tpoly (ty, tyl) ->
        List.iter (fonc t -> add_alias t) tyl;
        mark_loops_rec visited ty
    | Tunivar _ -> add_named_var ty

soit mark_loops ty =
  normalize_type Env.empty ty;
  mark_loops_rec [] ty;;

soit reset_loop_marks () =
  visited_objects := []; aliased := []; delayed := []

soit reset () =
  unique_names := Ident.empty; reset_names (); reset_loop_marks ()

soit reset_and_mark_loops ty =
  reset (); mark_loops ty

soit reset_and_mark_loops_list tyl =
  reset (); List.iter mark_loops tyl

(* Disabled in classic mode when printing an unification error *)
soit print_labels = ref vrai
soit print_label ppf l =
  si !print_labels && l <> "" || is_optional l alors fprintf ppf "%s:" l

soit rec tree_of_typexp sch ty =
  soit ty = repr ty dans
  soit px = proxy ty dans
  si List.mem_assq px !names && not (List.memq px !delayed) alors
   soit mark = is_non_gen sch ty dans
   Otyp_var (mark, name_of_type px) sinon

  soit pr_typ () =
    filtre ty.desc avec
    | Tvar _ ->
        Otyp_var (is_non_gen sch ty, name_of_type ty)
    | Tarrow(l, ty1, ty2, _) ->
        soit pr_arrow l ty1 ty2 =
          soit lab =
            si !print_labels && l <> "" || is_optional l alors l sinon ""
          dans
          soit t1 =
            si is_optional l alors
              filtre (repr ty1).desc avec
              | Tconstr(path, [ty], _)
                quand Path.same path Predef.path_option ->
                  tree_of_typexp sch ty
              | _ -> Otyp_stuff "<hidden>"
            sinon tree_of_typexp sch ty1 dans
          Otyp_arrow (lab, t1, tree_of_typexp sch ty2) dans
        pr_arrow l ty1 ty2
    | Ttuple tyl ->
        Otyp_tuple (tree_of_typlist sch tyl)
    | Tconstr(p, tyl, abbrev) ->
        début filtre best_type_path p avec
          (_, Nth n) -> tree_of_typexp sch (List.nth tyl n)
        | (p', s) ->
            soit tyl' = apply_subst s tyl dans
            Otyp_constr (tree_of_path p', tree_of_typlist sch tyl')
        fin
    | Tvariant row ->
        soit row = row_repr row dans
        soit fields =
          si row.row_closed alors
            List.filter (fonc (_, f) -> row_field_repr f <> Rabsent)
              row.row_fields
          sinon row.row_fields dans
        soit present =
          List.filter
            (fonc (_, f) ->
               filtre row_field_repr f avec
               | Rpresent _ -> vrai
               | _ -> faux)
            fields dans
        soit all_present = List.length present = List.length fields dans
        début filtre row.row_name avec
        | Some(p, tyl) quand namable_row row ->
            soit (p', s) = best_type_path p dans
            affirme (s = Id);
            soit id = tree_of_path p' dans
            soit args = tree_of_typlist sch tyl dans
            si row.row_closed && all_present alors
              Otyp_constr (id, args)
            sinon
              soit non_gen = is_non_gen sch px dans
              soit tags =
                si all_present alors None sinon Some (List.map fst present) dans
              Otyp_variant (non_gen, Ovar_name(id, args),
                            row.row_closed, tags)
        | _ ->
            soit non_gen =
              not (row.row_closed && all_present) && is_non_gen sch px dans
            soit fields = List.map (tree_of_row_field sch) fields dans
            soit tags =
              si all_present alors None sinon Some (List.map fst present) dans
            Otyp_variant (non_gen, Ovar_fields fields, row.row_closed, tags)
        fin
    | Tobject (fi, nm) ->
        tree_of_typobject sch fi !nm
    | Tnil | Tfield _ ->
        tree_of_typobject sch ty None
    | Tsubst ty ->
        tree_of_typexp sch ty
    | Tlink _ ->
        fatal_error "Printtyp.tree_of_typexp"
    | Tpoly (ty, []) ->
        tree_of_typexp sch ty
    | Tpoly (ty, tyl) ->
        (*let print_names () =
          List.iter (fun (_, name) -> prerr_string (name ^ " ")) !names;
          prerr_string "; " in *)
        soit tyl = List.map repr tyl dans
        si tyl = [] alors tree_of_typexp sch ty sinon début
          soit old_delayed = !delayed dans
          (* Make the names delayed, so that the real type is
             printed once when used as proxy *)
          List.iter add_delayed tyl;
          soit tl = List.map name_of_type tyl dans
          soit tr = Otyp_poly (tl, tree_of_typexp sch ty) dans
          (* Forget names when we leave scope *)
          remove_names tyl;
          delayed := old_delayed; tr
        fin
    | Tunivar _ ->
        Otyp_var (faux, name_of_type ty)
    | Tpackage (p, n, tyl) ->
        soit n =
          List.map (fonc li -> String.concat "." (Longident.flatten li)) n dans
        Otyp_module (Path.name p, n, tree_of_typlist sch tyl)
  dans
  si List.memq px !delayed alors delayed := List.filter ((!=) px) !delayed;
  si is_aliased px && aliasable ty alors début
    check_name_of_type px;
    Otyp_alias (pr_typ (), name_of_type px) fin
  sinon pr_typ ()

et tree_of_row_field sch (l, f) =
  filtre row_field_repr f avec
  | Rpresent None | Reither(vrai, [], _, _) -> (l, faux, [])
  | Rpresent(Some ty) -> (l, faux, [tree_of_typexp sch ty])
  | Reither(c, tyl, _, _) ->
      si c (* contradiction: un constructeur constant qui a un argument *)
      alors (l, vrai, tree_of_typlist sch tyl)
      sinon (l, faux, tree_of_typlist sch tyl)
  | Rabsent -> (l, faux, [] (* une erreur, en fait *))

et tree_of_typlist sch tyl =
  List.map (tree_of_typexp sch) tyl

et tree_of_typobject sch fi nm =
  début filtre nm avec
  | None ->
      soit pr_fields fi =
        soit (fields, rest) = flatten_fields fi dans
        soit present_fields =
          List.fold_right
            (fonc (n, k, t) l ->
               filtre field_kind_repr k avec
               | Fpresent -> (n, t) :: l
               | _ -> l)
            fields [] dans
        soit sorted_fields =
          List.sort (fonc (n, _) (n', _) -> compare n n') present_fields dans
        tree_of_typfields sch rest sorted_fields dans
      soit (fields, rest) = pr_fields fi dans
      Otyp_object (fields, rest)
  | Some (p, ty :: tyl) ->
      soit non_gen = is_non_gen sch (repr ty) dans
      soit args = tree_of_typlist sch tyl dans
      soit (p', s) = best_type_path p dans
      affirme (s = Id);
      Otyp_class (non_gen, tree_of_path p', args)
  | _ ->
      fatal_error "Printtyp.tree_of_typobject"
  fin

et is_non_gen sch ty =
    sch && is_Tvar ty && ty.level <> generic_level

et tree_of_typfields sch rest = fonction
  | [] ->
      soit rest =
        filtre rest.desc avec
        | Tvar _ | Tunivar _ -> Some (is_non_gen sch rest)
        | Tconstr _ -> Some faux
        | Tnil -> None
        | _ -> fatal_error "typfields (1)"
      dans
      ([], rest)
  | (s, t) :: l ->
      soit field = (s, tree_of_typexp sch t) dans
      soit (fields, rest) = tree_of_typfields sch rest l dans
      (field :: fields, rest)

soit typexp sch prio ppf ty =
  !Oprint.out_type ppf (tree_of_typexp sch ty)

soit type_expr ppf ty = typexp faux 0 ppf ty

et type_sch ppf ty = typexp vrai 0 ppf ty

et type_scheme ppf ty = reset_and_mark_loops ty; typexp vrai 0 ppf ty

(* Maxence *)
soit type_scheme_max ?(b_reset_names=vrai) ppf ty =
  si b_reset_names alors reset_names () ;
  typexp vrai 0 ppf ty
(* Fin Maxence *)

soit tree_of_type_scheme ty = reset_and_mark_loops ty; tree_of_typexp vrai ty

(* Print one type declaration *)

soit tree_of_constraints params =
  List.fold_right
    (fonc ty list ->
       soit ty' = unalias ty dans
       si proxy ty != proxy ty' alors
         soit tr = tree_of_typexp vrai ty dans
         (tr, tree_of_typexp vrai ty') :: list
       sinon list)
    params []

soit filter_params tyl =
  soit params =
    List.fold_left
      (fonc tyl ty ->
        soit ty = repr ty dans
        si List.memq ty tyl alors Btype.newgenty (Tsubst ty) :: tyl
        sinon ty :: tyl)
      [] tyl
  dans List.rev params

soit string_of_mutable = fonction
  | Immutable -> ""
  | Mutable -> "mutable "

soit rec tree_of_type_decl id decl =

  reset();

  soit params = filter_params decl.type_params dans

  début filtre decl.type_manifest avec
  | Some ty ->
      soit vars = free_variables ty dans
      List.iter
        (fonction {desc = Tvar (Some "_")} tel ty ->
            si List.memq ty vars alors ty.desc <- Tvar None
          | _ -> ())
        params
  | None -> ()
  fin;

  List.iter add_alias params;
  List.iter mark_loops params;
  List.iter check_name_of_type (List.map proxy params);
  soit ty_manifest =
    filtre decl.type_manifest avec
    | None -> None
    | Some ty ->
        soit ty =
          (* Special hack to hide variant name *)
          filtre repr ty avec {desc=Tvariant row} ->
            soit row = row_repr row dans
            début filtre row.row_name avec
              Some (Pident id', _) quand Ident.same id id' ->
                newgenty (Tvariant {row avec row_name = None})
            | _ -> ty
            fin
          | _ -> ty
        dans
        mark_loops ty;
        Some ty
  dans
  début filtre decl.type_kind avec
  | Type_abstract -> ()
  | Type_variant cstrs ->
      List.iter
        (fonc c ->
          List.iter mark_loops c.cd_args;
          may mark_loops c.cd_res)
        cstrs
  | Type_record(l, rep) ->
      List.iter (fonc l -> mark_loops l.ld_type) l
  fin;

  soit type_param =
    fonction
    | Otyp_var (_, id) -> id
    | _ -> "?"
  dans
  soit type_defined decl =
    soit abstr =
      filtre decl.type_kind avec
        Type_abstract ->
          decl.type_manifest = None || decl.type_private = Private
      | Type_record _ ->
          decl.type_private = Private
      | Type_variant tll ->
          decl.type_private = Private ||
          List.exists (fonc cd -> cd.cd_res <> None) tll
    dans
    soit vari =
      List.map2
        (fonc ty v ->
          si abstr || not (is_Tvar (repr ty)) alors Variance.get_upper v
          sinon (vrai,vrai))
        decl.type_params decl.type_variance
    dans
    (Ident.name id,
     List.map2 (fonc ty cocn -> type_param (tree_of_typexp faux ty), cocn)
       params vari)
  dans
  soit tree_of_manifest ty1 =
    filtre ty_manifest avec
    | None -> ty1
    | Some ty -> Otyp_manifest (tree_of_typexp faux ty, ty1)
  dans
  soit (name, args) = type_defined decl dans
  soit constraints = tree_of_constraints params dans
  soit ty, priv =
    filtre decl.type_kind avec
    | Type_abstract ->
        début filtre ty_manifest avec
        | None -> (Otyp_abstract, Public)
        | Some ty ->
            tree_of_typexp faux ty, decl.type_private
        fin
    | Type_variant cstrs ->
        tree_of_manifest (Otyp_sum (List.map tree_of_constructor cstrs)),
        decl.type_private
    | Type_record(lbls, rep) ->
        tree_of_manifest (Otyp_record (List.map tree_of_label lbls)),
        decl.type_private
  dans
  (name, args, ty, priv, constraints)

et tree_of_constructor cd =
  soit name = Ident.name cd.cd_id dans
  filtre cd.cd_res avec
  | None -> (name, tree_of_typlist faux cd.cd_args, None)
  | Some res ->
      soit nm = !names dans
      names := [];
      soit ret = tree_of_typexp faux res dans
      soit args = tree_of_typlist faux cd.cd_args dans
      names := nm;
      (name, args, Some ret)


et tree_of_constructor_ret =
  fonction
    | None -> None
    | Some ret_type -> Some (tree_of_typexp faux ret_type)

et tree_of_label l =
  (Ident.name l.ld_id, l.ld_mutable = Mutable, tree_of_typexp faux l.ld_type)

soit tree_of_type_declaration id decl rs =
  Osig_type (tree_of_type_decl id decl, tree_of_rec rs)

soit type_declaration id ppf decl =
  !Oprint.out_sig_item ppf (tree_of_type_declaration id decl Trec_first)

(* Print an exception declaration *)

soit tree_of_exception_declaration id decl =
  reset_and_mark_loops_list decl.exn_args;
  soit tyl = tree_of_typlist faux decl.exn_args dans
  Osig_exception (Ident.name id, tyl)

soit exception_declaration id ppf decl =
  !Oprint.out_sig_item ppf (tree_of_exception_declaration id decl)

(* Print a value declaration *)

soit tree_of_value_description id decl =
  soit id = Ident.name id dans
  soit ty = tree_of_type_scheme decl.val_type dans
  soit prims =
    filtre decl.val_kind avec
    | Val_prim p -> Primitive.description_list p
    | _ -> []
  dans
  Osig_value (id, ty, prims)

soit value_description id ppf decl =
  !Oprint.out_sig_item ppf (tree_of_value_description id decl)

(* Print a class type *)

soit class_var sch ppf l (m, t) =
  fprintf ppf
    "@ @[<2>val %s%s :@ %a@]" (string_of_mutable m) l (typexp sch 0) t

soit method_type (_, kind, ty) =
  filtre field_kind_repr kind, repr ty avec
    Fpresent, {desc=Tpoly(ty, tyl)} -> (ty, tyl)
  | _       , ty                    -> (ty, [])

soit tree_of_metho sch concrete csil (lab, kind, ty) =
  si lab <> dummy_method alors début
    soit kind = field_kind_repr kind dans
    soit priv = kind <> Fpresent dans
    soit virt = not (Concr.mem lab concrete) dans
    soit (ty, tyl) = method_type (lab, kind, ty) dans
    soit tty = tree_of_typexp sch ty dans
    remove_names tyl;
    Ocsg_method (lab, priv, virt, tty) :: csil
  fin
  sinon csil

soit rec prepare_class_type params = fonction
  | Cty_constr (p, tyl, cty) ->
      soit sty = Ctype.self_type cty dans
      si List.memq (proxy sty) !visited_objects
      || not (List.for_all is_Tvar params)
      || List.exists (deep_occur sty) tyl
      alors prepare_class_type params cty
      sinon List.iter mark_loops tyl
  | Cty_signature sign ->
      soit sty = repr sign.csig_self dans
      (* Self may have a name *)
      soit px = proxy sty dans
      si List.memq px !visited_objects alors add_alias sty
      sinon visited_objects := px :: !visited_objects;
      soit (fields, _) =
        Ctype.flatten_fields (Ctype.object_fields sign.csig_self)
      dans
      List.iter (fonc met -> mark_loops (fst (method_type met))) fields;
      Vars.iter (fonc _ (_, _, ty) -> mark_loops ty) sign.csig_vars
  | Cty_arrow (_, ty, cty) ->
      mark_loops ty;
      prepare_class_type params cty

soit rec tree_of_class_type sch params =
  fonction
  | Cty_constr (p', tyl, cty) ->
      soit sty = Ctype.self_type cty dans
      si List.memq (proxy sty) !visited_objects
      || not (List.for_all is_Tvar params)
      alors
        tree_of_class_type sch params cty
      sinon
        Octy_constr (tree_of_path p', tree_of_typlist vrai tyl)
  | Cty_signature sign ->
      soit sty = repr sign.csig_self dans
      soit self_ty =
        si is_aliased sty alors
          Some (Otyp_var (faux, name_of_type (proxy sty)))
        sinon None
      dans
      soit (fields, _) =
        Ctype.flatten_fields (Ctype.object_fields sign.csig_self)
      dans
      soit csil = [] dans
      soit csil =
        List.fold_left
          (fonc csil (ty1, ty2) -> Ocsg_constraint (ty1, ty2) :: csil)
          csil (tree_of_constraints params)
      dans
      soit all_vars =
        Vars.fold (fonc l (m, v, t) all -> (l, m, v, t) :: all) sign.csig_vars []
      dans
      (* Consequence of PR#3607: order of Map.fold has changed! *)
      soit all_vars = List.rev all_vars dans
      soit csil =
        List.fold_left
          (fonc csil (l, m, v, t) ->
            Ocsg_value (l, m = Mutable, v = Virtual, tree_of_typexp sch t)
            :: csil)
          csil all_vars
      dans
      soit csil =
        List.fold_left (tree_of_metho sch sign.csig_concr) csil fields
      dans
      Octy_signature (self_ty, List.rev csil)
  | Cty_arrow (l, ty, cty) ->
      soit lab = si !print_labels && l <> "" || is_optional l alors l sinon "" dans
      soit ty =
       si is_optional l alors
         filtre (repr ty).desc avec
         | Tconstr(path, [ty], _) quand Path.same path Predef.path_option -> ty
         | _ -> newconstr (Path.Pident(Ident.create "<hidden>")) []
       sinon ty dans
      soit tr = tree_of_typexp sch ty dans
      Octy_arrow (lab, tr, tree_of_class_type sch params cty)

soit class_type ppf cty =
  reset ();
  prepare_class_type [] cty;
  !Oprint.out_class_type ppf (tree_of_class_type faux [] cty)

soit tree_of_class_param param variance =
  (filtre tree_of_typexp vrai param avec
    Otyp_var (_, s) -> s
  | _ -> "?"),
  si is_Tvar (repr param) alors (vrai, vrai) sinon variance

soit tree_of_class_params params =
  soit tyl = tree_of_typlist vrai params dans
  List.map (fonction Otyp_var (_, s) -> s | _ -> "?") tyl

soit class_variance =
  List.map Variance.(fonc v -> mem May_pos v, mem May_neg v)

soit tree_of_class_declaration id cl rs =
  soit params = filter_params cl.cty_params dans

  reset ();
  List.iter add_alias params;
  prepare_class_type params cl.cty_type;
  soit sty = Ctype.self_type cl.cty_type dans
  List.iter mark_loops params;

  List.iter check_name_of_type (List.map proxy params);
  si is_aliased sty alors check_name_of_type (proxy sty);

  soit vir_flag = cl.cty_new = None dans
  Osig_class
    (vir_flag, Ident.name id,
     List.map2 tree_of_class_param params (class_variance cl.cty_variance),
     tree_of_class_type vrai params cl.cty_type,
     tree_of_rec rs)

soit class_declaration id ppf cl =
  !Oprint.out_sig_item ppf (tree_of_class_declaration id cl Trec_first)

soit tree_of_cltype_declaration id cl rs =
  soit params = List.map repr cl.clty_params dans

  reset ();
  List.iter add_alias params;
  prepare_class_type params cl.clty_type;
  soit sty = Ctype.self_type cl.clty_type dans
  List.iter mark_loops params;

  List.iter check_name_of_type (List.map proxy params);
  si is_aliased sty alors check_name_of_type (proxy sty);

  soit sign = Ctype.signature_of_class_type cl.clty_type dans

  soit virt =
    soit (fields, _) =
      Ctype.flatten_fields (Ctype.object_fields sign.csig_self) dans
    List.exists
      (fonc (lab, _, ty) ->
         not (lab = dummy_method || Concr.mem lab sign.csig_concr))
      fields
    || Vars.fold (fonc _ (_,vr,_) b -> vr = Virtual || b) sign.csig_vars faux
  dans

  Osig_class_type
    (virt, Ident.name id,
     List.map2 tree_of_class_param params (class_variance cl.clty_variance),
     tree_of_class_type vrai params cl.clty_type,
     tree_of_rec rs)

soit cltype_declaration id ppf cl =
  !Oprint.out_sig_item ppf (tree_of_cltype_declaration id cl Trec_first)

(* Print a module type *)

soit wrap_env fenv ftree arg =
  soit env = !printing_env dans
  set_printing_env (fenv env);
  soit tree = ftree arg dans
  set_printing_env env;
  tree

soit filter_rem_sig item rem =
  filtre item, rem avec
  | Sig_class _, ctydecl :: tydecl1 :: tydecl2 :: rem ->
      ([ctydecl; tydecl1; tydecl2], rem)
  | Sig_class_type _, tydecl1 :: tydecl2 :: rem ->
      ([tydecl1; tydecl2], rem)
  | _ ->
      ([], rem)

soit dummy =
  { type_params = []; type_arity = 0; type_kind = Type_abstract;
    type_private = Public; type_manifest = None; type_variance = [];
    type_newtype_level = None; type_loc = Location.none;
    type_attributes = [];
  }

soit hide_rec_items = fonction
  | Sig_type(id, decl, rs) ::rem
    quand rs <> Trec_next && not !Clflags.real_paths ->
      soit rec get_ids = fonction
          Sig_type (id, _, Trec_next) :: rem ->
            id :: get_ids rem
        | _ -> []
      dans
      soit ids = id :: get_ids rem dans
      set_printing_env
        (List.fold_right
           (fonc id -> Env.add_type ~check:faux (Ident.rename id) dummy)
           ids !printing_env)
  | _ -> ()

soit rec tree_of_modtype = fonction
  | Mty_ident p ->
      Omty_ident (tree_of_path p)
  | Mty_signature sg ->
      Omty_signature (tree_of_signature sg)
  | Mty_functor(param, ty_arg, ty_res) ->
      soit res =
        filtre ty_arg avec None -> tree_of_modtype ty_res
        | Some mty ->
            wrap_env (Env.add_module ~arg:vrai param mty) tree_of_modtype ty_res
      dans
      Omty_functor (Ident.name param, may_map tree_of_modtype ty_arg, res)
  | Mty_alias p ->
      Omty_alias (tree_of_path p)

et tree_of_signature sg =
  wrap_env (fonc env -> env) (tree_of_signature_rec !printing_env) sg

et tree_of_signature_rec env' = fonction
    [] -> []
  | item :: rem ->
      début filtre item avec
        Sig_type (_, _, rs) quand rs <> Trec_next -> ()
      | _ -> set_printing_env env'
      fin;
      soit (sg, rem) = filter_rem_sig item rem dans
      soit trees =
        filtre item avec
        | Sig_value(id, decl) ->
            [tree_of_value_description id decl]
        | Sig_type(id, _, _) quand is_row_name (Ident.name id) ->
            []
        | Sig_type(id, decl, rs) ->
            hide_rec_items (item :: rem);
            [Osig_type(tree_of_type_decl id decl, tree_of_rec rs)]
        | Sig_exception(id, decl) ->
            [tree_of_exception_declaration id decl]
        | Sig_module(id, md, rs) ->
            [Osig_module (Ident.name id, tree_of_modtype md.md_type,
                          tree_of_rec rs)]
        | Sig_modtype(id, decl) ->
            [tree_of_modtype_declaration id decl]
        | Sig_class(id, decl, rs) ->
            [tree_of_class_declaration id decl rs]
        | Sig_class_type(id, decl, rs) ->
            [tree_of_cltype_declaration id decl rs]
      dans
      soit env' = Env.add_signature (item :: sg) env' dans
      trees @ tree_of_signature_rec env' rem

et tree_of_modtype_declaration id decl =
  soit mty =
    filtre decl.mtd_type avec
    | None -> Omty_abstract
    | Some mty -> tree_of_modtype mty
  dans
  Osig_modtype (Ident.name id, mty)

soit tree_of_module id mty rs =
  Osig_module (Ident.name id, tree_of_modtype mty, tree_of_rec rs)

soit modtype ppf mty = !Oprint.out_module_type ppf (tree_of_modtype mty)
soit modtype_declaration id ppf decl =
  !Oprint.out_sig_item ppf (tree_of_modtype_declaration id decl)

(* Print a signature body (used by -i when compiling a .ml) *)

soit print_signature ppf tree =
  fprintf ppf "@[<v>%a@]" !Oprint.out_signature tree

soit signature ppf sg =
  fprintf ppf "%a" print_signature (tree_of_signature sg)

(* Print an unification error *)

soit same_path t t' =
  soit t = repr t et t' = repr t' dans
  t == t' ||
  filtre t.desc, t'.desc avec
    Tconstr(p,tl,_), Tconstr(p',tl',_) ->
      soit (p1, s1) = best_type_path p et (p2, s2)  = best_type_path p' dans
      début filtre s1, s2 avec
        Nth n1, Nth n2 quand n1 = n2 -> vrai
      | (Id | Map _), (Id | Map _) quand Path.same p1 p2 ->
          soit tl = apply_subst s1 tl et tl' = apply_subst s2 tl' dans
          List.length tl = List.length tl' &&
          List.for_all2 same_type tl tl'
      | _ -> faux
      fin
  | _ ->
      faux

soit type_expansion t ppf t' =
  si same_path t t' alors type_expr ppf t sinon
  soit t' = si proxy t == proxy t' alors unalias t' sinon t' dans
  fprintf ppf "@[<2>%a@ =@ %a@]" type_expr t type_expr t'

soit type_path_expansion tp ppf tp' =
  si Path.same tp tp' alors path ppf tp sinon
  fprintf ppf "@[<2>%a@ =@ %a@]" path tp path tp'

soit rec trace fst txt ppf = fonction
  | (t1, t1') :: (t2, t2') :: rem ->
      si not fst alors fprintf ppf "@,";
      fprintf ppf "@[Type@;<1 2>%a@ %s@;<1 2>%a@] %a"
       (type_expansion t1) t1' txt (type_expansion t2) t2'
       (trace faux txt) rem
  | _ -> ()

soit rec filter_trace keep_last = fonction
  | (_, t1') :: (_, t2') :: [] quand is_Tvar t1' || is_Tvar t2' ->
      []
  | (t1, t1') :: (t2, t2') :: rem ->
      soit rem' = filter_trace keep_last rem dans
      si is_constr_row t1' || is_constr_row t2'
      || same_path t1 t1' && same_path t2 t2' && not (keep_last && rem' = [])
      alors rem'
      sinon (t1, t1') :: (t2, t2') :: rem'
  | _ -> []

soit rec type_path_list ppf = fonction
  | [tp, tp'] -> type_path_expansion tp ppf tp'
  | (tp, tp') :: rem ->
      fprintf ppf "%a@;<2 0>%a"
        (type_path_expansion tp) tp'
        type_path_list rem
  | [] -> ()

(* Hide variant name and var, to force printing the expanded type *)
soit hide_variant_name t =
  filtre repr t avec
  | {desc = Tvariant row} tel t quand (row_repr row).row_name <> None ->
      newty2 t.level
        (Tvariant {(row_repr row) avec row_name = None;
                   row_more = newvar2 (row_more row).level})
  | _ -> t

soit prepare_expansion (t, t') =
  soit t' = hide_variant_name t' dans
  mark_loops t;
  si not (same_path t t') alors mark_loops t';
  (t, t')

soit may_prepare_expansion compact (t, t') =
  filtre (repr t').desc avec
    Tvariant _ | Tobject _ quand compact ->
      mark_loops t; (t, t)
  | _ -> prepare_expansion (t, t')

soit print_tags ppf fields =
  filtre fields avec [] -> ()
  | (t, _) :: fields ->
      fprintf ppf "`%s" t;
      List.iter (fonc (t, _) -> fprintf ppf ",@ `%s" t) fields

soit has_explanation unif t3 t4 =
  filtre t3.desc, t4.desc avec
    Tfield _, (Tnil|Tconstr _) | (Tnil|Tconstr _), Tfield _
  | Tnil, Tconstr _ | Tconstr _, Tnil
  | _, Tvar _ | Tvar _, _
  | Tvariant _, Tvariant _ -> vrai
  | Tfield (l,_,_,{desc=Tnil}), Tfield (l',_,_,{desc=Tnil}) -> l = l'
  | _ -> faux

soit rec mismatch unif = fonction
    (_, t) :: (_, t') :: rem ->
      début filtre mismatch unif rem avec
        Some _ tel m -> m
      | None ->
          si has_explanation unif t t' alors Some(t,t') sinon None
      fin
  | [] -> None
  | _ -> affirme faux

soit explanation unif t3 t4 ppf =
  filtre t3.desc, t4.desc avec
  | Ttuple [], Tvar _ | Tvar _, Ttuple [] ->
      fprintf ppf "@,Self type cannot escape its class"
  | Tconstr (p, tl, _), Tvar _
    quand unif && t4.level < Path.binding_time p ->
      fprintf ppf
        "@,@[The type constructor@;<1 2>%a@ would escape its scope@]"
        path p
  | Tvar _, Tconstr (p, tl, _)
    quand unif && t3.level < Path.binding_time p ->
      fprintf ppf
        "@,@[The type constructor@;<1 2>%a@ would escape its scope@]"
        path p
  | Tvar _, Tunivar _ | Tunivar _, Tvar _ ->
      fprintf ppf "@,The universal variable %a would escape its scope"
        type_expr (si is_Tunivar t3 alors t3 sinon t4)
  | Tvar _, _ | _, Tvar _ ->
      soit t, t' = si is_Tvar t3 alors (t3, t4) sinon (t4, t3) dans
      si occur_in Env.empty t t' alors
        fprintf ppf "@,@[<hov>The type variable %a occurs inside@ %a@]"
          type_expr t type_expr t'
      sinon
        fprintf ppf "@,@[<hov>This instance of %a is ambiguous:@ %s@]"
          type_expr t'
          "it would escape the scope of its equation"
  | Tfield (lab, _, _, _), _
  | _, Tfield (lab, _, _, _) quand lab = dummy_method ->
      fprintf ppf
        "@,Self type cannot be unified with a closed object type"
  | Tfield (l,_,_,{desc=Tnil}), Tfield (l',_,_,{desc=Tnil}) quand l = l' ->
      fprintf ppf "@,Types for method %s are incompatible" l
  | (Tnil|Tconstr _), Tfield (l, _, _, _) ->
      fprintf ppf
        "@,@[The first object type has no method %s@]" l
  | Tfield (l, _, _, _), (Tnil|Tconstr _) ->
      fprintf ppf
        "@,@[The second object type has no method %s@]" l
  | Tnil, Tconstr _ | Tconstr _, Tnil ->
      fprintf ppf
        "@,@[The %s object type has an abstract row, it cannot be closed@]"
        (si t4.desc = Tnil alors "first" sinon "second")
  | Tvariant row1, Tvariant row2 ->
      soit row1 = row_repr row1 et row2 = row_repr row2 dans
      début filtre
        row1.row_fields, row1.row_closed, row2.row_fields, row2.row_closed avec
      | [], vrai, [], vrai ->
          fprintf ppf "@,These two variant types have no intersection"
      | [], vrai, fields, _ ->
          fprintf ppf
            "@,@[The first variant type does not allow tag(s)@ @[<hov>%a@]@]"
            print_tags fields
      | fields, _, [], vrai ->
          fprintf ppf
            "@,@[The second variant type does not allow tag(s)@ @[<hov>%a@]@]"
            print_tags fields
      | [l1,_], vrai, [l2,_], vrai quand l1 = l2 ->
          fprintf ppf "@,Types for tag `%s are incompatible" l1
      | _ -> ()
      fin
  | _ -> ()

soit explanation unif mis ppf =
  filtre mis avec
    None -> ()
  | Some (t3, t4) -> explanation unif t3 t4 ppf

soit ident_same_name id1 id2 =
  si Ident.equal id1 id2 && not (Ident.same id1 id2) alors début
    add_unique id1; add_unique id2
  fin

soit rec path_same_name p1 p2 =
  filtre p1, p2 avec
    Pident id1, Pident id2 -> ident_same_name id1 id2
  | Pdot (p1, s1, _), Pdot (p2, s2, _) quand s1 = s2 -> path_same_name p1 p2
  | Papply (p1, p1'), Papply (p2, p2') ->
      path_same_name p1 p2; path_same_name p1' p2'
  | _ -> ()

soit type_same_name t1 t2 =
  filtre (repr t1).desc, (repr t2).desc avec
    Tconstr (p1, _, _), Tconstr (p2, _, _) ->
      path_same_name (fst (best_type_path p1)) (fst (best_type_path p2))
  | _ -> ()

soit rec trace_same_names = fonction
    (t1, t1') :: (t2, t2') :: rem ->
      type_same_name t1 t2; type_same_name t1' t2'; trace_same_names rem
  | _ -> ()

soit unification_error unif tr txt1 ppf txt2 =
  reset ();
  trace_same_names tr;
  soit tr = List.map (fonc (t, t') -> (t, hide_variant_name t')) tr dans
  soit mis = mismatch unif tr dans
  filtre tr avec
  | [] | _ :: [] -> affirme faux
  | t1 :: t2 :: tr ->
    essaie
      soit tr = filter_trace (mis = None) tr dans
      soit t1, t1' = may_prepare_expansion (tr = []) t1
      et t2, t2' = may_prepare_expansion (tr = []) t2 dans
      print_labels := not !Clflags.classic;
      soit tr = List.map prepare_expansion tr dans
      fprintf ppf
        "@[<v>\
          @[%t@;<1 2>%a@ \
            %t@;<1 2>%a\
          @]%a%t\
         @]"
        txt1 (type_expansion t1) t1'
        txt2 (type_expansion t2) t2'
        (trace faux "is not compatible with type") tr
        (explanation unif mis);
      print_labels := vrai
    avec exn ->
      print_labels := vrai;
      raise exn

soit report_unification_error ppf env ?(unif=vrai)
    tr txt1 txt2 =
  wrap_printing_env env (fonc () -> unification_error unif tr txt1 ppf txt2)
;;

soit trace fst keep_last txt ppf tr =
  print_labels := not !Clflags.classic;
  trace_same_names tr;
  essaie filtre tr avec
    t1 :: t2 :: tr' ->
      si fst alors trace fst txt ppf (t1 :: t2 :: filter_trace keep_last tr')
      sinon trace fst txt ppf (filter_trace keep_last tr);
      print_labels := vrai
  | _ -> ()
  avec exn ->
    print_labels := vrai;
    raise exn

soit report_subtyping_error ppf env tr1 txt1 tr2 =
  wrap_printing_env env (fonc () ->
    reset ();
    soit tr1 = List.map prepare_expansion tr1
    et tr2 = List.map prepare_expansion tr2 dans
    fprintf ppf "@[<v>%a" (trace vrai (tr2 = []) txt1) tr1;
    si tr2 = [] alors fprintf ppf "@]" sinon
    soit mis = mismatch vrai tr2 dans
    fprintf ppf "%a%t@]"
      (trace faux (mis = None) "is not compatible with type") tr2
      (explanation vrai mis))

soit report_ambiguous_type_error ppf env (tp0, tp0') tpl txt1 txt2 txt3 =
  wrap_printing_env env (fonc () ->
    reset ();
    List.iter
      (fonc (tp, tp') -> path_same_name tp0 tp; path_same_name tp0' tp')
      tpl;
    filtre tpl avec
      [] -> affirme faux
    | [tp, tp'] ->
        fprintf ppf
          "@[%t@;<1 2>%a@ \
             %t@;<1 2>%a\
           @]"
          txt1 (type_path_expansion tp) tp'
          txt3 (type_path_expansion tp0) tp0'
    | _ ->
        fprintf ppf
          "@[%t@;<1 2>@[<hv>%a@]\
             @ %t@;<1 2>%a\
           @]"
          txt2 type_path_list tpl
          txt3 (type_path_expansion tp0) tp0')
