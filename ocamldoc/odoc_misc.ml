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

soit no_blanks s =
  soit len = String.length s dans
  soit buf = Buffer.create len dans
  pour i = 0 à len - 1 faire
    filtre s.[i] avec
      ' ' | '\n' | '\t' | '\r' -> ()
    | c -> Buffer.add_char buf c
  fait;
  Buffer.contents buf

soit input_file_as_string nom =
  soit chanin = open_in_bin nom dans
  soit len = 1024 dans
  soit s = String.create len dans
  soit buf = Buffer.create len dans
  soit rec iter () =
    essaie
      soit n = input chanin s 0 len dans
      si n = 0 alors
        ()
      sinon
        (
         Buffer.add_substring buf s 0 n;
         iter ()
        )
    avec
      End_of_file -> ()
  dans
  iter ();
  close_in chanin;
  Buffer.contents buf

soit split_string s chars =
  soit len = String.length s dans
  soit rec iter acc pos =
    si pos >= len alors
      filtre acc avec
        "" -> []
      | _ -> [acc]
    sinon
      si List.mem s.[pos] chars alors
        filtre acc avec
          "" -> iter "" (pos + 1)
        | _ -> acc :: (iter "" (pos + 1))
      sinon
        iter (Printf.sprintf "%s%c" acc s.[pos]) (pos + 1)
  dans
  iter "" 0

soit split_with_blanks s = split_string s [' ' ; '\n' ; '\r' ; '\t' ]

soit list_concat sep =
  soit rec iter = fonction
      [] -> []
    | [h] -> [h]
    | h :: q -> h :: sep :: q
  dans
  iter

soit rec string_of_longident li =
  filtre li avec
  | Longident.Lident s -> s
  | Longident.Ldot(li, s) -> string_of_longident li ^ "." ^ s
  | Longident.Lapply(l1, l2) ->
      string_of_longident l1 ^ "(" ^ string_of_longident l2 ^ ")"

soit get_fields type_expr =
  soit (fields, _) = Ctype.flatten_fields (Ctype.object_fields type_expr) dans
  List.fold_left
    (fonc acc -> fonc (label, field_kind, typ) ->
      filtre field_kind avec
        Types.Fabsent ->
          acc
      | _ ->
          si label = "*dummy method*" alors
            acc
          sinon
            acc @ [label, typ]
    )
    []
    fields

soit rec string_of_text t =
  soit rec iter t_ele =
    filtre t_ele avec
      | Odoc_types.Raw s
      | Odoc_types.Code s
      | Odoc_types.CodePre s
      | Odoc_types.Verbatim s -> s
      | Odoc_types.Bold t
      | Odoc_types.Italic t
      | Odoc_types.Center t
      | Odoc_types.Left t
      | Odoc_types.Right t
      | Odoc_types.Emphasize t -> string_of_text t
      | Odoc_types.List l ->
          (String.concat ""
             (List.map (fonc t -> "\n- "^(string_of_text t)) l))^
          "\n"
      | Odoc_types.Enum l ->
          soit rec f n = fonction
              [] -> "\n"
            | t :: q ->
                "\n"^(string_of_int n)^". "^(string_of_text t)^
                (f (n + 1) q)
          dans
          f 1 l
      | Odoc_types.Newline -> "\n"
      | Odoc_types.Block t -> "\t"^(string_of_text t)^"\n"
      | Odoc_types.Title (_, _, t) -> "\n"^(string_of_text t)^"\n"
      | Odoc_types.Latex s -> "{% "^s^" %}"
      | Odoc_types.Link (s, t) ->
          "["^s^"]"^(string_of_text t)
      | Odoc_types.Ref (name, _, Some text) ->
          Printf.sprintf "[%s]" (string_of_text text)
      | Odoc_types.Ref (name, _, None) ->
          iter (Odoc_types.Code name)
      | Odoc_types.Superscript t ->
          "^{"^(string_of_text t)^"}"
      | Odoc_types.Subscript t ->
          "^{"^(string_of_text t)^"}"
      | Odoc_types.Module_list l ->
          string_of_text
            (list_concat (Odoc_types.Raw ", ")
               (List.map (fonc s -> Odoc_types.Code s) l)
            )
      | Odoc_types.Index_list ->
          ""
      | Odoc_types.Custom (_, t) -> string_of_text t
      | Odoc_types.Target _ -> ""
  dans
  String.concat "" (List.map iter t)

soit string_of_author_list l =
  filtre l avec
    [] ->
      ""
  | _ ->
      "* "^Odoc_messages.authors^":\n"^
      (String.concat ", " l)^
      "\n"

soit string_of_version_opt v_opt =
  filtre v_opt avec
    None -> ""
  | Some v -> Odoc_messages.version^": "^v^"\n"

soit string_of_since_opt s_opt =
  filtre s_opt avec
    None -> ""
  | Some s -> Odoc_messages.since^" "^s^"\n"

soit string_of_raised_exceptions l =
  filtre l avec
    [] -> ""
  | (s, t) :: [] -> Odoc_messages.raises^" "^s^" "^(string_of_text t)^"\n"
  | _ ->
      Odoc_messages.raises^"\n"^
      (String.concat ""
         (List.map
            (fonc (ex, desc) -> "- "^ex^" "^(string_of_text desc)^"\n")
            l
         )
      )^"\n"

soit string_of_see (see_ref, t) =
  soit t_ref =
    filtre see_ref avec
      Odoc_types.See_url s -> [ Odoc_types.Link (s, t) ]
    | Odoc_types.See_file s -> (Odoc_types.Code s) :: (Odoc_types.Raw " ") :: t
    | Odoc_types.See_doc s -> (Odoc_types.Italic [Odoc_types.Raw s]) :: (Odoc_types.Raw " ") :: t
  dans
  string_of_text t_ref

soit string_of_sees l =
  filtre l avec
    [] -> ""
  | see :: [] -> Odoc_messages.see_also^" "^(string_of_see see)^" \n"
  | _ ->
      Odoc_messages.see_also^"\n"^
      (String.concat ""
         (List.map
            (fonc see -> "- "^(string_of_see see)^"\n")
            l
         )
      )^"\n"

soit string_of_return_opt return_opt =
  filtre return_opt avec
    None -> ""
  | Some s -> Odoc_messages.returns^" "^(string_of_text s)^"\n"

soit string_of_info i =
  soit module M = Odoc_types dans
  (filtre i.M.i_deprecated avec
    None -> ""
  | Some d -> Odoc_messages.deprecated^"! "^(string_of_text d)^"\n")^
  (filtre i.M.i_desc avec
    None -> ""
  | Some d quand d = [Odoc_types.Raw ""] -> ""
  | Some d -> (string_of_text d)^"\n"
  )^
  (string_of_author_list i.M.i_authors)^
  (string_of_version_opt i.M.i_version)^
  (string_of_since_opt i.M.i_since)^
  (string_of_raised_exceptions i.M.i_raised_exceptions)^
  (string_of_return_opt i.M.i_return_value)

soit apply_opt f v_opt =
  filtre v_opt avec
    None -> None
  | Some v -> Some (f v)

soit string_of_date ?(hour=vrai) d =
  soit add_0 s = si String.length s < 2 alors "0"^s sinon s dans
  soit t = Unix.localtime d dans
  (string_of_int (t.Unix.tm_year + 1900))^"-"^
  (add_0 (string_of_int (t.Unix.tm_mon + 1)))^"-"^
  (add_0 (string_of_int t.Unix.tm_mday))^
  (
   si hour alors
     " "^
     (add_0 (string_of_int t.Unix.tm_hour))^":"^
     (add_0 (string_of_int t.Unix.tm_min))
   sinon
     ""
  )


soit rec text_list_concat sep l =
  filtre l avec
    [] -> []
  | [t] -> t
  | t :: q ->
      t @ (sep :: (text_list_concat sep q))

soit rec text_no_title_no_list t =
  soit rec iter t_ele =
    filtre t_ele avec
    | Odoc_types.Title (_,_,t) -> text_no_title_no_list t
    | Odoc_types.List l
    | Odoc_types.Enum l ->
        (Odoc_types.Raw " ") ::
        (text_list_concat
           (Odoc_types.Raw ", ")
           (List.map text_no_title_no_list l))
    | Odoc_types.Raw _
    | Odoc_types.Code _
    | Odoc_types.CodePre _
    | Odoc_types.Verbatim _
    | Odoc_types.Ref _
    | Odoc_types.Target _ -> [t_ele]
    | Odoc_types.Newline ->  [Odoc_types.Newline]
    | Odoc_types.Block t -> [Odoc_types.Block (text_no_title_no_list t)]
    | Odoc_types.Bold t -> [Odoc_types.Bold (text_no_title_no_list t)]
    | Odoc_types.Italic t -> [Odoc_types.Italic (text_no_title_no_list t)]
    | Odoc_types.Center t -> [Odoc_types.Center (text_no_title_no_list t)]
    | Odoc_types.Left t -> [Odoc_types.Left (text_no_title_no_list t)]
    | Odoc_types.Right t -> [Odoc_types.Right (text_no_title_no_list t)]
    | Odoc_types.Emphasize t -> [Odoc_types.Emphasize (text_no_title_no_list t)]
    | Odoc_types.Latex s -> [Odoc_types.Latex s]
    | Odoc_types.Link (s, t) -> [Odoc_types.Link (s, (text_no_title_no_list t))]
    | Odoc_types.Superscript t -> [Odoc_types.Superscript (text_no_title_no_list t)]
    | Odoc_types.Subscript t -> [Odoc_types.Subscript (text_no_title_no_list t)]
    | Odoc_types.Module_list l ->
        list_concat (Odoc_types.Raw ", ")
          (List.map
             (fonc s -> Odoc_types.Ref (s, Some Odoc_types.RK_module, None))
             l
          )
    | Odoc_types.Index_list -> []
    | Odoc_types.Custom (s,t) -> [Odoc_types.Custom (s, text_no_title_no_list t)]
  dans
  List.flatten (List.map iter t)

soit get_titles_in_text t =
  soit l = ref [] dans
  soit rec iter_ele ele =
    filtre ele avec
    | Odoc_types.Title (n,lopt,t) -> l := (n,lopt,t) :: !l
    | Odoc_types.List l
    | Odoc_types.Enum l -> List.iter iter_text l
    | Odoc_types.Raw _
    | Odoc_types.Code _
    | Odoc_types.CodePre _
    | Odoc_types.Verbatim _
    | Odoc_types.Ref _ -> ()
    | Odoc_types.Newline ->  ()
    | Odoc_types.Block t
    | Odoc_types.Bold t
    | Odoc_types.Italic t
    | Odoc_types.Center t
    | Odoc_types.Left t
    | Odoc_types.Right t
    | Odoc_types.Emphasize t -> iter_text t
    | Odoc_types.Latex s -> ()
    | Odoc_types.Link (_, t)
    | Odoc_types.Superscript t
    | Odoc_types.Subscript t  -> iter_text t
    | Odoc_types.Module_list _ -> ()
    | Odoc_types.Index_list -> ()
    | Odoc_types.Custom (_, t) -> iter_text t
    | Odoc_types.Target _ -> ()
  et iter_text te =
    List.iter iter_ele te
  dans
  iter_text t;
  List.rev !l

soit text_concat (sep : Odoc_types.text) l =
  soit rec iter = fonction
      [] -> []
    | [last] -> last
    | h :: q -> h @ sep @ (iter q)
  dans
  iter l

(*********************************************************)
soit rec get_before_dot s =
  essaie
    soit len = String.length s dans
    soit n = String.index s '.' dans
    si n + 1 >= len alors
      (* le point est le dernier caractere *)
      (vrai, s, "")
    sinon
      filtre s.[n+1] avec
        ' ' | '\n' | '\r' | '\t' ->
          (vrai, String.sub s 0 (n+1),
           String.sub s (n+1) (len - n - 1))
      | _ ->
          soit b, s2, s_after = get_before_dot (String.sub s (n + 1) (len - n - 1)) dans
          (b, (String.sub s 0 (n+1))^s2, s_after)
  avec
    Not_found -> (faux, s, "")

soit rec first_sentence_text t =
  filtre t avec
    [] -> (faux, [], [])
  | ele :: q ->
      soit (stop, ele2, ele3_opt) = first_sentence_text_ele ele dans
      si stop alors
        (stop, [ele2],
         filtre ele3_opt avec None -> q | Some e -> e :: q)
      sinon
        soit (stop2, q2, rest) = first_sentence_text q dans
        (stop2, ele2 :: q2, rest)


et first_sentence_text_ele text_ele =
  filtre text_ele avec
  | Odoc_types.Raw s ->
      soit b, s2, s_after = get_before_dot s dans
      (b, Odoc_types.Raw s2, Some (Odoc_types.Raw s_after))
  | Odoc_types.Code _
  | Odoc_types.CodePre _
  | Odoc_types.Verbatim _ -> (faux, text_ele, None)
  | Odoc_types.Bold t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Bold t2, Some (Odoc_types.Bold t3))
  | Odoc_types.Italic t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Italic t2, Some (Odoc_types.Italic t3))
  | Odoc_types.Center t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Center t2, Some (Odoc_types.Center t3))
  | Odoc_types.Left t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Left t2, Some (Odoc_types.Left t3))
  | Odoc_types.Right t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Right t2, Some (Odoc_types.Right t3))
  | Odoc_types.Emphasize t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Emphasize t2, Some (Odoc_types.Emphasize t3))
  | Odoc_types.Block t ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b, Odoc_types.Block t2, Some (Odoc_types.Block t3))
  | Odoc_types.Title (n, l_opt, t) ->
      soit (b, t2, t3) = first_sentence_text t dans
      (b,
       Odoc_types.Title (n, l_opt, t2),
       Some (Odoc_types.Title (n, l_opt, t3)))
  | Odoc_types.Newline ->
      (vrai, Odoc_types.Raw "", Some Odoc_types.Newline)
  | Odoc_types.List _
  | Odoc_types.Enum _
  | Odoc_types.Latex _
  | Odoc_types.Link _
  | Odoc_types.Ref _
  | Odoc_types.Superscript _
  | Odoc_types.Subscript _
  | Odoc_types.Module_list _
  | Odoc_types.Index_list -> (faux, text_ele, None)
  | Odoc_types.Custom _
  | Odoc_types.Target _ -> (faux, text_ele, None)


soit first_sentence_of_text t =
  soit (_,t2,_) = first_sentence_text t dans
  t2

soit first_sentence_and_rest_of_text t =
  soit (_,t1, t2) = first_sentence_text t dans
  (t1, t2)

soit remove_ending_newline s =
  soit len = String.length s dans
  si len <= 0 alors
    s
  sinon
    filtre s.[len-1] avec
      '\n' -> String.sub s 0 (len-1)
    | _ -> s

soit search_string_backward ~pat =
  soit lenp = String.length pat dans
  soit rec iter s =
    soit len = String.length s dans
    filtre compare len lenp avec
      -1 -> raise Not_found
    | 0 -> si pat = s alors 0 sinon raise Not_found
    | _ ->
        soit pos = len - lenp dans
        soit s2 = String.sub s pos lenp dans
        si s2 = pat alors
          pos
        sinon
          iter (String.sub s 0 pos)
  dans
  fonc ~s -> iter s



(*********************************************************)

soit create_index_lists elements string_of_ele =
  soit rec f current acc0 acc1 acc2 = fonction
      [] -> (acc0 :: acc1) @ [acc2]
    | ele :: q ->
        soit s = string_of_ele ele dans
        filtre s avec
          "" -> f current acc0 acc1 (acc2 @ [ele]) q
        | _ ->
            soit first = Char.uppercase s.[0] dans
            filtre first avec
              'A' .. 'Z' ->
                si current = first alors
                  f current acc0 acc1 (acc2 @ [ele]) q
                sinon
                  f first acc0 (acc1 @ [acc2]) [ele] q
            | _ ->
                f current (acc0 @ [ele]) acc1 acc2 q
  dans
  f '_' [] [] [] elements


(*** for labels *)

soit is_optional = Btype.is_optional
soit label_name = Btype.label_name

soit remove_option typ =
  soit rec iter t =
    filtre t avec
    | Types.Tconstr(path, [ty], _) quand Path.same path Predef.path_option -> ty.Types.desc
    | Types.Tconstr _
    | Types.Tvar _
    | Types.Tunivar _
    | Types.Tpoly _
    | Types.Tarrow _
    | Types.Ttuple _
    | Types.Tobject _
    | Types.Tfield _
    | Types.Tnil
    | Types.Tvariant _
    | Types.Tpackage _ -> t
    | Types.Tlink t2
    | Types.Tsubst t2 -> iter t2.Types.desc
  dans
  { typ avec Types.desc = iter typ.Types.desc }
