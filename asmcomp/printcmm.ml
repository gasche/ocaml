(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Pretty-printing of C-- code *)

ouvre Format
ouvre Cmm

soit machtype_component ppf = fonction
  | Addr -> fprintf ppf "addr"
  | Int -> fprintf ppf "int"
  | Float -> fprintf ppf "float"

soit machtype ppf mty =
  filtre Array.length mty avec
  | 0 -> fprintf ppf "unit"
  | n -> machtype_component ppf mty.(0);
         pour i = 1 à n-1 faire
           fprintf ppf "*%a" machtype_component mty.(i)
         fait

soit comparison = fonction
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

soit chunk = fonction
  | Byte_unsigned -> "unsigned int8"
  | Byte_signed -> "signed int8"
  | Sixteen_unsigned -> "unsigned int16"
  | Sixteen_signed -> "signed int16"
  | Thirtytwo_unsigned -> "unsigned int32"
  | Thirtytwo_signed -> "signed int32"
  | Word -> ""
  | Single -> "float32"
  | Double -> "float64"
  | Double_u -> "float64u"

soit operation = fonction
  | Capply(ty, d) -> "app" ^ Debuginfo.to_string d
  | Cextcall(lbl, ty, alloc, d) ->
      Printf.sprintf "extcall \"%s\"%s" lbl (Debuginfo.to_string d)
  | Cload Word -> "load"
  | Cload c -> Printf.sprintf "load %s" (chunk c)
  | Calloc -> "alloc"
  | Cstore Word -> "store"
  | Cstore c -> Printf.sprintf "store %s" (chunk c)
  | Caddi -> "+"
  | Csubi -> "-"
  | Cmuli -> "*"
  | Cmulhi -> "*h"
  | Cdivi -> "/"
  | Cmodi -> "mod"
  | Cand -> "and"
  | Cor -> "or"
  | Cxor -> "xor"
  | Clsl -> "<<"
  | Clsr -> ">>u"
  | Casr -> ">>s"
  | Ccmpi c -> comparison c
  | Cadda -> "+a"
  | Csuba -> "-a"
  | Ccmpa c -> Printf.sprintf "%sa" (comparison c)
  | Cnegf -> "~f"
  | Cabsf -> "absf"
  | Caddf -> "+f"
  | Csubf -> "-f"
  | Cmulf -> "*f"
  | Cdivf -> "/f"
  | Cfloatofint -> "floatofint"
  | Cintoffloat -> "intoffloat"
  | Ccmpf c -> Printf.sprintf "%sf" (comparison c)
  | Craise (k, d) -> Lambda.raise_kind k ^ Debuginfo.to_string d
  | Ccheckbound d -> "checkbound" ^ Debuginfo.to_string d

soit rec expr ppf = fonction
  | Cconst_int n -> fprintf ppf "%i" n
  | Cconst_natint n | Cconst_blockheader n ->
    fprintf ppf "%s" (Nativeint.to_string n)
  | Cconst_float s -> fprintf ppf "%s" s
  | Cconst_symbol s -> fprintf ppf "\"%s\"" s
  | Cconst_pointer n -> fprintf ppf "%ia" n
  | Cconst_natpointer n -> fprintf ppf "%sa" (Nativeint.to_string n)
  | Cvar id -> Ident.print ppf id
  | Clet(id, def, (Clet(_, _, _) tel body)) ->
      soit print_binding id ppf def =
        fprintf ppf "@[<2>%a@ %a@]" Ident.print id expr def dans
      soit rec in_part ppf = fonction
        | Clet(id, def, body) ->
            fprintf ppf "@ %a" (print_binding id) def;
            in_part ppf body
        | exp -> exp dans
      fprintf ppf "@[<2>(let@ @[<1>(%a" (print_binding id) def;
      soit exp = in_part ppf body dans
      fprintf ppf ")@]@ %a)@]" sequence exp
  | Clet(id, def, body) ->
     fprintf ppf
      "@[<2>(let@ @[<2>%a@ %a@]@ %a)@]"
      Ident.print id expr def sequence body
  | Cassign(id, exp) ->
      fprintf ppf "@[<2>(assign @[<2>%a@ %a@])@]" Ident.print id expr exp
  | Ctuple el ->
      soit tuple ppf el =
       soit first = ref vrai dans
       List.iter
        (fonc e ->
          si !first alors first := faux sinon fprintf ppf "@ ";
          expr ppf e)
        el dans
      fprintf ppf "@[<1>[%a]@]" tuple el
  | Cop(op, el) ->
      fprintf ppf "@[<2>(%s" (operation op);
      List.iter (fonc e -> fprintf ppf "@ %a" expr e) el;
      début filtre op avec
      | Capply (mty, _) -> fprintf ppf "@ %a" machtype mty
      | Cextcall(_, mty, _, _) -> fprintf ppf "@ %a" machtype mty
      | _ -> ()
      fin;
      fprintf ppf ")@]"
  | Csequence(e1, e2) ->
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" sequence e1 sequence e2
  | Cifthenelse(e1, e2, e3) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" expr e1 expr e2 expr e3
  | Cswitch(e1, index, cases) ->
      soit print_case i ppf =
        pour j = 0 à Array.length index - 1 faire
          si index.(j) = i alors fprintf ppf "case %i:" j
        fait dans
      soit print_cases ppf =
       pour i = 0 à Array.length cases - 1 faire
        fprintf ppf "@ @[<2>%t@ %a@]" (print_case i) sequence cases.(i)
       fait dans
      fprintf ppf "@[<v 0>@[<2>(switch@ %a@ @]%t)@]" expr e1 print_cases
  | Cloop e ->
      fprintf ppf "@[<2>(loop@ %a)@]" sequence e
  | Ccatch(i, ids, e1, e2) ->
      fprintf ppf
        "@[<2>(catch@ %a@;<1 -2>with(%d%a)@ %a)@]"
        sequence e1 i
        (fonc ppf ids ->
          List.iter
            (fonc id -> fprintf ppf " %a" Ident.print id)
            ids) ids
        sequence e2
  | Cexit (i, el) ->
      fprintf ppf "@[<2>(exit %d" i ;
      List.iter (fonc e -> fprintf ppf "@ %a" expr e) el;
      fprintf ppf ")@]"
  | Ctrywith(e1, id, e2) ->
      fprintf ppf "@[<2>(try@ %a@;<1 -2>with@ %a@ %a)@]"
             sequence e1 Ident.print id sequence e2

et sequence ppf = fonction
  | Csequence(e1, e2) -> fprintf ppf "%a@ %a" sequence e1 sequence e2
  | e -> expression ppf e

et expression ppf e = fprintf ppf "%a" expr e

soit fundecl ppf f =
  soit print_cases ppf cases =
    soit first = ref vrai dans
    List.iter
     (fonc (id, ty) ->
       si !first alors first := faux sinon fprintf ppf "@ ";
       fprintf ppf "%a: %a" Ident.print id machtype ty)
     cases dans
  fprintf ppf "@[<1>(function%s %s@;<1 4>@[<1>(%a)@]@ @[%a@])@]@."
         (Debuginfo.to_string f.fun_dbg) f.fun_name
         print_cases f.fun_args sequence f.fun_body

soit data_item ppf = fonction
  | Cdefine_symbol s -> fprintf ppf "\"%s\":" s
  | Cdefine_label l -> fprintf ppf "L%i:" l
  | Cglobal_symbol s -> fprintf ppf "global \"%s\"" s
  | Cint8 n -> fprintf ppf "byte %i" n
  | Cint16 n -> fprintf ppf "int16 %i" n
  | Cint32 n -> fprintf ppf "int32 %s" (Nativeint.to_string n)
  | Cint n -> fprintf ppf "int %s" (Nativeint.to_string n)
  | Csingle f -> fprintf ppf "single %s" f
  | Cdouble f -> fprintf ppf "double %s" f
  | Csymbol_address s -> fprintf ppf "addr \"%s\"" s
  | Clabel_address l -> fprintf ppf "addr L%i" l
  | Cstring s -> fprintf ppf "string \"%s\"" s
  | Cskip n -> fprintf ppf "skip %i" n
  | Calign n -> fprintf ppf "align %i" n

soit data ppf dl =
  soit items ppf = List.iter (fonc d -> fprintf ppf "@ %a" data_item d) dl dans
  fprintf ppf "@[<hv 1>(data%t)@]" items

soit phrase ppf = fonction
  | Cfunction f -> fundecl ppf f
  | Cdata dl -> data ppf dl
