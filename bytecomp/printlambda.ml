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

ouvre Format
ouvre Asttypes
ouvre Primitive
ouvre Types
ouvre Lambda


soit rec struct_const ppf = fonction
  | Const_base(Const_int n) -> fprintf ppf "%i" n
  | Const_base(Const_char c) -> fprintf ppf "%C" c
  | Const_base(Const_string (s, _)) -> fprintf ppf "%S" s
  | Const_immstring s -> fprintf ppf "#%S" s
  | Const_base(Const_float f) -> fprintf ppf "%s" f
  | Const_base(Const_int32 n) -> fprintf ppf "%lil" n
  | Const_base(Const_int64 n) -> fprintf ppf "%LiL" n
  | Const_base(Const_nativeint n) -> fprintf ppf "%nin" n
  | Const_pointer n -> fprintf ppf "%ia" n
  | Const_block(tag, []) ->
      fprintf ppf "[%i]" tag
  | Const_block(tag, sc1::scl) ->
      soit sconsts ppf scl =
        List.iter (fonc sc -> fprintf ppf "@ %a" struct_const sc) scl dans
      fprintf ppf "@[<1>[%i:@ @[%a%a@]]@]" tag struct_const sc1 sconsts scl
  | Const_float_array [] ->
      fprintf ppf "[| |]"
  | Const_float_array (f1 :: fl) ->
      soit floats ppf fl =
        List.iter (fonc f -> fprintf ppf "@ %s" f) fl dans
      fprintf ppf "@[<1>[|@[%s%a@]|]@]" f1 floats fl

soit boxed_integer_name = fonction
  | Pnativeint -> "nativeint"
  | Pint32 -> "int32"
  | Pint64 -> "int64"

soit print_boxed_integer name ppf bi =
  fprintf ppf "%s_%s" (boxed_integer_name bi) name

soit print_boxed_integer_conversion ppf bi1 bi2 =
  fprintf ppf "%s_of_%s" (boxed_integer_name bi2) (boxed_integer_name bi1)

soit boxed_integer_mark name = fonction
  | Pnativeint -> Printf.sprintf "Nativeint.%s" name
  | Pint32 -> Printf.sprintf "Int32.%s" name
  | Pint64 -> Printf.sprintf "Int64.%s" name

soit print_boxed_integer name ppf bi =
  fprintf ppf "%s" (boxed_integer_mark name bi);;

soit print_bigarray name unsafe kind ppf layout =
  fprintf ppf "Bigarray.%s[%s,%s]"
    (si unsafe alors "unsafe_"^ name sinon name)
    (filtre kind avec
     | Pbigarray_unknown -> "generic"
     | Pbigarray_float32 -> "float32"
     | Pbigarray_float64 -> "float64"
     | Pbigarray_sint8 -> "sint8"
     | Pbigarray_uint8 -> "uint8"
     | Pbigarray_sint16 -> "sint16"
     | Pbigarray_uint16 -> "uint16"
     | Pbigarray_int32 -> "int32"
     | Pbigarray_int64 -> "int64"
     | Pbigarray_caml_int -> "camlint"
     | Pbigarray_native_int -> "nativeint"
     | Pbigarray_complex32 -> "complex32"
     | Pbigarray_complex64 -> "complex64")
    (filtre layout avec
    |  Pbigarray_unknown_layout -> "unknown"
     | Pbigarray_c_layout -> "C"
     | Pbigarray_fortran_layout -> "Fortran")

soit record_rep ppf r =
  filtre r avec
  | Record_regular -> fprintf ppf "regular"
  | Record_float -> fprintf ppf "float"
;;

soit primitive ppf = fonction
  | Pidentity -> fprintf ppf "id"
  | Pignore -> fprintf ppf "ignore"
  | Prevapply _ -> fprintf ppf "revapply"
  | Pdirapply _ -> fprintf ppf "dirapply"
  | Pgetglobal id -> fprintf ppf "global %a" Ident.print id
  | Psetglobal id -> fprintf ppf "setglobal %a" Ident.print id
  | Pmakeblock(tag, Immutable) -> fprintf ppf "makeblock %i" tag
  | Pmakeblock(tag, Mutable) -> fprintf ppf "makemutable %i" tag
  | Pfield n -> fprintf ppf "field %i" n
  | Psetfield(n, ptr) ->
      soit instr = si ptr alors "setfield_ptr " sinon "setfield_imm " dans
      fprintf ppf "%s%i" instr n
  | Pfloatfield n -> fprintf ppf "floatfield %i" n
  | Psetfloatfield n -> fprintf ppf "setfloatfield %i" n
  | Pduprecord (rep, size) -> fprintf ppf "duprecord %a %i" record_rep rep size
  | Plazyforce -> fprintf ppf "force"
  | Pccall p -> fprintf ppf "%s" p.prim_name
  | Praise k -> fprintf ppf "%s" (Lambda.raise_kind k)
  | Psequand -> fprintf ppf "&&"
  | Psequor -> fprintf ppf "||"
  | Pnot -> fprintf ppf "not"
  | Pnegint -> fprintf ppf "~"
  | Paddint -> fprintf ppf "+"
  | Psubint -> fprintf ppf "-"
  | Pmulint -> fprintf ppf "*"
  | Pdivint -> fprintf ppf "/"
  | Pmodint -> fprintf ppf "mod"
  | Pandint -> fprintf ppf "and"
  | Porint -> fprintf ppf "or"
  | Pxorint -> fprintf ppf "xor"
  | Plslint -> fprintf ppf "lsl"
  | Plsrint -> fprintf ppf "lsr"
  | Pasrint -> fprintf ppf "asr"
  | Pintcomp(Ceq) -> fprintf ppf "=="
  | Pintcomp(Cneq) -> fprintf ppf "!="
  | Pintcomp(Clt) -> fprintf ppf "<"
  | Pintcomp(Cle) -> fprintf ppf "<="
  | Pintcomp(Cgt) -> fprintf ppf ">"
  | Pintcomp(Cge) -> fprintf ppf ">="
  | Poffsetint n -> fprintf ppf "%i+" n
  | Poffsetref n -> fprintf ppf "+:=%i"n
  | Pintoffloat -> fprintf ppf "int_of_float"
  | Pfloatofint -> fprintf ppf "float_of_int"
  | Pnegfloat -> fprintf ppf "~."
  | Pabsfloat -> fprintf ppf "abs."
  | Paddfloat -> fprintf ppf "+."
  | Psubfloat -> fprintf ppf "-."
  | Pmulfloat -> fprintf ppf "*."
  | Pdivfloat -> fprintf ppf "/."
  | Pfloatcomp(Ceq) -> fprintf ppf "==."
  | Pfloatcomp(Cneq) -> fprintf ppf "!=."
  | Pfloatcomp(Clt) -> fprintf ppf "<."
  | Pfloatcomp(Cle) -> fprintf ppf "<=."
  | Pfloatcomp(Cgt) -> fprintf ppf ">."
  | Pfloatcomp(Cge) -> fprintf ppf ">=."
  | Pstringlength -> fprintf ppf "string.length"
  | Pstringrefu -> fprintf ppf "string.unsafe_get"
  | Pstringsetu -> fprintf ppf "string.unsafe_set"
  | Pstringrefs -> fprintf ppf "string.get"
  | Pstringsets -> fprintf ppf "string.set"
  | Parraylength _ -> fprintf ppf "array.length"
  | Pmakearray _ -> fprintf ppf "makearray "
  | Parrayrefu _ -> fprintf ppf "array.unsafe_get"
  | Parraysetu _ -> fprintf ppf "array.unsafe_set"
  | Parrayrefs _ -> fprintf ppf "array.get"
  | Parraysets _ -> fprintf ppf "array.set"
  | Pctconst c ->
     soit const_name = filtre c avec
       | Big_endian -> "big_endian"
       | Word_size -> "word_size"
       | Ostype_unix -> "ostype_unix"
       | Ostype_win32 -> "ostype_win32"
       | Ostype_cygwin -> "ostype_cygwin" dans
     fprintf ppf "sys.constant_%s" const_name
  | Pisint -> fprintf ppf "isint"
  | Pisout -> fprintf ppf "isout"
  | Pbittest -> fprintf ppf "testbit"
  | Pbintofint bi -> print_boxed_integer "of_int" ppf bi
  | Pintofbint bi -> print_boxed_integer "to_int" ppf bi
  | Pcvtbint (bi1, bi2) -> print_boxed_integer_conversion ppf bi1 bi2
  | Pnegbint bi -> print_boxed_integer "neg" ppf bi
  | Paddbint bi -> print_boxed_integer "add" ppf bi
  | Psubbint bi -> print_boxed_integer "sub" ppf bi
  | Pmulbint bi -> print_boxed_integer "mul" ppf bi
  | Pdivbint bi -> print_boxed_integer "div" ppf bi
  | Pmodbint bi -> print_boxed_integer "mod" ppf bi
  | Pandbint bi -> print_boxed_integer "and" ppf bi
  | Porbint bi -> print_boxed_integer "or" ppf bi
  | Pxorbint bi -> print_boxed_integer "xor" ppf bi
  | Plslbint bi -> print_boxed_integer "lsl" ppf bi
  | Plsrbint bi -> print_boxed_integer "lsr" ppf bi
  | Pasrbint bi -> print_boxed_integer "asr" ppf bi
  | Pbintcomp(bi, Ceq) -> print_boxed_integer "==" ppf bi
  | Pbintcomp(bi, Cneq) -> print_boxed_integer "!=" ppf bi
  | Pbintcomp(bi, Clt) -> print_boxed_integer "<" ppf bi
  | Pbintcomp(bi, Cgt) -> print_boxed_integer ">" ppf bi
  | Pbintcomp(bi, Cle) -> print_boxed_integer "<=" ppf bi
  | Pbintcomp(bi, Cge) -> print_boxed_integer ">=" ppf bi
  | Pbigarrayref(unsafe, n, kind, layout) ->
      print_bigarray "get" unsafe kind ppf layout
  | Pbigarrayset(unsafe, n, kind, layout) ->
      print_bigarray "set" unsafe kind ppf layout
  | Pbigarraydim(n) -> fprintf ppf "Bigarray.dim_%i" n
  | Pstring_load_16(unsafe) ->
     si unsafe alors fprintf ppf "string.unsafe_get16"
     sinon fprintf ppf "string.get16"
  | Pstring_load_32(unsafe) ->
     si unsafe alors fprintf ppf "string.unsafe_get32"
     sinon fprintf ppf "string.get32"
  | Pstring_load_64(unsafe) ->
     si unsafe alors fprintf ppf "string.unsafe_get64"
     sinon fprintf ppf "string.get64"
  | Pstring_set_16(unsafe) ->
     si unsafe alors fprintf ppf "string.unsafe_set16"
     sinon fprintf ppf "string.set16"
  | Pstring_set_32(unsafe) ->
     si unsafe alors fprintf ppf "string.unsafe_set32"
     sinon fprintf ppf "string.set32"
  | Pstring_set_64(unsafe) ->
     si unsafe alors fprintf ppf "string.unsafe_set64"
     sinon fprintf ppf "string.set64"
  | Pbigstring_load_16(unsafe) ->
     si unsafe alors fprintf ppf "bigarray.array1.unsafe_get16"
     sinon fprintf ppf "bigarray.array1.get16"
  | Pbigstring_load_32(unsafe) ->
     si unsafe alors fprintf ppf "bigarray.array1.unsafe_get32"
     sinon fprintf ppf "bigarray.array1.get32"
  | Pbigstring_load_64(unsafe) ->
     si unsafe alors fprintf ppf "bigarray.array1.unsafe_get64"
     sinon fprintf ppf "bigarray.array1.get64"
  | Pbigstring_set_16(unsafe) ->
     si unsafe alors fprintf ppf "bigarray.array1.unsafe_set16"
     sinon fprintf ppf "bigarray.array1.set16"
  | Pbigstring_set_32(unsafe) ->
     si unsafe alors fprintf ppf "bigarray.array1.unsafe_set32"
     sinon fprintf ppf "bigarray.array1.set32"
  | Pbigstring_set_64(unsafe) ->
     si unsafe alors fprintf ppf "bigarray.array1.unsafe_set64"
     sinon fprintf ppf "bigarray.array1.set64"
  | Pbswap16 -> fprintf ppf "bswap16"
  | Pbbswap(bi) -> print_boxed_integer "bswap" ppf bi

soit rec lam ppf = fonction
  | Lvar id ->
      Ident.print ppf id
  | Lconst cst ->
      struct_const ppf cst
  | Lapply(lfun, largs, _) ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(apply@ %a%a)@]" lam lfun lams largs
  | Lfunction(kind, params, body) ->
      soit pr_params ppf params =
        filtre kind avec
        | Curried ->
            List.iter (fonc param -> fprintf ppf "@ %a" Ident.print param) params
        | Tupled ->
            fprintf ppf " (";
            soit first = ref vrai dans
            List.iter
              (fonc param ->
                si !first alors first := faux sinon fprintf ppf ",@ ";
                Ident.print ppf param)
              params;
            fprintf ppf ")" dans
      fprintf ppf "@[<2>(function%a@ %a)@]" pr_params params lam body
  | Llet(str, id, arg, body) ->
      soit kind = fonction
        Alias -> "a" | Strict -> "" | StrictOpt -> "o" | Variable -> "v" dans
      soit rec letbody = fonction
        | Llet(str, id, arg, body) ->
            fprintf ppf "@ @[<2>%a =%s@ %a@]" Ident.print id (kind str) lam arg;
            letbody body
        | expr -> expr dans
      fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a =%s@ %a@]"
        Ident.print id (kind str) lam arg;
      soit expr = letbody body dans
      fprintf ppf ")@]@ %a)@]" lam expr
  | Lletrec(id_arg_list, body) ->
      soit bindings ppf id_arg_list =
        soit spc = ref faux dans
        List.iter
          (fonc (id, l) ->
            si !spc alors fprintf ppf "@ " sinon spc := vrai;
            fprintf ppf "@[<2>%a@ %a@]" Ident.print id lam l)
          id_arg_list dans
      fprintf ppf
        "@[<2>(letrec@ (@[<hv 1>%a@])@ %a)@]" bindings id_arg_list lam body
  | Lprim(prim, largs) ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(%a%a)@]" primitive prim lams largs
  | Lswitch(larg, sw) ->
      soit switch ppf sw =
        soit spc = ref faux dans
        List.iter
         (fonc (n, l) ->
           si !spc alors fprintf ppf "@ " sinon spc := vrai;
           fprintf ppf "@[<hv 1>case int %i:@ %a@]" n lam l)
         sw.sw_consts;
        List.iter
          (fonc (n, l) ->
            si !spc alors fprintf ppf "@ " sinon spc := vrai;
            fprintf ppf "@[<hv 1>case tag %i:@ %a@]" n lam l)
          sw.sw_blocks ;
        début filtre sw.sw_failaction avec
        | None  -> ()
        | Some l ->
            si !spc alors fprintf ppf "@ " sinon spc := vrai;
            fprintf ppf "@[<hv 1>default:@ %a@]" lam l
        fin dans
      fprintf ppf
       "@[<1>(%s %a@ @[<v 0>%a@])@]"
       (filtre sw.sw_failaction avec None -> "switch*" | _ -> "switch")
       lam larg switch sw
  | Lstringswitch(arg, cases, default) ->
      soit switch ppf cases =
        soit spc = ref faux dans
        List.iter
         (fonc (s, l) ->
           si !spc alors fprintf ppf "@ " sinon spc := vrai;
           fprintf ppf "@[<hv 1>case \"%s\":@ %a@]" (String.escaped s) lam l)
          cases;
        si !spc alors fprintf ppf "@ " sinon spc := vrai;
        fprintf ppf "@[<hv 1>default:@ %a@]" lam default dans
      fprintf ppf
       "@[<1>(stringswitch %a@ @[<v 0>%a@])@]" lam arg switch cases
  | Lstaticraise (i, ls)  ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(exit@ %d%a)@]" i lams ls;
  | Lstaticcatch(lbody, (i, vars), lhandler) ->
      fprintf ppf "@[<2>(catch@ %a@;<1 -1>with (%d%a)@ %a)@]"
        lam lbody i
        (fonc ppf vars -> filtre vars avec
          | [] -> ()
          | _ ->
              List.iter
                (fonc x -> fprintf ppf " %a" Ident.print x)
                vars)
        vars
        lam lhandler
  | Ltrywith(lbody, param, lhandler) ->
      fprintf ppf "@[<2>(try@ %a@;<1 -1>with %a@ %a)@]"
        lam lbody Ident.print param lam lhandler
  | Lifthenelse(lcond, lif, lelse) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" lam lcond lam lif lam lelse
  | Lsequence(l1, l2) ->
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" lam l1 sequence l2
  | Lwhile(lcond, lbody) ->
      fprintf ppf "@[<2>(while@ %a@ %a)@]" lam lcond lam lbody
  | Lfor(param, lo, hi, dir, body) ->
      fprintf ppf "@[<2>(for %a@ %a@ %s@ %a@ %a)@]"
       Ident.print param lam lo
       (filtre dir avec Upto -> "to" | Downto -> "downto")
       lam hi lam body
  | Lassign(id, expr) ->
      fprintf ppf "@[<2>(assign@ %a@ %a)@]" Ident.print id lam expr
  | Lsend (k, met, obj, largs, _) ->
      soit args ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      soit kind =
        si k = Self alors "self" sinon si k = Cached alors "cache" sinon "" dans
      fprintf ppf "@[<2>(send%s@ %a@ %a%a)@]" kind lam obj lam met args largs
  | Levent(expr, ev) ->
      soit kind =
       filtre ev.lev_kind avec
       | Lev_before -> "before"
       | Lev_after _  -> "after"
       | Lev_function -> "funct-body" dans
      fprintf ppf "@[<2>(%s %s(%i)%s:%i-%i@ %a)@]" kind
              ev.lev_loc.Location.loc_start.Lexing.pos_fname
              ev.lev_loc.Location.loc_start.Lexing.pos_lnum
              (si ev.lev_loc.Location.loc_ghost alors "<ghost>" sinon "")
              ev.lev_loc.Location.loc_start.Lexing.pos_cnum
              ev.lev_loc.Location.loc_end.Lexing.pos_cnum
              lam expr
  | Lifused(id, expr) ->
      fprintf ppf "@[<2>(ifused@ %a@ %a)@]" Ident.print id lam expr

et sequence ppf = fonction
  | Lsequence(l1, l2) ->
      fprintf ppf "%a@ %a" sequence l1 sequence l2
  | l ->
      lam ppf l

soit structured_constant = struct_const

soit lambda = lam
