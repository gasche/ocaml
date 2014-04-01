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
ouvre Clambda

soit rec structured_constant ppf = fonction
  | Uconst_float x -> fprintf ppf "%s" x
  | Uconst_int32 x -> fprintf ppf "%ld" x
  | Uconst_int64 x -> fprintf ppf "%Ld" x
  | Uconst_nativeint x -> fprintf ppf "%nd" x
  | Uconst_block (tag, l) ->
      fprintf ppf "block(%i" tag;
      List.iter (fonc u -> fprintf ppf ",%a" uconstant u) l;
      fprintf ppf ")"
  | Uconst_float_array sl ->
      fprintf ppf "floatarray(%s)"
        (String.concat "," sl)
  | Uconst_string s -> fprintf ppf "%S" s

et uconstant ppf = fonction
  | Uconst_ref (s, c) ->
      fprintf ppf "%S=%a" s structured_constant c
  | Uconst_int i -> fprintf ppf "%i" i
  | Uconst_ptr i -> fprintf ppf "%ia" i

soit rec lam ppf = fonction
  | Uvar id ->
      Ident.print ppf id
  | Uconst c -> uconstant ppf c
  | Udirect_apply(f, largs, _) ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(apply*@ %s %a)@]" f lams largs
  | Ugeneric_apply(lfun, largs, _) ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(apply@ %a%a)@]" lam lfun lams largs
  | Uclosure(clos, fv) ->
      soit idents ppf =
        List.iter (fprintf ppf "@ %a" Ident.print)dans
      soit one_fun ppf f =
        fprintf ppf "(fun@ %s@ %d @[<2>%a@] @[<2>%a@])"
          f.label f.arity idents f.params lam f.body dans
      soit funs ppf =
        List.iter (fprintf ppf "@ %a" one_fun) dans
      soit lams ppf =
        List.iter (fprintf ppf "@ %a" lam) dans
      fprintf ppf "@[<2>(closure@ %a %a)@]" funs clos lams fv
  | Uoffset(l,i) -> fprintf ppf "@[<2>(offset %a %d)@]" lam l i
  | Ulet(id, arg, body) ->
      soit rec letbody ul = filtre ul avec
        | Ulet(id, arg, body) ->
            fprintf ppf "@ @[<2>%a@ %a@]" Ident.print id lam arg;
            letbody body
        | _ -> ul dans
      fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a@ %a@]" Ident.print id lam arg;
      soit expr = letbody body dans
      fprintf ppf ")@]@ %a)@]" lam expr
  | Uletrec(id_arg_list, body) ->
      soit bindings ppf id_arg_list =
        soit spc = ref faux dans
        List.iter
          (fonc (id, l) ->
            si !spc alors fprintf ppf "@ " sinon spc := vrai;
            fprintf ppf "@[<2>%a@ %a@]" Ident.print id lam l)
          id_arg_list dans
      fprintf ppf
        "@[<2>(letrec@ (@[<hv 1>%a@])@ %a)@]" bindings id_arg_list lam body
  | Uprim(prim, largs, _) ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(%a%a)@]" Printlambda.primitive prim lams largs
  | Uswitch(larg, sw) ->
      soit switch ppf sw =
        soit spc = ref faux dans
        pour i = 0 à Array.length sw.us_index_consts - 1 faire
          soit n = sw.us_index_consts.(i) dans
          soit l = sw.us_actions_consts.(n) dans
          si !spc alors fprintf ppf "@ " sinon spc := vrai;
          fprintf ppf "@[<hv 1>case int %i:@ %a@]" i lam l;
        fait;
        pour i = 0 à Array.length sw.us_index_blocks - 1 faire
          soit n = sw.us_index_blocks.(i) dans
          soit l = sw.us_actions_blocks.(n) dans
          si !spc alors fprintf ppf "@ " sinon spc := vrai;
          fprintf ppf "@[<hv 1>case tag %i:@ %a@]" i lam l;
        fait dans
      fprintf ppf
       "@[<1>(switch %a@ @[<v 0>%a@])@]"
        lam larg switch sw
  | Ustringswitch(larg,sw,d) ->
      soit switch ppf sw =
        soit spc = ref faux dans
        List.iter
          (fonc (s,l) ->
            si !spc alors fprintf ppf "@ " sinon spc := vrai;
            fprintf ppf "@[<hv 1>case \"%s\":@ %a@]"
              (String.escaped s) lam l)
          sw ;
        si !spc alors fprintf ppf "@ " sinon spc := vrai;
        fprintf ppf "@[<hv 1>default:@ %a@]" lam d dans
      fprintf ppf
        "@[<1>(switch %a@ @[<v 0>%a@])@]" lam larg switch sw
  | Ustaticfail (i, ls)  ->
      soit lams ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      fprintf ppf "@[<2>(exit@ %d%a)@]" i lams ls;
  | Ucatch(i, vars, lbody, lhandler) ->
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
  | Utrywith(lbody, param, lhandler) ->
      fprintf ppf "@[<2>(try@ %a@;<1 -1>with %a@ %a)@]"
        lam lbody Ident.print param lam lhandler
  | Uifthenelse(lcond, lif, lelse) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" lam lcond lam lif lam lelse
  | Usequence(l1, l2) ->
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" lam l1 sequence l2
  | Uwhile(lcond, lbody) ->
      fprintf ppf "@[<2>(while@ %a@ %a)@]" lam lcond lam lbody
  | Ufor(param, lo, hi, dir, body) ->
      fprintf ppf "@[<2>(for %a@ %a@ %s@ %a@ %a)@]"
       Ident.print param lam lo
       (filtre dir avec Upto -> "to" | Downto -> "downto")
       lam hi lam body
  | Uassign(id, expr) ->
      fprintf ppf "@[<2>(assign@ %a@ %a)@]" Ident.print id lam expr
  | Usend (k, met, obj, largs, _) ->
      soit args ppf largs =
        List.iter (fonc l -> fprintf ppf "@ %a" lam l) largs dans
      soit kind =
        si k = Lambda.Self alors "self"
        sinon si k = Lambda.Cached alors "cache"
        sinon "" dans
      fprintf ppf "@[<2>(send%s@ %a@ %a%a)@]" kind lam obj lam met args largs

et sequence ppf ulam = filtre ulam avec
  | Usequence(l1, l2) ->
      fprintf ppf "%a@ %a" sequence l1 sequence l2
  | _ -> lam ppf ulam

soit clambda ppf ulam =
  fprintf ppf "%a@." lam ulam


soit rec approx ppf = fonction
    Value_closure(fundesc, a) ->
      Format.fprintf ppf "@[<2>function %s@ arity %i"
        fundesc.fun_label fundesc.fun_arity;
      si fundesc.fun_closed alors début
        Format.fprintf ppf "@ (closed)"
      fin;
      si fundesc.fun_inline <> None alors début
        Format.fprintf ppf "@ (inline)"
      fin;
      Format.fprintf ppf "@ -> @ %a@]" approx a
  | Value_tuple a ->
      soit tuple ppf a =
        pour i = 0 à Array.length a - 1 faire
          si i > 0 alors Format.fprintf ppf ";@ ";
          Format.fprintf ppf "%i: %a" i approx a.(i)
        fait dans
      Format.fprintf ppf "@[<hov 1>(%a)@]" tuple a
  | Value_unknown ->
      Format.fprintf ppf "_"
  | Value_const c ->
      fprintf ppf "@[const(%a)@]" uconstant c
  | Value_global_field (s, i) ->
      fprintf ppf "@[global(%s,%i)@]" s i

