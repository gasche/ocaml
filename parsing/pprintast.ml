(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*    Thomas Gazagnaire (OCamlPro), Fabrice Le Fessant (INRIA Saclay)     *)
(*    Hongbo Zhang (University of Pennsylvania)                           *)
(*   Copyright 2007 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

(* Original Code from Ber-metaocaml, modified for 3.12.0 and fixed *)
(* Printing code expressions *)
(* Authors:  Ed Pizzi, Fabrice Le Fessant *)
(* Extensive Rewrite: Hongbo Zhang: University of Pennsylvania *)
(* TODO more fine-grained precedence pretty-printing *)

ouvre Asttypes
ouvre Format
ouvre Location
ouvre Longident
ouvre Parsetree

soit prefix_symbols  = [ '!'; '?'; '~' ] ;;
soit infix_symbols = [ '='; '<'; '>'; '@'; '^'; '|'; '&'; '+'; '-'; '*'; '/';
                      '$'; '%' ]
soit operator_chars = [ '!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/';
                       ':'; '<'; '='; '>'; '?'; '@'; '^'; '|'; '~' ]
soit numeric_chars  = [ '0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9' ]

(* type fixity = Infix| Prefix  *)

soit special_infix_strings =
  ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; ":="; "!=" ]

(* determines if the string is an infix string.
   checks backwards, first allowing a renaming postfix ("_102") which
   may have resulted from Pexp -> Texp -> Pexp translation, then checking
   if all the characters in the beginning of the string are valid infix
   characters. *)
soit fixity_of_string  = fonction
  | s quand List.mem s special_infix_strings -> `Infix s
  | s quand List.mem s.[0] infix_symbols -> `Infix s
  | s quand List.mem s.[0] prefix_symbols -> `Prefix s
  | _ -> `Normal

soit view_fixity_of_exp = fonction
  | {pexp_desc = Pexp_ident {txt=Lident l;_};_} -> fixity_of_string l
  | _ -> `Normal  ;;

soit is_infix  = fonction  | `Infix _ -> vrai | _  -> faux

soit is_predef_option = fonction
  | (Ldot (Lident "*predef*","option")) -> vrai
  | _ -> faux

(* which identifiers are in fact operators needing parentheses *)
soit needs_parens txt =
  is_infix (fixity_of_string txt)
  || List.mem txt.[0] prefix_symbols

(* some infixes need spaces around parens to avoid clashes with comment syntax *)
soit needs_spaces txt =
  txt.[0]='*' || txt.[String.length txt - 1] = '*'

(* add parentheses to binders when they are in fact infix or prefix operators *)
soit protect_ident ppf txt =
  soit format : (_, _, _) format =
    si not (needs_parens txt) alors "%s"
    sinon si needs_spaces txt alors "(@;%s@;)"
    sinon "(%s)"
  dans fprintf ppf format txt

soit protect_longident ppf print_longident longprefix txt =
  soit format : (_, _, _) format =
    si not (needs_parens txt) alors "%a.%s"
    sinon si needs_spaces txt alors  "(@;%a.%s@;)"
    sinon "(%a.%s)" dans
  fprintf ppf format print_longident longprefix txt

type space_formatter = (unit, Format.formatter, unit) format

soit override = fonction
  | Override -> "!"
  | Fresh -> ""

(* variance encoding: need to sync up with the [parser.mly] *)
soit type_variance = fonction
  | Invariant -> ""
  | Covariant -> "+"
  | Contravariant -> "-"

type construct =
  [ `cons de expression list
  | `list de expression list
  | `nil
  | `normal
  | `simple de Longident.t
  | `tuple ]

soit view_expr x =
  filtre x.pexp_desc avec
  | Pexp_construct ( {txt= Lident "()"; _},_) -> `tuple
  | Pexp_construct ( {txt= Lident "[]";_},_) -> `nil
  | Pexp_construct ( {txt= Lident"::";_},Some _) ->
      soit rec loop exp acc = filtre exp avec
          | {pexp_desc=Pexp_construct ({txt=Lident "[]";_},_);_} ->
              (List.rev acc,vrai)
          | {pexp_desc=
             Pexp_construct ({txt=Lident "::";_},
                             Some ({pexp_desc= Pexp_tuple([e1;e2]);_}));_} ->
              loop e2 (e1::acc)
          | e -> (List.rev (e::acc),faux) dans
      soit (ls,b) = loop x []  dans
      si b alors
        `list ls
      sinon `cons ls
  | Pexp_construct (x,None) -> `simple (x.txt)
  | _ -> `normal

soit is_simple_construct :construct -> bool = fonction
  | `nil | `tuple | `list _ | `simple _  -> vrai
  | `cons _ | `normal -> faux

soit pp = fprintf

soit rec is_irrefut_patt x =
  filtre x.ppat_desc avec
  | Ppat_any | Ppat_var _ | Ppat_unpack _ -> vrai
  | Ppat_alias (p,_) -> is_irrefut_patt p
  | Ppat_tuple (ps) -> List.for_all is_irrefut_patt ps
  | Ppat_constraint (p,_) -> is_irrefut_patt p
  | Ppat_or (l,r) -> is_irrefut_patt l || is_irrefut_patt r
  | Ppat_record (ls,_) -> List.for_all (fonc (_,x) -> is_irrefut_patt x) ls
  | Ppat_lazy p -> is_irrefut_patt p
  | Ppat_extension _ -> affirme faux
  | Ppat_interval _
  | Ppat_constant _ | Ppat_construct _  | Ppat_variant _ | Ppat_array _
  | Ppat_type _-> faux (*conservative*)
classe printer  ()= objet(self:'self)
  val pipe = faux
  val semi = faux
  val ifthenelse = faux
  méthode under_pipe = {<pipe=vrai>}
  méthode under_semi = {<semi=vrai>}
  méthode under_ifthenelse = {<ifthenelse=vrai>}
  méthode reset_semi = {<semi=faux>}
  méthode reset_ifthenelse = {<ifthenelse=faux>}
  méthode reset_pipe = {<pipe=faux>}
  méthode reset = {<pipe=faux;semi=faux;ifthenelse=faux>}
  méthode list : 'a . ?sep:space_formatter -> ?first:space_formatter ->
    ?last:space_formatter -> (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a list -> unit
        = fonc  ?sep ?first  ?last fu f xs ->
          soit first = filtre first avec Some x -> x |None -> ""
          et last = filtre last avec Some x -> x |None -> ""
          et sep = filtre sep avec Some x -> x |None -> "@ " dans
          soit aux f = fonction
            | [] -> ()
            | [x] -> fu f x
            | xs ->
                soit rec loop  f = fonction
                  | [x] -> fu f x
                  | x::xs ->  pp f "%a%(%)%a" fu x sep loop xs
                  | _ -> affirme faux dans début
                      pp f "%(%)%a%(%)" first loop xs last;
                  fin dans
          aux f xs
  méthode option : 'a. ?first:space_formatter -> ?last:space_formatter ->
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit =
      fonc  ?first  ?last fu f a ->
        soit first = filtre first avec Some x -> x | None -> ""
        et last = filtre last avec Some x -> x | None -> "" dans
        filtre a avec
        | None -> ()
        | Some x -> pp f "%(%)%a%(%)" first fu x last
  méthode paren: 'a . ?first:space_formatter -> ?last:space_formatter ->
    bool -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit =
    fonc  ?(first="") ?(last="") b fu f x ->
      si b alors pp f "(%(%)%a%(%))" first fu  x last
      sinon fu f x


  méthode longident f = fonction
    | Lident s -> protect_ident f s
    | Ldot(y,s) -> protect_longident f self#longident y s
    | Lapply (y,s) ->
        pp f "%a(%a)" self#longident y self#longident s
  méthode longident_loc f x = pp f "%a" self#longident x.txt
  méthode constant f  = fonction
    | Const_char i -> pp f "%C"  i
    | Const_string (i, None) -> pp f "%S" i
    | Const_string (i, Some delim) -> pp f "{%s|%s|%s}" delim i delim
    | Const_int i -> self#paren (i<0) (fonc f -> pp f "%d") f i
    | Const_float  i -> self#paren (i.[0]='-') (fonc f -> pp f "%s") f i
    | Const_int32 i -> self#paren (i<0l) (fonc f -> pp f "%ldl") f i
    | Const_int64 i -> self#paren (i<0L) (fonc f -> pp f "%LdL") f i
                                         (* pp f "%LdL" i *)
    | Const_nativeint i -> self#paren (i<0n) (fonc f -> pp f "%ndn") f i
                                             (* pp f "%ndn" i *)

  (* trailing space*)
  méthode mutable_flag f   = fonction
    | Immutable -> ()
    | Mutable -> pp f "mutable@;"
  méthode virtual_flag f  = fonction
    | Concrete -> ()
    | Virtual -> pp f "virtual@;"

  (* trailing space added *)
  méthode rec_flag f = fonction
    | Nonrecursive -> ()
    | Recursive -> pp f "rec "
  méthode direction_flag f = fonction
    | Upto -> pp f "to@ "
    | Downto -> pp f "downto@ "
  méthode private_flag f = fonction
    | Public -> ()
    | Private -> pp f "private@ "

  méthode constant_string f s = pp f "%S" s
  méthode tyvar f str = pp f "'%s" str
  méthode string_quot f x = pp f "`%s" x
  méthode type_var_option f str =
    filtre str avec
    | None -> pp f "_" (* wildcard*)
    | Some {txt;_} -> self#tyvar f txt

          (* c ['a,'b] *)
  méthode class_params_def f =  fonction
    | [] -> ()
    | l ->
        pp f "[%a] " (* space *)
          (self#list (fonc f ({txt;_},s) ->
            pp f "%s%a" (type_variance s) self#tyvar txt) ~sep:",") l

  méthode type_with_label f (label,({ptyp_desc;_}tel c) ) =
    filtre label avec
    | "" ->  self#core_type1 f c (* otherwise parenthesize *)
    | s  ->
        si s.[0]='?' alors
          filtre ptyp_desc avec
          | Ptyp_constr ({txt;_}, l) ->
              affirme (is_predef_option txt);
              pp f "%s:%a" s (self#list self#core_type1) l
          | _ -> failwith "entrée invalide dans print_type_with_label"
        sinon pp f "%s:%a" s self#core_type1 c
  méthode core_type f x =
    si x.ptyp_attributes <> [] alors début
      pp f "((%a)%a)" self#core_type {x avec ptyp_attributes=[]}
        self#attributes x.ptyp_attributes
    fin
    sinon filtre x.ptyp_desc avec
    | Ptyp_arrow (l, ct1, ct2) ->
        pp f "@[<2>%a@;->@;%a@]" (* FIXME remove parens later *)
          self#type_with_label (l,ct1) self#core_type ct2
    | Ptyp_alias (ct, s) ->
        pp f "@[<2>%a@;as@;'%s@]" self#core_type1 ct s
    | Ptyp_poly (sl, ct) ->
        pp f "@[<2>%a%a@]"
          (fonc f l ->
            pp f "%a"
              (fonc f l -> filtre l avec
              | [] -> ()
              | _ ->
                  pp f "%a@;.@;"
                    (self#list self#tyvar ~sep:"@;")  l)
              l)
          sl  self#core_type ct
    | _ -> pp f "@[<2>%a@]" self#core_type1 x
  méthode core_type1 f x =
    si x.ptyp_attributes <> [] alors self#core_type f x
    sinon filtre x.ptyp_desc avec
    | Ptyp_any -> pp f "_";
    | Ptyp_var s -> self#tyvar f  s;
    | Ptyp_tuple l ->  pp f "(%a)" (self#list self#core_type1 ~sep:"*@;") l
    | Ptyp_constr (li, l) ->
        pp f (* "%a%a@;" *) "%a%a"
          (fonc f l -> filtre l avec
          |[] -> ()
          |[x]-> pp f "%a@;" self#core_type1  x
          | _ -> self#list ~first:"(" ~last:")@;" self#core_type ~sep:"," f l)
          l self#longident_loc li
    | Ptyp_variant (l, closed, low) ->
        soit type_variant_helper f x =
          filtre x avec
          | Rtag (l, _, ctl) -> pp f "@[<2>%a%a@]"  self#string_quot l
                (fonc f l -> filtre l avec
                |[] -> ()
                | _ -> pp f "@;of@;%a"
                      (self#list self#core_type ~sep:"&")  ctl) ctl
          | Rinherit ct -> self#core_type f ct dans
        pp f "@[<2>[%a%a]@]"
          (fonc f l
            ->
              filtre l avec
              | [] -> ()
              | _ ->
              pp f "%s@;%a"
                (filtre (closed,low) avec
                | (Closed,None) -> ""
                | (Closed,Some _) -> "<" (* FIXME desugar the syntax sugar*)
                | (Open,_) -> ">")
                (self#list type_variant_helper ~sep:"@;<1 -2>| ") l) l
          (fonc f low
            ->
              filtre low avec
              |Some [] |None -> ()
              |Some xs ->
              pp f ">@ %a"
                (self#list self#string_quot) xs) low
    | Ptyp_object (l, o) ->
        soit core_field_type f (s, ct) =
          pp f "@[<hov2>%s@ :%a@ @]" s self#core_type ct
        dans
        soit field_var f = fonction
          | Asttypes.Closed -> ()
          | Asttypes.Open ->
              filtre l avec
              | [] -> pp f ".."
              | _ -> pp f " ;.."
        dans
        pp f "@[<hov2><@ %a%a@ >@]" (self#list core_field_type ~sep:";") l
          field_var o
    | Ptyp_class (li, l) ->   (*FIXME*)
        pp f "@[<hov2>%a#%a@]"
          (self#list self#core_type ~sep:"," ~first:"(" ~last:")") l
          self#longident_loc li
    | Ptyp_package (lid, cstrs) ->
        soit aux f (s, ct) =
          pp f "type %a@ =@ %a" self#longident_loc s self#core_type ct  dans
        (filtre cstrs avec
        |[] -> pp f "@[<hov2>(module@ %a)@]" self#longident_loc lid
        |_ ->
            pp f "@[<hov2>(module@ %a@ with@ %a)@]" self#longident_loc lid
              (self#list aux  ~sep:"@ and@ ")  cstrs)
    | Ptyp_extension (s, arg) ->
      pp f "@[<2>(&%s@ %a)@]" s.txt self#payload arg
    | _ -> self#paren vrai self#core_type f x
          (********************pattern********************)
          (* be cautious when use [pattern], [pattern1] is preferred *)
  méthode pattern f x =
    soit rec list_of_pattern acc = fonction (* only consider ((A|B)|C)*)
      | {ppat_desc= Ppat_or (p1,p2);_} ->
          list_of_pattern  (p2::acc) p1
      | x -> x::acc dans
    si x.ppat_attributes <> [] alors début
      pp f "((%a)%a)" self#pattern {x avec ppat_attributes=[]}
        self#attributes x.ppat_attributes
    fin
    sinon filtre x.ppat_desc avec
    | Ppat_alias (p, s) -> pp f "@[<2>%a@;as@;%a@]"
          self#pattern p protect_ident s.txt (* RA*)
    | Ppat_or (p1, p2) -> (* *)
        pp f "@[<hov0>%a@]" (self#list ~sep:"@,|" self#pattern) (list_of_pattern [] x)
    | _ -> self#pattern1 f x
  méthode pattern1 (f:Format.formatter) (x:pattern) :unit =
    soit rec pattern_list_helper f  =  fonction
      | {ppat_desc =
         Ppat_construct
           ({ txt = Lident("::") ;_},
            Some ({ppat_desc = Ppat_tuple([pat1; pat2]);_})); _}
            ->
              pp f "%a::%a"  self#simple_pattern  pat1  pattern_list_helper pat2 (*RA*)
      | p -> self#pattern1 f p dans
    si x.ppat_attributes <> [] alors self#pattern f x
    sinon filtre x.ppat_desc avec
    | Ppat_variant (l, Some p) ->  pp f "@[<2>`%s@;%a@]" l self#pattern1 p (*RA*)
    | Ppat_construct (({txt=Lident("()"|"[]");_}), _) -> self#simple_pattern f x
    | Ppat_construct (({txt;_} tel li), po) -> (* FIXME The third field always false *)
        si txt = Lident "::" alors
          pp f "%a" pattern_list_helper x
        sinon
          (filtre po avec
          |Some x ->
              pp f "%a@;%a"  self#longident_loc li self#simple_pattern x
          | None -> pp f "%a@;"self#longident_loc li )
    | _ -> self#simple_pattern f x
  méthode simple_pattern (f:Format.formatter) (x:pattern) :unit =
    filtre x.ppat_desc avec
    | Ppat_construct (({txt=Lident ("()"|"[]" tel x);_}), _) -> pp f  "%s" x
    | Ppat_any -> pp f "_";
    | Ppat_var ({txt = txt;_}) -> protect_ident f txt
    | Ppat_array l ->
        pp f "@[<2>[|%a|]@]"  (self#list self#pattern1 ~sep:";") l
    | Ppat_unpack (s) ->
        pp f "(module@ %s)@ " s.txt
    | Ppat_type li ->
        pp f "#%a" self#longident_loc li
    | Ppat_record (l, closed) ->
        soit longident_x_pattern f (li, p) =
          filtre (li,p.ppat_desc) avec
          | ({txt=Lident s;_ },Ppat_var {txt;_} ) quand s = txt ->
              pp f "@[<2>%a@]"  self#longident_loc li
          | _ ->
            pp f "@[<2>%a@;=@;%a@]" self#longident_loc li self#pattern1 p dans
        (filtre closed avec
        |Closed ->
            pp f "@[<2>{@;%a@;}@]"
              (self#list longident_x_pattern ~sep:";@;") l
        | _ ->
            pp f "@[<2>{@;%a;_}@]"
              (self#list longident_x_pattern ~sep:";@;") l)
    | Ppat_tuple l -> pp f "@[<1>(%a)@]" (self#list  ~sep:"," self#pattern1)  l (* level1*)
    | Ppat_constant (c) -> pp f "%a" self#constant c
    | Ppat_interval (c1, c2) -> pp f "%a..%a" self#constant c1 self#constant c2
    | Ppat_variant (l,None) ->  pp f "`%s" l
    | Ppat_constraint (p, ct) ->
        pp f "@[<2>(%a@;:@;%a)@]" self#pattern1 p self#core_type ct
    | Ppat_lazy p ->
        pp f "@[<2>(lazy@;%a)@]" self#pattern1 p
    | _ -> self#paren vrai self#pattern f x

  méthode label_exp f (l,opt,p) =
    si l = "" alors
      pp f "%a@ " self#simple_pattern p (*single case pattern parens needed here *)
    sinon
      si l.[0] = '?' alors
        soit len = String.length l - 1 dans
        soit rest = String.sub l 1 len dans début
          filtre p.ppat_desc avec
          | Ppat_var {txt;_} quand txt = rest ->
              (filtre opt avec
              |Some o -> pp f "?(%s=@;%a)@;" rest  self#expression o
              | None -> pp f "?%s@ " rest)
          | _ -> (filtre opt avec
            | Some o -> pp f "%s:(%a=@;%a)@;" l self#pattern1 p self#expression o
            | None -> pp f "%s:%a@;" l self#simple_pattern p  )
        fin
      sinon
        (filtre p.ppat_desc avec
        | Ppat_var {txt;_} quand txt = l ->
            pp f "~%s@;" l
        | _ ->  pp f "~%s:%a@;" l self#simple_pattern p )
  méthode sugar_expr f e =
    si e.pexp_attributes <> [] alors faux
      (* should also check attributes underneath *)
    sinon filtre e.pexp_desc avec
    | Pexp_apply
        ({pexp_desc=
          Pexp_ident
            {txt= Ldot (Lident (("Array"|"String") tel s),"get");_};_},
         [(_,e1);(_,e2)]) -> début
              soit fmt:(_,_,_)format =
                si s= "Array" alors "@[%a.(%a)@]" sinon "@[%a.[%a]@]" dans
              pp f fmt   self#simple_expr e1 self#expression e2;
              vrai
            fin
    |Pexp_apply
        ({pexp_desc=
          Pexp_ident
            {txt= Ldot (Lident (("Array"|"String") tel s),
                        "set");_};_},[(_,e1);(_,e2);(_,e3)])
      ->
        soit fmt :(_,_,_) format=
          si s= "Array" alors
            "@[%a.(%a)@ <-@;%a@]"
          sinon
            "@[%a.[%a]@ <-@;%a@]" dans  (* @;< gives error here *)
        pp f fmt self#simple_expr e1  self#expression e2  self#expression e3;
        vrai
    | Pexp_apply ({pexp_desc=Pexp_ident {txt=Lident "!";_};_}, [(_,e)]) -> début
        pp f "@[<hov>!%a@]" self#simple_expr e;
        vrai
    fin
    | Pexp_apply
        ({pexp_desc=Pexp_ident
                     {txt= Ldot (Ldot (Lident "Bigarray", array), ("get"|"set" tel gs)) ;_};_},
         label_exprs) ->
           début filtre array,gs avec
           | "Genarray","get"   ->
               début filtre label_exprs avec
               | [(_,a);(_,{pexp_desc=Pexp_array ls;_})]  -> début
                   pp f "@[%a.{%a}@]" self#simple_expr a
                   (self#list ~sep:"," self#simple_expr ) ls;
                   vrai
               fin
               | _ -> faux
               fin
           | "Genarray","set" ->
               début filtre label_exprs avec
               | [(_,a);(_,{pexp_desc=Pexp_array ls;_});(_,c)]  -> début
                   pp f "@[%a.{%a}@ <-@ %a@]" self#simple_expr a
                   (self#list ~sep:"," self#simple_expr ) ls self#simple_expr c;
                   vrai
               fin
               | _ -> faux
               fin
           | ("Array1"|"Array2"|"Array3"),"set" ->
               début
                 filtre label_exprs avec
                 | (_,a)::rest ->
                     début filtre List.rev rest avec
                     | (_,v)::rest ->
                         soit args = List.map snd (List.rev rest) dans
                         pp f "@[%a.{%a}@ <-@ %a@]"
                           self#simple_expr a (self#list ~sep:"," self#simple_expr)
                           args self#simple_expr v;
                         vrai
                     | _ -> affirme faux
                     fin
                 | _ -> affirme faux
               fin
           | ("Array1"|"Array2"|"Array3"),"get" ->
               début filtre label_exprs avec
               |(_,a)::rest ->
                 pp f "@[%a.{%a}@]"
                     self#simple_expr a (self#list ~sep:"," self#simple_expr)
                     (List.map snd rest);
                   vrai
               | _ -> affirme faux
               fin
           | _ -> faux
           fin

    | _ -> faux
  méthode expression f x =
    si x.pexp_attributes <> [] alors début
      pp f "((%a)%a)" self#expression {x avec pexp_attributes=[]}
        self#attributes x.pexp_attributes
    fin
    sinon filtre x.pexp_desc avec
    | Pexp_function _ | Pexp_fun _ | Pexp_match _ | Pexp_try _ | Pexp_sequence _
      quand pipe || semi ->
        self#paren vrai self#reset#expression f x
    | Pexp_ifthenelse _ | Pexp_sequence _ quand ifthenelse ->
        self#paren vrai self#reset#expression f x
    | Pexp_let _ | Pexp_letmodule _ quand semi ->
        self#paren vrai self#reset#expression f x
    | Pexp_fun (l, e0, p, e) ->
        pp f "@[<2>fun@;%a@;->@;%a@]"
          self#label_exp (l, e0, p)
          self#expression e
    | Pexp_function l ->
        pp f "@[<hv>function%a@]" self#case_list l
    | Pexp_match (e, l) ->
        pp f "@[<hv0>@[<hv0>@[<2>match %a@]@ with@]%a@]" self#reset#expression e self#case_list l

    | Pexp_try (e, l) ->
        pp f "@[<0>@[<hv2>try@ %a@]@ @[<0>with%a@]@]" (* "try@;@[<2>%a@]@\nwith@\n%a"*)
          self#reset#expression e  self#case_list l
    | Pexp_let (rf, l, e) ->
        (* pp f "@[<2>let %a%a in@;<1 -2>%a@]" (\*no identation here, a new line*\) *)
        (*   self#rec_flag rf *)
        pp f "@[<2>%a in@;<1 -2>%a@]"
          self#reset#bindings (rf,l)
          self#expression e
    | Pexp_apply (e, l) ->
        (si not (self#sugar_expr f x) alors
          filtre view_fixity_of_exp e avec
          | `Infix s ->
            (filtre l avec
            | [ arg1; arg2 ] ->
                pp f "@[<2>%a@;%s@;%a@]" (* FIXME associativity lable_x_expression_parm*)
                  self#reset#label_x_expression_param  arg1 s  self#label_x_expression_param arg2
            | _ ->
                pp f "@[<2>%a %a@]" self#simple_expr e  (self#list self#label_x_expression_param)  l)
          | `Prefix s ->
              soit s =
                si List.mem s ["~+";"~-";"~+.";"~-."] alors String.sub s 1 (String.length s -1)
                sinon s dans
            (filtre l avec
            |[v] -> pp f "@[<2>%s@;%a@]" s self#label_x_expression_param v
            | _ -> pp f "@[<2>%s@;%a@]" s (self#list self#label_x_expression_param) l  (*FIXME assert false*)
            )
          | _ ->
            pp f "@[<hov2>%a@]" début fonc f (e,l) ->
              pp f "%a@ %a" self#expression2 e
                (self#list self#reset#label_x_expression_param)  l
               (*reset here only because [function,match,try,sequence] are lower priority*)
            fin (e,l))

    | Pexp_construct (li, Some eo)
      quand not (is_simple_construct (view_expr x))-> (* Not efficient FIXME*)
        (filtre view_expr x avec
        | `cons ls -> self#list self#simple_expr f ls ~sep:"@;::@;"
        | `normal ->
            pp f "@[<2>%a@;%a@]" self#longident_loc li
              self#simple_expr  eo
        | _ -> affirme faux)
    | Pexp_setfield (e1, li, e2) ->
        pp f "@[<2>%a.%a@ <-@ %a@]" self#simple_expr  e1  self#longident_loc li self#expression e2;
    | Pexp_ifthenelse (e1, e2, eo) ->
        (* @;@[<2>else@ %a@]@] *)
        soit fmt:(_,_,_)format ="@[<hv0>@[<2>if@ %a@]@;@[<2>then@ %a@]%a@]" dans
        pp f fmt  self#under_ifthenelse#expression e1 self#under_ifthenelse#expression e2
          (fonc f eo -> filtre eo avec
          | Some x -> pp f "@;@[<2>else@;%a@]" self#under_semi#expression  x
          | None -> () (* pp f "()" *)) eo
    | Pexp_sequence _ ->
        soit rec sequence_helper acc = fonction
          | {pexp_desc=Pexp_sequence(e1,e2);_} ->
              sequence_helper (e1::acc) e2
          | v -> List.rev (v::acc) dans
        soit lst = sequence_helper [] x dans
        pp f "@[<hv>%a@]"
          (self#list self#under_semi#expression ~sep:";@;") lst
    | Pexp_new (li) ->
        pp f "@[<hov2>new@ %a@]" self#longident_loc li;
    | Pexp_setinstvar (s, e) ->
        pp f "@[<hov2>%s@ <-@ %a@]" s.txt self#expression e
    | Pexp_override l -> (* FIXME *)
        soit string_x_expression f (s, e) =
          pp f "@[<hov2>%s@ =@ %a@]" s.txt self#expression e dans
        pp f "@[<hov2>{<%a>}@]"
          (self#list string_x_expression  ~sep:";"  )  l;
    | Pexp_letmodule (s, me, e) ->
        pp f "@[<hov2>let@ module@ %s@ =@ %a@ in@ %a@]" s.txt
          self#reset#module_expr me  self#expression e
    | Pexp_assert e ->
        pp f "@[<hov2>assert@ %a@]" self#simple_expr e
    | Pexp_lazy (e) ->
        pp f "@[<hov2>lazy@ %a@]" self#simple_expr e
    | Pexp_poly _ ->
        affirme faux
    | Pexp_open (ovf, lid, e) ->
        pp f "@[<2>let open%s %a in@;%a@]" (override ovf) self#longident_loc lid
          self#expression  e
    | Pexp_variant (l,Some eo) ->
        pp f "@[<2>`%s@;%a@]" l  self#simple_expr eo
    | Pexp_extension (s, arg) ->
      pp f "@[<2>(&%s@ %a)@]" s.txt self#payload arg
    | _ -> self#expression1 f x
  méthode expression1 f x =
    si x.pexp_attributes <> [] alors self#expression f x
    sinon filtre x.pexp_desc avec
    | Pexp_object cs -> pp f "%a" self#class_structure cs
    | _ -> self#expression2 f x
  (* used in [Pexp_apply] *)
  méthode expression2 f x =
    si x.pexp_attributes <> [] alors self#expression f x
    sinon filtre x.pexp_desc avec
    | Pexp_field (e, li) -> pp f "@[<hov2>%a.%a@]" self#simple_expr e self#longident_loc li
    | Pexp_send (e, s) ->  pp f "@[<hov2>%a#%s@]" self#simple_expr e  s

    | _ -> self#simple_expr f x
  méthode simple_expr f x =
    si x.pexp_attributes <> [] alors self#expression f x
    sinon filtre x.pexp_desc avec
    | Pexp_construct _  quand is_simple_construct (view_expr x) ->
        (filtre view_expr x avec
        | `nil -> pp f "[]"
        | `tuple -> pp f "()"
        | `list xs -> pp f "@[<hv0>[%a]@]"  (self#list self#under_semi#expression ~sep:";@;") xs
        | `simple x -> self#longident f x
        | _ -> affirme faux)
    | Pexp_ident li ->
        self#longident_loc f li
        (* (match view_fixity_of_exp x with *)
        (* |`Normal -> self#longident_loc f li *)
        (* | `Prefix _ | `Infix _ -> pp f "( %a )" self#longident_loc li) *)
    | Pexp_constant c -> self#constant f c;
    | Pexp_pack me ->
        pp f "(module@;%a)"  self#module_expr me
    | Pexp_newtype (lid, e) ->
        pp f "fun@;(type@;%s)@;->@;%a"  lid  self#expression  e
    | Pexp_tuple l ->
        pp f "@[<hov2>(%a)@]"  (self#list self#simple_expr  ~sep:",@;")  l
    | Pexp_constraint (e, ct) ->
        pp f "(%a : %a)" self#expression e self#core_type ct
    | Pexp_coerce (e, cto1, ct) ->
        pp f "(%a%a :> %a)" self#expression e
          (self#option self#core_type ~first:" : " ~last:" ") cto1 (* no sep hint*)
          self#core_type ct
    | Pexp_variant (l, None) -> pp f "`%s" l
    | Pexp_record (l, eo) ->
        soit longident_x_expression f ( li, e) =
          filtre e.pexp_desc avec
          |  Pexp_ident {txt;_} quand li.txt = txt ->
              pp f "@[<hov2>%a@]" self#longident_loc li
          | _ ->
              pp f "@[<hov2>%a@;=@;%a@]" self#longident_loc li self#simple_expr e dans
        pp f "@[<hv0>@[<hv2>{@;%a%a@]@;}@]"(* "@[<hov2>{%a%a}@]" *)
          (self#option ~last:" with@;" self#simple_expr) eo
          (self#list longident_x_expression ~sep:";@;")  l
    | Pexp_array (l) ->
        pp f "@[<0>@[<2>[|%a|]@]@]"
          (self#list self#under_semi#simple_expr ~sep:";") l
    | Pexp_while (e1, e2) ->
        soit fmt:(_,_,_)format = "@[<2>while@;%a@;do@;%a@;done@]" dans
        pp f fmt self#expression e1 self#expression e2
    | Pexp_for (s, e1, e2, df, e3) ->
        soit fmt:(_,_,_)format =
          "@[<hv0>@[<hv2>@[<2>for %a =@;%a@;%a%a@;do@]@;%a@]@;done@]" dans
        pp f fmt self#pattern s self#expression e1 self#direction_flag df self#expression e2  self#expression e3
    | _ ->  self#paren vrai self#expression f x

  méthode attributes f l =
    List.iter (self # attribute f) l

  méthode attribute f (s, e) =
    pp f "[@@%s %a]" s.txt self#payload e

  méthode value_description f x =
    pp f "@[<hov2>%a%a@]" self#core_type x.pval_type
      (fonc f x ->
        si x.pval_prim<>[] alors début
          pp f "@ =@ %a"
            (self#list self#constant_string)
            x.pval_prim ;
        fin) x


  méthode exception_declaration f cd =
    pp f "@[<hov2>exception@ %s%a@]" cd.pcd_name.txt
      (fonc f ed -> filtre ed avec
      |[] -> ()
      |_ -> pp f "@ of@ %a" (self#list ~sep:"*" self#core_type) ed) cd.pcd_args

  méthode class_signature f { pcsig_self = ct; pcsig_fields = l ;_} =
    soit class_type_field f x =
      filtre x.pctf_desc avec
      | Pctf_inherit (ct) ->
          pp f "@[<2>inherit@ %a@]" self#class_type ct
      | Pctf_val (s, mf, vf, ct) ->
          pp f "@[<2>val @ %a%a%s@ :@ %a@]"
            self#mutable_flag mf self#virtual_flag vf s  self#core_type  ct
      | Pctf_method (s, pf, vf, ct) ->
          pp f "@[<2>method %a %a%s :@;%a@]"
            self#private_flag pf self#virtual_flag vf s self#core_type ct
      | Pctf_constraint (ct1, ct2) ->
          pp f "@[<2>constraint@ %a@ =@ %a@]"
            self#core_type ct1 self#core_type ct2
      | Pctf_extension _ -> affirme faux
    dans
    pp f "@[<hv0>@[<hv2>object @[<1>%a@]@ %a@]@ end@]"
      (fonc f ct -> filtre ct.ptyp_desc avec
      | Ptyp_any -> ()
      | _ -> pp f "(%a)" self#core_type ct) ct
      (self#list   class_type_field ~sep:"@;") l  ;

  (* call [class_signature] called by [class_signature] *)
  méthode class_type f x =
    filtre x.pcty_desc avec
    | Pcty_signature cs -> self#class_signature f cs;
    | Pcty_constr (li, l) ->
        pp f "%a%a"
          (fonc f l -> filtre l avec
          | [] -> ()
          | _  -> pp f "[%a]@ " (self#list self#core_type ~sep:"," ) l) l
          self#longident_loc li
    | Pcty_arrow (l, co, cl) ->
        pp f "@[<2>%a@;->@;%a@]" (* FIXME remove parens later *)
          self#type_with_label (l,co) self#class_type cl
    | Pcty_extension _ -> affirme faux


  (* [class type a = object end] *)
  méthode class_type_declaration_list f  l =
    soit class_type_declaration f ({pci_params=ls;pci_name={txt;_};_} tel x) =
      pp f "%a%a%s@ =@ %a" self#virtual_flag x.pci_virt
        self#class_params_def ls txt
        self#class_type x.pci_expr dans
    filtre l avec
    | [] -> ()
    | [h] -> pp f "@[<hv2>class type %a@]" class_type_declaration   h
    | _ ->
        pp f "@[<2>class type %a@]"
          (self#list class_type_declaration ~sep:"@]@;@[<2>and@;") l

  méthode class_field f x =
    filtre x.pcf_desc avec
    | Pcf_inherit (ovf, ce, so) ->
        pp f "@[<2>inherit@ %s@ %a%a@]"  (override ovf) self#class_expr ce
          (fonc f so -> filtre so avec
          | None -> ();
          | Some (s) -> pp f "@ as %s" s ) so
    | Pcf_val (s, mf, Cfk_concrete (ovf, e)) ->
        pp f "@[<2>val%s %a%s =@;%a@]" (override ovf)  self#mutable_flag mf
          s.txt  self#expression  e
    | Pcf_method (s, pf, Cfk_virtual ct) ->
        pp f "@[<2>method virtual %a %s :@;%a@]"
          self#private_flag pf s.txt self#core_type  ct
    | Pcf_val (s, mf, Cfk_virtual ct) ->
        pp f "@[<2>val virtual %a%s :@ %a@]"
          self#mutable_flag mf s.txt
          self#core_type  ct
    | Pcf_method (s, pf, Cfk_concrete (ovf, e)) ->
        pp f "@[<2>method%s %a%a@]"
          (override ovf)
          self#private_flag pf
          (fonc f e -> filtre e.pexp_desc avec
          | Pexp_poly (e, Some ct) ->
              pp f "%s :@;%a=@;%a"
                s.txt (self#core_type) ct self#expression e
          | Pexp_poly (e,None) ->
              self#binding f {pvb_pat={ppat_desc=Ppat_var s;ppat_loc=Location.none;ppat_attributes=[]};
                              pvb_expr=e;
                              pvb_attributes=[]}
          | _ ->
              self#expression f e ) e
    | Pcf_constraint (ct1, ct2) ->
        pp f "@[<2>constraint %a =@;%a@]" self#core_type  ct1 self#core_type  ct2
    | Pcf_initializer (e) ->
        pp f "@[<2>initializer@ %a@]" self#expression e
    | Pcf_extension _ -> affirme faux

  méthode class_structure f { pcstr_self = p; pcstr_fields =  l } =
    pp f "@[<hv0>@[<hv2>object %a@;%a@]@;end@]"
      (fonc f p -> filtre p.ppat_desc avec
      | Ppat_any -> ()
      | Ppat_constraint _ -> pp f "%a"  self#pattern  p
      | _ -> pp f "(%a)" self#pattern p) p
      (self#list self#class_field ) l

  méthode class_expr f x =
    filtre x.pcl_desc avec
    | Pcl_structure (cs) ->  self#class_structure f cs ;
    | Pcl_fun (l, eo, p, e) ->
        pp f "fun@ %a@ ->@ %a" self#label_exp (l,eo,p)  self#class_expr e
    | Pcl_let (rf, l, ce) ->
        (* pp f "let@;%a%a@ in@ %a" *)
          pp f "%a@ in@ %a"
          (* self#rec_flag rf *)
          self#bindings  (rf,l)
          self#class_expr ce
    | Pcl_apply (ce, l) ->
        pp f "(%a@ %a)"  self#class_expr ce (self#list self#label_x_expression_param) l
    | Pcl_constr (li, l) ->
        pp f "%a%a"
          (fonc f l-> si l <>[] alors
            pp f "[%a]@ "
              (self#list self#core_type  ~sep:"," ) l ) l
          self#longident_loc li
    | Pcl_constraint (ce, ct) ->
        pp f "(%a@ :@ %a)"
          self#class_expr ce
          self#class_type ct
    | Pcl_extension _ -> affirme faux

  méthode module_type f x =
    filtre x.pmty_desc avec
    | Pmty_ident li ->
        pp f "%a" self#longident_loc li;
    | Pmty_alias li ->
        pp f "(module %a)" self#longident_loc li;
    | Pmty_signature (s) ->
        pp f "@[<hv0>@[<hv2>sig@ %a@]@ end@]" (* "@[<hov>sig@ %a@ end@]" *)
          (self#list self#signature_item  ) s (* FIXME wrong indentation*)
    | Pmty_functor (_, None, mt2) ->
        pp f "@[<hov2>functor () ->@ %a@]" self#module_type mt2 
    | Pmty_functor (s, Some mt1, mt2) ->
        pp f "@[<hov2>functor@ (%s@ :@ %a)@ ->@ %a@]" s.txt
          self#module_type mt1  self#module_type mt2
    | Pmty_with (mt, l) ->
        soit with_constraint f = fonction
          | Pwith_type (li, ({ptype_params= ls ;_} tel td)) ->
              soit ls = List.map fst ls dans
              pp f "type@ %a %a =@ %a"
                (self#list self#type_var_option ~sep:"," ~first:"(" ~last:")")
                ls self#longident_loc li  self#type_declaration  td
          | Pwith_module (li, li2) ->
              pp f "module %a =@ %a" self#longident_loc li self#longident_loc li2;
          | Pwith_typesubst ({ptype_params=ls;_} tel td) ->
              soit ls = List.map fst ls dans
              pp f "type@ %a %s :=@ %a"
                (self#list self#type_var_option ~sep:"," ~first:"(" ~last:")")
                ls td.ptype_name.txt
                self#type_declaration  td
          | Pwith_modsubst (s, li2) ->
              pp f "module %s :=@ %a" s.txt self#longident_loc li2 dans
        (filtre l avec
        | [] -> pp f "@[<hov2>%a@]" self#module_type mt
        | _ -> pp f "@[<hov2>(%a@ with@ %a)@]"
              self#module_type mt (self#list with_constraint ~sep:"@ and@ ") l )
    | Pmty_typeof me ->
        pp f "@[<hov2>module@ type@ of@ %a@]"
          self#module_expr me
    | Pmty_extension _ -> affirme faux

  méthode signature f x =  self#list ~sep:"@\n" self#signature_item f x

  méthode signature_item f x :unit= début
    filtre x.psig_desc avec
    | Psig_type l ->
        self#type_def_list f l
    | Psig_value vd ->
        pp f "@[<2>%a@]"
          (fonc f vd ->
            soit intro = si vd.pval_prim = [] alors "val" sinon "external" dans
            pp f "%s@ %a@ :@ " intro protect_ident vd.pval_name.txt;
            self#value_description f vd;) vd
    | Psig_exception ed ->
        self#exception_declaration f ed
    | Psig_class l ->
        soit class_description f ({pci_params=ls;pci_name={txt;_};_} tel x) =
          pp f "%a%a%s@;:@;%a" (* "@[<2>class %a%a%s@;:@;%a@]" *)
            self#virtual_flag x.pci_virt
            self#class_params_def
            ls
            txt  self#class_type x.pci_expr dans
        pp f  "@[<0>%a@]"
          (fonc f l ->  filtre l avec
            |[]  ->()
            |[x] -> pp f "@[<2>class %a@]" class_description x
            |_ ->
                self#list ~first:"@[<v0>class @[<2>" ~sep:"@]@;and @["
                  ~last:"@]@]" class_description f l)
          l
    | Psig_module {pmd_name; pmd_type={pmty_desc=Pmty_alias alias}} ->
        pp f "@[<hov>module@ %s@ =@ %a@]"
          pmd_name.txt self#longident_loc alias
    | Psig_module pmd ->
        pp f "@[<hov>module@ %s@ :@ %a@]"
          pmd.pmd_name.txt
          self#module_type  pmd.pmd_type
    | Psig_open (ovf, li, _attrs) ->
        pp f "@[<hov2>open%s@ %a@]" (override ovf) self#longident_loc li
    | Psig_include (mt, _attrs) ->
        pp f "@[<hov2>include@ %a@]"
          self#module_type  mt
    | Psig_modtype {pmtd_name=s; pmtd_type=md} ->
        pp f "@[<hov2>module@ type@ %s%a@]"
          s.txt
          (fonc f md -> filtre md avec
          | None -> ()
          | Some mt ->
              pp_print_space f () ;
              pp f "@ =@ %a"  self#module_type mt
          ) md
    | Psig_class_type (l) ->
        self#class_type_declaration_list f l ;
    | Psig_recmodule decls ->
        soit rec  string_x_module_type_list f ?(first=vrai) l =
          filtre l avec
          | [] -> () ;
          | pmd :: tl ->
              si not first alors
                pp f "@ @[<hov2>and@ %s:@ %a@]"
                  pmd.pmd_name.txt self#module_type pmd.pmd_type
              sinon
                pp f "@ @[<hov2>module@ rec@ %s:@ %a@]"
                  pmd.pmd_name.txt self#module_type pmd.pmd_type;
              string_x_module_type_list f ~first:faux tl  dans
        string_x_module_type_list f decls
    | Psig_attribute _
    | Psig_extension _ -> affirme faux
  fin
  méthode module_expr f x =
    filtre x.pmod_desc avec
    | Pmod_structure (s) ->
        pp f "@[<hv2>struct@;@[<0>%a@]@;<1 -2>end@]"
          (self#list self#structure_item  ~sep:"@\n") s;
    | Pmod_constraint (me, mt) ->
        pp f "@[<hov2>(%a@ :@ %a)@]"
          self#module_expr  me
          self#module_type mt
    | Pmod_ident (li) ->
        pp f "%a" self#longident_loc li;
    | Pmod_functor (_, None, me) ->
        pp f "functor ()@;->@;%a" self#module_expr me
    | Pmod_functor (s, Some mt, me) ->
        pp f "functor@ (%s@ :@ %a)@;->@;%a"
          s.txt  self#module_type mt  self#module_expr me
    | Pmod_apply (me1, me2) ->
        pp f "%a(%a)" self#module_expr me1  self#module_expr  me2
    | Pmod_unpack e ->
        pp f "(val@ %a)"  self#expression  e
    | Pmod_extension _ -> affirme faux

  méthode structure f x = self#list ~sep:"@\n" self#structure_item f x

  méthode payload f = fonction
    | PStr x -> self#structure f x
    | PTyp x -> pp f ":"; self#core_type f x
    | PPat (x, None) -> pp f "?"; self#pattern f x
    | PPat (x, Some e) ->
      pp f "?"; self#pattern f x;
      pp f " when "; self#expression f e

  (* transform [f = fun g h -> ..] to [f g h = ... ] could be improved *)
  méthode binding f {pvb_pat=p; pvb_expr=x; pvb_attributes=_} = (* TODO: print attributes *)
    soit rec pp_print_pexp_function f x =
      si x.pexp_attributes <> [] alors pp f "=@;%a" self#expression x
      sinon filtre x.pexp_desc avec
      | Pexp_fun (label, eo, p, e) ->
          si label="" alors
            pp f "%a@ %a" self#simple_pattern p pp_print_pexp_function e
          sinon
            pp f "%a@ %a" self#label_exp (label,eo,p) pp_print_pexp_function e
      | Pexp_newtype (str,e) ->
          pp f "(type@ %s)@ %a" str pp_print_pexp_function e
      | _ -> pp f "=@;%a" self#expression x dans
    si x.pexp_attributes <> [] alors
      pp f "%a@;=@;%a" self#pattern p self#expression x
    sinon filtre (x.pexp_desc,p.ppat_desc) avec
    | ( _ , Ppat_constraint( p ,ty)) -> (* special case for the first*)
        (filtre ty.ptyp_desc avec
        | Ptyp_poly _ ->
            pp f "%a@;:@;%a=@;%a" self#simple_pattern p  self#core_type ty self#expression x
        | _ ->
            pp f "(%a@;:%a)=@;%a" self#simple_pattern p  self#core_type ty self#expression x)
    | Pexp_constraint (e,t1),Ppat_var {txt;_} ->
        pp f "%s:@ %a@;=@;%a" txt self#core_type t1  self#expression e
    | (_, Ppat_var _) ->
        pp f "%a@ %a" self#simple_pattern p pp_print_pexp_function x
    | _ ->
        pp f "%a@;=@;%a" self#pattern p self#expression x
  (* [in] is not printed *)
  méthode bindings f (rf,l) =
    début filtre l avec
    | [] -> ()
    | [x] -> pp f "@[<2>let %a%a@]" self#rec_flag rf self#binding x
    | x::xs ->
        (* pp f "@[<hv0>let %a@[<2>%a%a@]" *)
        (* FIXME the indentation is not good see [Insert].ml*)
        pp f "@[<hv0>@[<2>let %a%a%a@]"
          self#rec_flag rf  self#binding x
          (fonc f l -> filtre l avec
          | [] -> affirme faux
          | [x] ->
              pp f
                (* "@]@;and @[<2>%a@]" *)
                "@]@;@[<2>and %a@]"
                self#binding x
          | xs ->
              self#list self#binding
                (* ~first:"@]@;and @[<2>" *)
                ~first:"@]@;@[<2>and "
                (* ~sep:"@]@;and @[<2>" *)
                ~sep:"@]@;@[<2>and "
                ~last:"@]" f xs )  xs
    fin

  méthode structure_item f x = début
    filtre x.pstr_desc avec
    | Pstr_eval (e, _attrs) ->
        pp f "@[<hov2>let@ _ =@ %a@]" self#expression e
    | Pstr_type [] -> affirme faux
    | Pstr_type l  -> self#type_def_list f l
    | Pstr_value (rf, l) -> (* pp f "@[<hov2>let %a%a@]"  self#rec_flag rf self#bindings l *)
        pp f "@[<2>%a@]" self#bindings (rf,l)
    | Pstr_exception ed -> self#exception_declaration f ed
    | Pstr_module x ->
        soit rec module_helper me = filtre me.pmod_desc avec
        | Pmod_functor(s,mt,me) ->
            si mt = None alors pp f "()"
            sinon Misc.may (pp f "(%s:%a)" s.txt self#module_type) mt;
            module_helper me
        | _ -> me dans
        pp f "@[<hov2>module %s%a@]"
          x.pmb_name.txt
          (fonc f me ->
            soit me = module_helper me  dans
            (filtre me.pmod_desc avec
            | Pmod_constraint
                (me,
                 ({pmty_desc=(Pmty_ident (_)
            | Pmty_signature (_));_} tel mt)) ->
                pp f " :@;%a@;=@;%a@;"  self#module_type mt self#module_expr  me
            | _ ->
                pp f " =@ %a"  self#module_expr  me 
            )) x.pmb_expr
    | Pstr_open (ovf, li, _attrs) ->
        pp f "@[<2>open%s@;%a@]" (override ovf) self#longident_loc li;
    | Pstr_modtype {pmtd_name=s; pmtd_type=md} ->
        pp f "@[<hov2>module@ type@ %s%a@]"
          s.txt
          (fonc f md -> filtre md avec
          | None -> ()
          | Some mt ->
              pp_print_space f () ;
              pp f "@ =@ %a"  self#module_type mt
          ) md
    | Pstr_class l ->
        soit class_declaration f  (* for the second will be changed to and FIXME*)
            ({pci_params=ls;
              pci_name={txt;_};
              pci_virt;
              pci_expr={pcl_desc;_};
              _ } tel x) =
          soit rec  class_fun_helper f e = filtre e.pcl_desc avec
          | Pcl_fun (l, eo, p, e) ->
              self#label_exp f (l,eo,p);
              class_fun_helper f e
          | _ -> e dans
          pp f "%a%a%s %a"  self#virtual_flag pci_virt self#class_params_def ls txt
            (fonc f _ ->
              soit ce =
                (filtre pcl_desc avec
                | Pcl_fun _ ->
                    class_fun_helper f x.pci_expr;
                | _ -> x.pci_expr) dans
              soit ce =
                (filtre ce.pcl_desc avec
                | Pcl_constraint (ce, ct) ->
                    pp f ": @[%a@] " self#class_type  ct ;
                    ce
                | _ -> ce ) dans
              pp f "=@;%a" self#class_expr ce ) x dans
        (filtre l avec
        | [] -> ()
        | [x] -> pp f "@[<2>class %a@]" class_declaration x
        | xs ->  self#list
              ~first:"@[<v0>class @[<2>"
              ~sep:"@]@;and @["
              ~last:"@]@]" class_declaration f xs)
    | Pstr_class_type (l) ->
        self#class_type_declaration_list f l ;
    | Pstr_primitive vd ->
        pp f "@[<hov2>external@ %a@ :@ %a@]" protect_ident vd.pval_name.txt
          self#value_description  vd
    | Pstr_include (me, _attrs) ->
        pp f "@[<hov2>include@ %a@]"  self#module_expr  me
    | Pstr_exn_rebind (s, li, _attrs) ->        (* todo: check this *)
        pp f "@[<hov2>exception@ %s@ =@ %a@]" s.txt self#longident_loc li
    | Pstr_recmodule decls -> (* 3.07 *)
        soit aux f = fonction
          | {pmb_name = s; pmb_expr={pmod_desc=Pmod_constraint (expr, typ)}} ->
              pp f "@[<hov2>and@ %s:%a@ =@ %a@]"
              s.txt self#module_type typ self#module_expr expr
          | _ -> affirme faux
        dans
        début filtre decls avec
        | {pmb_name = s; pmb_expr={pmod_desc=Pmod_constraint (expr, typ)}} :: l2 ->
            pp f "@[<hv>@[<hov2>module@ rec@ %s:%a@ =@ %a@]@ %a@]"
              s.txt
              self#module_type typ
              self#module_expr expr
              (fonc f l2 -> List.iter (aux f) l2) l2
        | _ -> affirme faux
        fin
    | Pstr_attribute _ -> ()
    | Pstr_extension _ -> affirme faux
  fin
  méthode type_param f (opt, a) =
    pp f "%s%a" (type_variance a ) self#type_var_option opt
          (* shared by [Pstr_type,Psig_type]*)
  méthode  type_def_list f  l =
    soit aux f ({ptype_name = s; ptype_params;ptype_kind;ptype_manifest;_} tel td) =
      pp f "%a%s%a"
        (fonc f l -> filtre l avec
        |[] -> ()
        | _ ->  pp f "%a@;" (self#list self#type_param ~first:"(" ~last:")" ~sep:",") l)
        ptype_params s.txt
        (fonc f td ->début filtre ptype_kind, ptype_manifest avec
        | Ptype_abstract, None -> ()
        | _ , _ -> pp f " =@;" fin;
          pp f "%a" self#type_declaration td ) td  dans
    filtre l avec
    | [] -> () ;
    | [x] -> pp f "@[<2>type %a@]" aux x
    | xs -> pp f "@[<v>@[<2>type %a"
          (self#list aux ~sep:"@]@,@[<2>and " ~last:"@]@]") xs
          (* called by type_def_list *)
  méthode type_declaration f x = début
    soit  type_variant_leaf f  {pcd_name; pcd_args; pcd_res; pcd_loc=_} = filtre pcd_res avec
    |None ->
        pp f "@\n|@;%s%a" pcd_name.txt
          (fonc f l -> filtre l avec
          | [] -> ()
          | _ -> pp f "@;of@;%a" (self#list self#core_type1 ~sep:"*@;") l) pcd_args
    |Some x ->
        pp f "@\n|@;%s:@;%a" pcd_name.txt
          (self#list self#core_type1 ~sep:"@;->@;") (pcd_args@[x]) dans
    pp f "%a%a@ %a"
      (fonc f x -> filtre (x.ptype_manifest,x.ptype_kind,x.ptype_private) avec
      | (None,_,Public) ->  pp f "@;"
      | (None,Ptype_abstract,Private) -> pp f "@;" (* private type without print*)
      | (None,_,Private) -> pp f "private@;"
      | (Some y, Ptype_abstract,Private) ->
          pp f "private@;%a" self#core_type y;
      | (Some y, _, Private) ->
          pp f "%a = private@;" self#core_type y
      | (Some y,Ptype_abstract, Public) ->  self#core_type f y;
      | (Some y, _,Public) -> début
          pp f "%a =@;" self#core_type y (* manifest types*)
      fin) x
      (fonc f x -> filtre x.ptype_kind avec
        (*here only normal variant types allowed here*)
      | Ptype_variant xs ->
          pp f "%a"
            (self#list ~sep:"" type_variant_leaf) xs
      | Ptype_abstract -> ()
      | Ptype_record l ->
          soit type_record_field f pld =
            pp f "@[<2>%a%s:@;%a@]" self#mutable_flag pld.pld_mutable pld.pld_name.txt self#core_type pld.pld_type dans
          pp f "{@\n%a}"
            (self#list type_record_field ~sep:";@\n" )  l ;
      ) x
      (self#list
         (fonc f (ct1,ct2,_) ->
           pp f "@[<hov2>constraint@ %a@ =@ %a@]"
             self#core_type ct1 self#core_type ct2 ))  x.ptype_cstrs  ;
      (* TODO: attributes *)
  fin
  méthode case_list f l : unit =
    soit aux f {pc_lhs; pc_guard; pc_rhs} =
      pp f "@;| @[<2>%a%a@;->@;%a@]"
        self#pattern pc_lhs (self#option self#expression ~first:"@;when@;") pc_guard self#under_pipe#expression pc_rhs dans
    self#list aux f l ~sep:""
  méthode label_x_expression_param f (l,e) =
    filtre l avec
    | ""  -> self#expression2 f e ; (* level 2*)
    | lbl ->
        soit simple_name = filtre e.pexp_desc avec
        | Pexp_ident {txt=Lident l;_} -> Some l
        | _ -> None dans
        si  lbl.[0] = '?' alors
          soit str = String.sub lbl 1 (String.length lbl-1) dans
          si Some str = simple_name alors
            pp f "%s" lbl
          sinon
            pp f "%s:%a" lbl self#simple_expr e
        sinon
          si Some lbl = simple_name alors
            pp f "~%s" lbl
          sinon
            pp f "~%s:%a" lbl self#simple_expr e

  méthode directive_argument f x =
    (filtre x avec
    | Pdir_none -> ()
    | Pdir_string (s) -> pp f "@ %S" s
    | Pdir_int (i) -> pp f "@ %d" i
    | Pdir_ident (li) -> pp f "@ %a" self#longident li
    | Pdir_bool (b) -> pp f "@ %s" (string_of_bool b))

  méthode toplevel_phrase f x =
    filtre x avec
    | Ptop_def (s) ->
        pp_open_hvbox f 0;
        self#list self#structure_item f s ;
        pp_close_box f ();
    | Ptop_dir (s, da) ->
        pp f "@[<hov2>#%s@ %a@]" s self#directive_argument da
fin;;


soit default = nouv printer ()


soit toplevel_phrase f x =
  filtre x avec
  | Ptop_def (s) ->pp f "@[<hov0>%a@]"  (default#list default#structure_item) s
   (* pp_open_hvbox f 0; *)
   (* pp_print_list structure_item f s ; *)
   (* pp_close_box f (); *)
  | Ptop_dir (s, da) ->
   pp f "@[<hov2>#%s@ %a@]" s default#directive_argument da
   (* pp f "@[<hov2>#%s@ %a@]" s directive_argument da *)

soit expression f x =
  pp f "@[%a@]" default#expression x


soit string_of_expression x =
  ignore (flush_str_formatter ()) ;
  soit f = str_formatter dans
  default#expression f x ;
  flush_str_formatter () ;;
soit string_of_structure x =
  ignore (flush_str_formatter ());
  soit f = str_formatter dans
  default#structure f x;
  flush_str_formatter ();;

soit top_phrase f x =
  pp_print_newline f () ;
  toplevel_phrase f x;
  pp f ";;" ;
  pp_print_newline f ();;

soit core_type=default#core_type
soit pattern=default#pattern
soit signature=default#signature
soit structure=default#structure
