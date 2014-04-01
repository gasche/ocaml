(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Jerome Vouillon, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Misc
ouvre Primitive
ouvre Asttypes
ouvre Longident
ouvre Lambda

(* Get oo primitives identifiers *)

soit oo_prim name =
  essaie
    transl_normal_path
      (fst (Env.lookup_value (Ldot (Lident "CamlinternalOO", name)) Env.empty))
  avec Not_found ->
    fatal_error ("Primitive " ^ name ^ " introuvable.")

(* Share blocks *)

soit consts : (structured_constant, Ident.t) Hashtbl.t = Hashtbl.create 17

soit share c =
  filtre c avec
    Const_block (n, l) quand l <> [] ->
      début essaie
        Lvar (Hashtbl.find consts c)
      avec Not_found ->
        soit id = Ident.create "shared" dans
        Hashtbl.add consts c id;
        Lvar id
      fin
  | _ -> Lconst c

(* Collect labels *)

soit cache_required = ref faux
soit method_cache = ref lambda_unit
soit method_count = ref 0
soit method_table = ref []

soit meth_tag s = Lconst(Const_base(Const_int(Btype.hash_variant s)))

soit next_cache tag =
  soit n = !method_count dans
  incr method_count;
  (tag, [!method_cache; Lconst(Const_base(Const_int n))])

soit rec is_path = fonction
    Lvar _ | Lprim (Pgetglobal _, []) | Lconst _ -> vrai
  | Lprim (Pfield _, [lam]) -> is_path lam
  | Lprim ((Parrayrefu _ | Parrayrefs _), [lam1; lam2]) ->
      is_path lam1 && is_path lam2
  | _ -> faux

soit meth obj lab =
  soit tag = meth_tag lab dans
  si not (!cache_required && !Clflags.native_code) alors (tag, []) sinon
  si not (is_path obj) alors next_cache tag sinon
  essaie
    soit r = List.assoc obj !method_table dans
    essaie
      (tag, List.assoc tag !r)
    avec Not_found ->
      soit p = next_cache tag dans
      r := p :: !r;
      p
  avec Not_found ->
    soit p = next_cache tag dans
    method_table := (obj, ref [p]) :: !method_table;
    p

soit reset_labels () =
  Hashtbl.clear consts;
  method_count := 0;
  method_table := []

(* Insert labels *)

soit string s = Lconst (Const_base (Const_string (s, None)))
soit int n = Lconst (Const_base (Const_int n))

soit prim_makearray =
  { prim_name = "caml_make_vect"; prim_arity = 2; prim_alloc = vrai;
    prim_native_name = ""; prim_native_float = faux }

(* Also use it for required globals *)
soit transl_label_init expr =
  soit expr =
    Hashtbl.fold
      (fonc c id expr -> Llet(Alias, id, Lconst c, expr))
      consts expr
  dans
  soit expr =
    List.fold_right
      (fonc id expr -> Lsequence(Lprim(Pgetglobal id, []), expr))
      (Env.get_required_globals ()) expr
  dans
  Env.reset_required_globals ();
  reset_labels ();
  expr

soit transl_store_label_init glob size f arg =
  method_cache := Lprim(Pfield size, [Lprim(Pgetglobal glob, [])]);
  soit expr = f arg dans
  soit (size, expr) =
    si !method_count = 0 alors (size, expr) sinon
    (size+1,
     Lsequence(
     Lprim(Psetfield(size, faux),
           [Lprim(Pgetglobal glob, []);
            Lprim (Pccall prim_makearray, [int !method_count; int 0])]),
     expr))
  dans
  (size, transl_label_init expr)

(* Share classes *)

soit wrapping = ref faux
soit top_env = ref Env.empty
soit classes = ref []
soit method_ids = ref IdentSet.empty

soit oo_add_class id =
  classes := id :: !classes;
  (!top_env, !cache_required)

soit oo_wrap env req f x =
  si !wrapping alors
    si !cache_required alors f x sinon
    essaie cache_required := vrai; soit lam = f x dans cache_required := faux; lam
    avec exn -> cache_required := faux; raise exn
  sinon essaie
    wrapping := vrai;
    cache_required := req;
    top_env := env;
    classes := [];
    method_ids := IdentSet.empty;
    soit lambda = f x dans
    soit lambda =
      List.fold_left
        (fonc lambda id ->
          Llet(StrictOpt, id,
               Lprim(Pmakeblock(0, Mutable),
                     [lambda_unit; lambda_unit; lambda_unit]),
               lambda))
        lambda !classes
    dans
    wrapping := faux;
    top_env := Env.empty;
    lambda
  avec exn ->
    wrapping := faux;
    top_env := Env.empty;
    raise exn
