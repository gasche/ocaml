open Lambda
open Clambda

(* Function call specialisation:
   This section is done to estimate wether a value (float) will be
   used boxed or not and decide if it should be passed as boxed
   parameter to a function or not.
   This is also done for return values.

   This is very conservative: it should never be worse that without
   this optimisation. i.e. avoid taking parameter unboxed if it is
   possible to need them boxed inside the body of the function *)

module IdentMap =
  Map.Make(struct
    type t = Ident.t
    let compare = compare
  end)

(* Identify a parameter position: i.e. a function and its position *)
type param_pos = (function_label * int)

(* Describes variable usage: wethere they are forced to be used boxed *)
type param_constraint =
  | Used_boxed
  (* The variable is known to be needed in boxed version: put inside
     a structure, passed to a polymorphic function, ... *)
  | Used_as_param of param_pos list
  (* No strong constraint, but known to be passed as parameter
     to the given functions *)

let variables_boxing_constraints u =
  let tbl = ref IdentMap.empty in
  let set_var v = function
    | Uvar id ->
       tbl := IdentMap.add id v !tbl
    | _ -> () in
  let add_var arg = set_var Used_boxed arg in
  let add_param_var desc i = function
    | Uvar id ->
       let prev =
         try IdentMap.find id !tbl with
         | Not_found -> Used_as_param []
       in
       begin match prev with
             | Used_boxed -> ()
             | Used_as_param l ->
                tbl := IdentMap.add id (Used_as_param ((desc,i)::l)) !tbl
       end
    | _ -> ()
  in
  let rec aux = function
    | Ugeneric_apply (fn, params, _) ->
       aux fn;
       List.iter aux params;
       List.iter add_var params
    | Udirect_apply (desc, params, _) ->
       List.iter aux params;
       let fun_params =
         let l = List.map snd desc.fun_params in
         let rec map_kind param kind = match param,kind with
           | [], [] -> []
           | [], _ -> assert false (* possible ? *)
           | t::q, [] -> Vaddr :: (map_kind q [])
           | t::q1, kind::q2 -> kind :: (map_kind q1 q2)
         in
         map_kind params l in
       let args = List.combine params fun_params in
       let mark_params i (arg, kind) =
         match kind with
         | Vaddr -> add_var arg
         | Vfloat
         | Vbint _
         | Vint ->
            if desc.fun_specialisation_done
            then ()
            else add_param_var desc.fun_label i arg in
       List.iteri mark_params args
    | Usend (_, p1, p2, params, _) ->
       aux p1;
       aux p2;
       List.iter aux params;
       List.iter add_var params
    | Ulet (id, lam1, lam2) ->
       aux lam1;
       aux lam2;
       begin try
         let v = IdentMap.find id !tbl in
         set_var v lam1
       with Not_found -> () end
    | Uletrec (id_lst, lam) ->
       aux lam;
       List.iter (fun (id, lam1) ->
         try
           let v = IdentMap.find id !tbl in
           set_var v lam1
         with Not_found -> ()) id_lst
    | Uvar _
    | Uconst _ -> ()
    | Uclosure (_, lst) ->
       List.iter aux lst;
    | Uswitch (lam, uswitch) ->
       aux lam;
       Array.iter aux uswitch.us_actions_consts;
       Array.iter aux uswitch.us_actions_blocks
    | Ustaticfail (_, lst) ->
       List.iter aux lst
    | Ucatch (nfail, ids, body, handler) ->
       aux body;
       aux handler;
    | Uoffset (lam, _)
    | Uassign (_, lam) ->
       aux lam
    | Utrywith (lam1, _, lam2)
    | Usequence (lam1, lam2)
    | Uwhile (lam1, lam2) ->
       aux lam1; aux lam2
    | Uifthenelse (lam1, lam2, lam3)
    | Ufor (_, lam1, lam2, _, lam3) ->
       aux lam1; aux lam2; aux lam3
    | Uprim (prim, params, _) ->
       begin
         match prim with
         | Psetglobal _
         | Psetfield _ -> List.iter add_var params
         | Pmakeblock _ -> List.iter add_var params
         | Pccall desc ->
            if not desc.Primitive.prim_native_float
            then List.iter add_var params
         | _ -> ()
       end;
      List.iter aux params
  in
  aux u;
  !tbl

(* Describes wether return value are built boxed *)
type return_constraint =
  | Returned_unboxed (* the value is build as a boxed value.
    ex: extracted from a tuple, returned from a polymorphic function, etc *)
  | Returned_boxed (* the value is build as an unboxed value.
    ex: result of arithmetic expression, etc *)
  | Returned_from of function_label list
  (* No strong constraint is known but the value can be returned by
     the listed functions *)

let merge_return_info v1 v2 = match v1,v2 with
  | Returned_boxed, _
  | _, Returned_boxed -> Returned_boxed
  | Returned_unboxed, t
  | t, Returned_unboxed -> t
  | Returned_from l1, Returned_from l2 -> Returned_from (l1@l2)

let return_boxing_constraints fun_params u =
  let tbl = ref IdentMap.empty in
  let rec aux = function
    | Ugeneric_apply (_, _, _) ->
       Returned_boxed
    | Udirect_apply (desc, _, _) ->
       begin match desc.fun_return with
             | Vaddr -> Returned_boxed
             | Vfloat | Vbint _ | Vint -> Returned_from [desc.fun_label] end
    | Usend (_, p1, p2, params, _) ->
       Returned_boxed
    | Ulet (id, lam1, lam2) ->
       let r = aux lam1 in
       tbl := IdentMap.add id r !tbl;
       aux lam2
    | Uletrec (id_lst, lam) ->
       aux lam
    | Uvar id ->
      begin try IdentMap.find id !tbl
      with Not_found ->
        try match IdentMap.find id fun_params with
        | Vaddr -> Returned_boxed
        | Vint | Vfloat | Vbint _ -> Returned_unboxed
        with Not_found -> Returned_boxed end
    | Uconst _ -> Returned_boxed
    | Uclosure (_, lst) -> Returned_boxed
    | Uswitch (lam, uswitch) ->
       let a1 = Array.map aux uswitch.us_actions_consts in
       let a2 = Array.map aux uswitch.us_actions_blocks in
       let r = Array.fold_left merge_return_info Returned_unboxed a1 in
       Array.fold_left merge_return_info r a2
    | Ustaticfail (_, _) ->
       Returned_boxed
    | Ucatch (_, _, body, handler) ->
       merge_return_info (aux body) (aux handler)
    | Uoffset (lam, _)
    | Uassign (_, lam) ->
       Returned_boxed
    | Utrywith (lam1, _, lam2) ->
       merge_return_info (aux lam1) (aux lam2)
    | Usequence (lam1, lam2) ->
       aux lam2
    | Uwhile (lam1, lam2) ->
       Returned_boxed
    | Uifthenelse (lam1, lam2, lam3) ->
       merge_return_info (aux lam2) (aux lam3)
    | Ufor (_, lam1, lam2, _, lam3) ->
       Returned_boxed
    | Uprim (prim, params, _) ->
       begin
         match prim with
         | Pidentity ->
           (* allow forcing *)
           Returned_unboxed
         | Pbintofint _ | Pintofbint _ | Pcvtbint _ | Pnegbint _ | Paddbint _
         | Psubbint _ | Pmulbint _ | Pdivbint _ | Pmodbint _ | Pandbint _
         | Porbint _  | Pxorbint _ | Plslbint _ | Plsrbint _ | Pasrbint _
         | Pbintcomp _
         | Pnegint | Paddint | Psubint | Pmulint | Pdivint | Pmodint
         | Pandint | Porint | Pxorint | Plslint | Plsrint | Pasrint
         | Pfloatofint | Pnegfloat | Pabsfloat | Paddfloat | Psubfloat
         | Pmulfloat | Pdivfloat ->
           Returned_unboxed
         | Pfloatfield _
         | Pstring_load_16 _ | Pstring_load_32 _ | Pstring_load_64 _
         | Pbigstring_load_16 _ | Pbigstring_load_32 _
         | Pbigstring_load_64 _ ->
            Returned_unboxed
         | Pbigarrayref(_,_,kind,_) ->
           begin match kind with
           | Pbigarray_unknown | Pbigarray_complex32 | Pbigarray_complex64 ->
             Returned_boxed
           | Pbigarray_float32 | Pbigarray_float64
           | Pbigarray_sint8 | Pbigarray_uint8
           | Pbigarray_sint16 | Pbigarray_uint16
           | Pbigarray_int32 | Pbigarray_int64
           | Pbigarray_caml_int | Pbigarray_native_int ->
             Returned_unboxed
           end
         | Pccall desc ->
            if desc.Primitive.prim_native_float
            then Returned_unboxed
            else Returned_boxed
         | _ -> Returned_boxed
       end
  in
  aux u

type param_usage =
  | Known of value_kind
  | Depend of param_pos list

type allow_spec =
  | No_const
  | Some_const

type function_unbox_usage = param_usage array

let param_usage_table : (function_label, function_unbox_usage) Hashtbl.t =
  Hashtbl.create 0
let param_type_table : (param_pos, allow_spec option) Hashtbl.t = Hashtbl.create 0
let return_usage_table : (function_label, return_constraint) Hashtbl.t =
  Hashtbl.create 0
let return_type_table : (function_label, allow_spec option) Hashtbl.t = Hashtbl.create 0

let clear_tables () =
  Hashtbl.clear param_usage_table;
  Hashtbl.clear param_type_table;
  Hashtbl.clear return_usage_table;
  Hashtbl.clear return_type_table

let find_boxed_usage (fun_label,i) =
  try
    let usage = Hashtbl.find param_usage_table fun_label in
    usage.(i)
  with
    | Not_found ->
       Printf.eprintf "unregistered: %s %i\n%!" fun_label i;
       assert false (* must be registered before searching ! *)

let find_return_usage fun_label =
  try
    Hashtbl.find return_usage_table fun_label
  with
    | Not_found ->
       Printf.eprintf "%s\n%!" fun_label;
       assert false (* must be registered before searching ! *)

let spec_kind = function
  | Vaddr -> false
  | Vfloat -> true
  | Vint -> false
  (* could be activated if some optimisations were added to Cmmgen *)
  | Vbint bi ->
    match bi with
    | Pnativeint
    | Pint32 -> true
    | Pint64 ->
      (* it is not possible to specialise for int64 on 32 bit arch *)
      (Arch.size_int = 8)

(* Find wether there are some boxing constraints on a function
   parameter. The constraints can come from strong ones inside the
   body of the function or a weak ones when the variable is used as
   parameter for another mutually recursive function. *)
let rec find_param_type (param:param_pos) =
  try Hashtbl.find param_type_table param with
  | Not_found ->
     match find_boxed_usage param with
     | Known Vaddr ->
        Some Some_const
     | Known (Vint | Vfloat | Vbint _) ->
        Some No_const
     | Depend l ->
        Hashtbl.add param_type_table param None;
        let rec iter ret = function
          | [] -> ret
          | t::q ->
             match find_param_type t with
             | None -> iter None q
             | Some No_const -> iter ret q
             | Some Some_const -> Some Some_const
        in
        match iter (Some No_const) l with
        | Some _ as v ->
           Hashtbl.replace param_type_table param v;
           v
        | None -> None

let rec find_return_type func =
  try Hashtbl.find return_type_table func with
  | Not_found ->
     match find_return_usage func with
     | Returned_boxed ->
        Some Some_const
     | Returned_unboxed ->
        Some No_const
     | Returned_from l ->
       Hashtbl.add return_type_table func None;
       let rec iter ret = function
         | [] -> ret
         | t::q ->
            match find_return_type t with
            | None -> iter None q
            | Some No_const -> iter ret q
            | Some Some_const -> Some Some_const
       in
       match iter (Some No_const) l with
       | Some _ as v ->
          Hashtbl.replace return_type_table func v;
          v
       | None -> None

(* Register boxing constraints of parameters of a function. When
   calling find_param_type, all functions called must have been
   registered with add_fun_param_constraints *)
let add_fun_param_constraints (clos,fundesc) =
  let tbl = variables_boxing_constraints clos.body in
  let f = function
    | (_,Vaddr) -> Known Vaddr
    | (id, (Vfloat|Vint|Vbint _ as kind)) ->
       if spec_kind kind
       then
         try
           match IdentMap.find id tbl with
           | Used_boxed -> Known Vaddr
           | Used_as_param l -> Depend l
         with
         | Not_found -> Known kind
       else Known Vaddr
  in
  let params = List.map f fundesc.fun_params in
  Hashtbl.add param_usage_table fundesc.fun_label (Array.of_list params)

(* Register boxing constraints of the return value of a function. When
   calling find_return_type, all functions called must have been
   registered with add_fun_return_constraints. *)
let add_fun_return_constraints (clos,fundesc) =
  let ret =
    if spec_kind fundesc.fun_return
    then
      let param_tbl = List.fold_left
          (fun map (id,kind) -> IdentMap.add id kind map)
          IdentMap.empty clos.params in
      return_boxing_constraints param_tbl clos.body
    else Returned_boxed
  in
  Hashtbl.add return_usage_table fundesc.fun_label ret

let specialised fundecl =
  match fundecl.return with
  | Vint | Vfloat | Vbint _ -> true
  | Vaddr ->
     List.exists (function (_, Vint)
                         | (_, Vbint _)
                         | (_, Vfloat) -> true
                         | (_, Vaddr) -> false)
                 fundecl.params

let specialised' fundesc =
  match fundesc.fun_return with
  | Vint | Vfloat | Vbint _ -> true
  | Vaddr ->
     List.exists (function (_, Vint)
                         | (_, Vbint _)
                         | (_, Vfloat) -> true
                         | (_, Vaddr) -> false)
                 fundesc.fun_params

let param_boxing (clos,fundesc) =
  let rec last = function
    | [] -> assert false
    | [v] -> v
    | t::q -> last q
  in
  let params =
    List.mapi (fun i (id,t) ->
               let new_t =
                 match find_param_type (fundesc.fun_label,i) with
                 | Some Some_const -> Vaddr
                 | Some No_const
                 | None -> t in
               id, new_t)
              fundesc.fun_params in
  let clos_params =
    if fundesc.fun_closed
    then params
    else params @ [last clos.params] (* environment *) in
  fundesc.fun_params <- params;
  clos.params <- clos_params

let return_boxing (clos,fundesc) =
  let return =
    match find_return_type fundesc.fun_label with
    | Some Some_const -> Vaddr
    | Some No_const
    | None -> fundesc.fun_return in
  fundesc.fun_return <- return;
  clos.return <- return

let function_constraints module_functions =
  List.iter add_fun_param_constraints module_functions;
  List.iter param_boxing module_functions;
  List.iter add_fun_return_constraints module_functions;
  List.iter return_boxing module_functions;
  List.iter (fun (_,desc) -> desc.fun_specialisation_done <- true)
            module_functions;
  clear_tables ()
