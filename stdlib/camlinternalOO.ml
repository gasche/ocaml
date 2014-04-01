(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Jerome Vouillon, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

ouvre Obj

(**** Object representation ****)

dehors set_id: 'a -> 'a = "caml_set_oo_id" "noalloc"

(**** Object copy ****)

soit copy o =
  soit o = (Obj.obj (Obj.dup (Obj.repr o))) dans
  set_id o

(**** Compression options ****)
(* Parameters *)
type params = {
    modifiable compact_table : bool;
    modifiable copy_parent : bool;
    modifiable clean_when_copying : bool;
    modifiable retry_count : int;
    modifiable bucket_small_size : int
  }

soit params = {
  compact_table = vrai;
  copy_parent = vrai;
  clean_when_copying = vrai;
  retry_count = 3;
  bucket_small_size = 16
}

(**** Parameters ****)

soit step = Sys.word_size / 16
soit initial_object_size = 2

(**** Items ****)

type item = DummyA | DummyB | DummyC de int
soit _ = [DummyA; DummyB; DummyC 0] (* to avoid warnings *)

soit dummy_item = (magic () : item)

(**** Types ****)

type tag
type label = int
type closure = item
type t = DummyA | DummyB | DummyC de int
soit _ = [DummyA; DummyB; DummyC 0] (* to avoid warnings *)

type obj = t array
dehors ret : (obj -> 'a) -> closure = "%identity"

(**** Labels ****)

soit public_method_label s : tag =
  soit accu = ref 0 dans
  pour i = 0 à String.length s - 1 faire
    accu := 223 * !accu + Char.code s.[i]
  fait;
  (* reduce to 31 bits *)
  accu := !accu etl (1 dgl 31 - 1);
  (* make it signed for 64 bits architectures *)
  soit tag = si !accu > 0x3FFFFFFF alors !accu - (1 dgl 31) sinon !accu dans
  (* Printf.eprintf "%s = %d\n" s tag; flush stderr; *)
  magic tag

(**** Sparse array ****)

module Vars =
  Map.Make(struct type t = string soit compare (x:t) y = compare x y fin)
type vars = int Vars.t

module Meths =
  Map.Make(struct type t = string soit compare (x:t) y = compare x y fin)
type meths = label Meths.t
module Labs =
  Map.Make(struct type t = label soit compare (x:t) y = compare x y fin)
type labs = bool Labs.t

(* The compiler assumes that the first field of this structure is [size]. *)
type table =
 { modifiable size: int;
   modifiable methods: closure array;
   modifiable methods_by_name: meths;
   modifiable methods_by_label: labs;
   modifiable previous_states:
     (meths * labs * (label * item) list * vars *
      label list * string list) list;
   modifiable hidden_meths: (label * item) list;
   modifiable vars: vars;
   modifiable initializers: (obj -> unit) list }

soit dummy_table =
  { methods = [| dummy_item |];
    methods_by_name = Meths.empty;
    methods_by_label = Labs.empty;
    previous_states = [];
    hidden_meths = [];
    vars = Vars.empty;
    initializers = [];
    size = 0 }

soit table_count = ref 0

(* dummy_met should be a pointer, so use an atom *)
soit dummy_met : item = obj (Obj.new_block 0 0)
(* if debugging is needed, this could be a good idea: *)
(* let dummy_met () = failwith "Undefined method" *)

soit rec fit_size n =
  si n <= 2 alors n sinon
  fit_size ((n+1)/2) * 2

soit new_table pub_labels =
  incr table_count;
  soit len = Array.length pub_labels dans
  soit methods = Array.create (len*2+2) dummy_met dans
  methods.(0) <- magic len;
  methods.(1) <- magic (fit_size len * Sys.word_size / 8 - 1);
  pour i = 0 à len - 1 faire methods.(i*2+3) <- magic pub_labels.(i) fait;
  { methods = methods;
    methods_by_name = Meths.empty;
    methods_by_label = Labs.empty;
    previous_states = [];
    hidden_meths = [];
    vars = Vars.empty;
    initializers = [];
    size = initial_object_size }

soit resize array new_size =
  soit old_size = Array.length array.methods dans
  si new_size > old_size alors début
    soit new_buck = Array.create new_size dummy_met dans
    Array.blit array.methods 0 new_buck 0 old_size;
    array.methods <- new_buck
 fin

soit put array label element =
  resize array (label + 1);
  array.methods.(label) <- element

(**** Classes ****)

soit method_count = ref 0
soit inst_var_count = ref 0

(* type t *)
type meth = item

soit new_method table =
  soit index = Array.length table.methods dans
  resize table (index + 1);
  index

soit get_method_label table name =
  essaie
    Meths.find name table.methods_by_name
  avec Not_found ->
    soit label = new_method table dans
    table.methods_by_name <- Meths.add name label table.methods_by_name;
    table.methods_by_label <- Labs.add label vrai table.methods_by_label;
    label

soit get_method_labels table names =
  Array.map (get_method_label table) names

soit set_method table label element =
  incr method_count;
  si Labs.find label table.methods_by_label alors
    put table label element
  sinon
    table.hidden_meths <- (label, element) :: table.hidden_meths

soit get_method table label =
  essaie List.assoc label table.hidden_meths
  avec Not_found -> table.methods.(label)

soit to_list arr =
  si arr == magic 0 alors [] sinon Array.to_list arr

soit narrow table vars virt_meths concr_meths =
  soit vars = to_list vars
  et virt_meths = to_list virt_meths
  et concr_meths = to_list concr_meths dans
  soit virt_meth_labs = List.map (get_method_label table) virt_meths dans
  soit concr_meth_labs = List.map (get_method_label table) concr_meths dans
  table.previous_states <-
     (table.methods_by_name, table.methods_by_label, table.hidden_meths,
      table.vars, virt_meth_labs, vars)
     :: table.previous_states;
  table.vars <-
    Vars.fold
      (fonc lab info tvars ->
        si List.mem lab vars alors Vars.add lab info tvars sinon tvars)
      table.vars Vars.empty;
  soit by_name = ref Meths.empty dans
  soit by_label = ref Labs.empty dans
  List.iter2
    (fonc met label ->
       by_name := Meths.add met label !by_name;
       by_label :=
          Labs.add label
            (essaie Labs.find label table.methods_by_label avec Not_found -> vrai)
            !by_label)
    concr_meths concr_meth_labs;
  List.iter2
    (fonc met label ->
       by_name := Meths.add met label !by_name;
       by_label := Labs.add label faux !by_label)
    virt_meths virt_meth_labs;
  table.methods_by_name <- !by_name;
  table.methods_by_label <- !by_label;
  table.hidden_meths <-
     List.fold_right
       (fonc ((lab, _) tel met) hm ->
          si List.mem lab virt_meth_labs alors hm sinon met::hm)
       table.hidden_meths
       []

soit widen table =
  soit (by_name, by_label, saved_hidden_meths, saved_vars, virt_meths, vars) =
    List.hd table.previous_states
  dans
  table.previous_states <- List.tl table.previous_states;
  table.vars <-
     List.fold_left
       (fonc s v -> Vars.add v (Vars.find v table.vars) s)
       saved_vars vars;
  table.methods_by_name <- by_name;
  table.methods_by_label <- by_label;
  table.hidden_meths <-
     List.fold_right
       (fonc ((lab, _) tel met) hm ->
          si List.mem lab virt_meths alors hm sinon met::hm)
       table.hidden_meths
       saved_hidden_meths

soit new_slot table =
  soit index = table.size dans
  table.size <- index + 1;
  index

soit new_variable table name =
  essaie Vars.find name table.vars
  avec Not_found ->
    soit index = new_slot table dans
    si name <> "" alors table.vars <- Vars.add name index table.vars;
    index

soit to_array arr =
  si arr = Obj.magic 0 alors [||] sinon arr

soit new_methods_variables table meths vals =
  soit meths = to_array meths dans
  soit nmeths = Array.length meths et nvals = Array.length vals dans
  soit res = Array.create (nmeths + nvals) 0 dans
  pour i = 0 à nmeths - 1 faire
    res.(i) <- get_method_label table meths.(i)
  fait;
  pour i = 0 à nvals - 1 faire
    res.(i+nmeths) <- new_variable table vals.(i)
  fait;
  res

soit get_variable table name =
  essaie Vars.find name table.vars avec Not_found -> affirme faux

soit get_variables table names =
  Array.map (get_variable table) names

soit add_initializer table f =
  table.initializers <- f::table.initializers

(*
module Keys =
  Map.Make(struct type t = tag array let compare (x:t) y = compare x y end)
let key_map = ref Keys.empty
let get_key tags : item =
  try magic (Keys.find tags !key_map : tag array)
  with Not_found ->
    key_map := Keys.add tags tags !key_map;
    magic tags
*)

soit create_table public_methods =
  si public_methods == magic 0 alors new_table [||] sinon
  (* [public_methods] must be in ascending order for bytecode *)
  soit tags = Array.map public_method_label public_methods dans
  soit table = new_table tags dans
  Array.iteri
    (fonc i met ->
      soit lab = i*2+2 dans
      table.methods_by_name  <- Meths.add met lab table.methods_by_name;
      table.methods_by_label <- Labs.add lab vrai table.methods_by_label)
    public_methods;
  table

soit init_class table =
  inst_var_count := !inst_var_count + table.size - 1;
  table.initializers <- List.rev table.initializers;
  resize table (3 + magic table.methods.(1) * 16 / Sys.word_size)

soit inherits cla vals virt_meths concr_meths (_, super, _, env) top =
  narrow cla vals virt_meths concr_meths;
  soit init =
    si top alors super cla env sinon Obj.repr (super cla) dans
  widen cla;
  Array.concat
    [[| repr init |];
     magic (Array.map (get_variable cla) (to_array vals) : int array);
     Array.map
       (fonc nm -> repr (get_method cla (get_method_label cla nm) : closure))
       (to_array concr_meths) ]

soit make_class pub_meths class_init =
  soit table = create_table pub_meths dans
  soit env_init = class_init table dans
  init_class table;
  (env_init (Obj.repr 0), class_init, env_init, Obj.repr 0)

type init_table = { modifiable env_init: t; modifiable class_init: table -> t }

soit make_class_store pub_meths class_init init_table =
  soit table = create_table pub_meths dans
  soit env_init = class_init table dans
  init_class table;
  init_table.class_init <- class_init;
  init_table.env_init <- env_init

soit dummy_class loc =
  soit undef = fonc _ -> raise (Undefined_recursive_module loc) dans
  (Obj.magic undef, undef, undef, Obj.repr 0)

(**** Objects ****)

soit create_object table =
  (* XXX Appel de [obj_block] *)
  soit obj = Obj.new_block Obj.object_tag table.size dans
  (* XXX Appel de [caml_modify] *)
  Obj.set_field obj 0 (Obj.repr table.methods);
  Obj.obj (set_id obj)

soit create_object_opt obj_0 table =
  si (Obj.magic obj_0 : bool) alors obj_0 sinon début
    (* XXX Appel de [obj_block] *)
    soit obj = Obj.new_block Obj.object_tag table.size dans
    (* XXX Appel de [caml_modify] *)
    Obj.set_field obj 0 (Obj.repr table.methods);
    Obj.obj (set_id obj)
  fin

soit rec iter_f obj =
  fonction
    []   -> ()
  | f::l -> f obj; iter_f obj l

soit run_initializers obj table =
  soit inits = table.initializers dans
  si inits <> [] alors
    iter_f obj inits

soit run_initializers_opt obj_0 obj table =
  si (Obj.magic obj_0 : bool) alors obj sinon début
    soit inits = table.initializers dans
    si inits <> [] alors iter_f obj inits;
    obj
  fin

soit create_object_and_run_initializers obj_0 table =
  si (Obj.magic obj_0 : bool) alors obj_0 sinon début
    soit obj = create_object table dans
    run_initializers obj table;
    obj
  fin

(* Equivalent primitive below
let sendself obj lab =
  (magic obj : (obj -> t) array array).(0).(lab) obj
*)
dehors send : obj -> tag -> 'a = "%send"
dehors sendcache : obj -> tag -> t -> int -> 'a = "%sendcache"
dehors sendself : obj -> label -> 'a = "%sendself"
dehors get_public_method : obj -> tag -> closure
    = "caml_get_public_method" "noalloc"

(**** table collection access ****)

type tables = Empty | Cons de closure * tables * tables
type mut_tables =
    {key: closure; modifiable data: tables; modifiable next: tables}
dehors mut : tables -> mut_tables = "%identity"
dehors demut : mut_tables -> tables = "%identity"

soit build_path n keys tables =
  (* Be careful not to create a seemingly immutable block, otherwise it could
     be statically allocated.  See #5779. *)
  soit res = demut {key = Obj.magic 0; data = Empty; next = Empty} dans
  soit r = ref res dans
  pour i = 0 à n faire
    r := Cons (keys.(i), !r, Empty)
  fait;
  tables.data <- !r;
  res

soit rec lookup_keys i keys tables =
  si i < 0 alors tables sinon
  soit key = keys.(i) dans
  soit rec lookup_key tables =
    si tables.key == key alors lookup_keys (i-1) keys tables.data sinon
    si tables.next <> Empty alors lookup_key (mut tables.next) sinon
    soit next = Cons (key, Empty, Empty) dans
    tables.next <- next;
    build_path (i-1) keys (mut next)
  dans
  lookup_key (mut tables)

soit lookup_tables root keys =
  soit root = mut root dans
  si root.data <> Empty alors
    lookup_keys (Array.length keys - 1) keys root.data
  sinon
    build_path (Array.length keys - 1) keys root

(**** builtin methods ****)

soit get_const x = ret (fonc obj -> x)
soit get_var n   = ret (fonc obj -> Array.unsafe_get obj n)
soit get_env e n =
  ret (fonc obj ->
    Array.unsafe_get (Obj.magic (Array.unsafe_get obj e) : obj) n)
soit get_meth n  = ret (fonc obj -> sendself obj n)
soit set_var n   = ret (fonc obj x -> Array.unsafe_set obj n x)
soit app_const f x = ret (fonc obj -> f x)
soit app_var f n   = ret (fonc obj -> f (Array.unsafe_get obj n))
soit app_env f e n =
  ret (fonc obj ->
    f (Array.unsafe_get (Obj.magic (Array.unsafe_get obj e) : obj) n))
soit app_meth f n  = ret (fonc obj -> f (sendself obj n))
soit app_const_const f x y = ret (fonc obj -> f x y)
soit app_const_var f x n   = ret (fonc obj -> f x (Array.unsafe_get obj n))
soit app_const_meth f x n = ret (fonc obj -> f x (sendself obj n))
soit app_var_const f n x = ret (fonc obj -> f (Array.unsafe_get obj n) x)
soit app_meth_const f n x = ret (fonc obj -> f (sendself obj n) x)
soit app_const_env f x e n =
  ret (fonc obj ->
    f x (Array.unsafe_get (Obj.magic (Array.unsafe_get obj e) : obj) n))
soit app_env_const f e n x =
  ret (fonc obj ->
    f (Array.unsafe_get (Obj.magic (Array.unsafe_get obj e) : obj) n) x)
soit meth_app_const n x = ret (fonc obj -> (sendself obj n : _ -> _) x)
soit meth_app_var n m =
  ret (fonc obj -> (sendself obj n : _ -> _) (Array.unsafe_get obj m))
soit meth_app_env n e m =
  ret (fonc obj -> (sendself obj n : _ -> _)
      (Array.unsafe_get (Obj.magic (Array.unsafe_get obj e) : obj) m))
soit meth_app_meth n m =
  ret (fonc obj -> (sendself obj n : _ -> _) (sendself obj m))
soit send_const m x c =
  ret (fonc obj -> sendcache x m (Array.unsafe_get obj 0) c)
soit send_var m n c =
  ret (fonc obj ->
    sendcache (Obj.magic (Array.unsafe_get obj n) : obj) m
      (Array.unsafe_get obj 0) c)
soit send_env m e n c =
  ret (fonc obj ->
    sendcache
      (Obj.magic (Array.unsafe_get
                    (Obj.magic (Array.unsafe_get obj e) : obj) n) : obj)
      m (Array.unsafe_get obj 0) c)
soit send_meth m n c =
  ret (fonc obj ->
    sendcache (sendself obj n) m (Array.unsafe_get obj 0) c)
soit new_cache table =
  soit n = new_method table dans
  soit n =
    si n mod 2 = 0 || n > 2 + magic table.methods.(1) * 16 / Sys.word_size
    alors n sinon new_method table
  dans
  table.methods.(n) <- Obj.magic 0;
  n

type impl =
    GetConst
  | GetVar
  | GetEnv
  | GetMeth
  | SetVar
  | AppConst
  | AppVar
  | AppEnv
  | AppMeth
  | AppConstConst
  | AppConstVar
  | AppConstEnv
  | AppConstMeth
  | AppVarConst
  | AppEnvConst
  | AppMethConst
  | MethAppConst
  | MethAppVar
  | MethAppEnv
  | MethAppMeth
  | SendConst
  | SendVar
  | SendEnv
  | SendMeth
  | Closure de closure

soit method_impl table i arr =
  soit next () = incr i; magic arr.(!i) dans
  filtre next() avec
    GetConst -> soit x : t = next() dans get_const x
  | GetVar   -> soit n = next() dans get_var n
  | GetEnv   -> soit e = next() et n = next() dans get_env e n
  | GetMeth  -> soit n = next() dans get_meth n
  | SetVar   -> soit n = next() dans set_var n
  | AppConst -> soit f = next() et x = next() dans app_const f x
  | AppVar   -> soit f = next() et n = next () dans app_var f n
  | AppEnv   ->
      soit f = next() et e = next() et n = next() dans app_env f e n
  | AppMeth  -> soit f = next() et n = next () dans app_meth f n
  | AppConstConst ->
      soit f = next() et x = next() et y = next() dans app_const_const f x y
  | AppConstVar ->
      soit f = next() et x = next() et n = next() dans app_const_var f x n
  | AppConstEnv ->
      soit f = next() et x = next() et e = next () et n = next() dans
      app_const_env f x e n
  | AppConstMeth ->
      soit f = next() et x = next() et n = next() dans app_const_meth f x n
  | AppVarConst ->
      soit f = next() et n = next() et x = next() dans app_var_const f n x
  | AppEnvConst ->
      soit f = next() et e = next () et n = next() et x = next() dans
      app_env_const f e n x
  | AppMethConst ->
      soit f = next() et n = next() et x = next() dans app_meth_const f n x
  | MethAppConst ->
      soit n = next() et x = next() dans meth_app_const n x
  | MethAppVar ->
      soit n = next() et m = next() dans meth_app_var n m
  | MethAppEnv ->
      soit n = next() et e = next() et m = next() dans meth_app_env n e m
  | MethAppMeth ->
      soit n = next() et m = next() dans meth_app_meth n m
  | SendConst ->
      soit m = next() et x = next() dans send_const m x (new_cache table)
  | SendVar ->
      soit m = next() et n = next () dans send_var m n (new_cache table)
  | SendEnv ->
      soit m = next() et e = next() et n = next() dans
      send_env m e n (new_cache table)
  | SendMeth ->
      soit m = next() et n = next () dans send_meth m n (new_cache table)
  | Closure _ tel clo -> magic clo

soit set_methods table methods =
  soit len = Array.length methods et i = ref 0 dans
  pendant_que !i < len faire
    soit label = methods.(!i) et clo = method_impl table i methods dans
    set_method table label clo;
    incr i
  fait

(**** Statistics ****)

type stats =
  { classes: int; methods: int; inst_vars: int; }

soit stats () =
  { classes = !table_count;
    methods = !method_count; inst_vars = !inst_var_count; }
