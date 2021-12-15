(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                Ulysse Gérard, Thomas Refis, Tarides                    *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module Uid = struct
  type t =
    | Compilation_unit of string
    | Item of { comp_unit: string; id: int }
    | Internal
    | Predef of string

  include Identifiable.Make(struct
    type nonrec t = t

    let equal (x : t) y = x = y
    let compare (x : t) y = compare x y
    let hash (x : t) = Hashtbl.hash x

    let print fmt = function
      | Internal -> Format.pp_print_string fmt "<internal>"
      | Predef name -> Format.fprintf fmt "<predef:%s>" name
      | Compilation_unit s -> Format.pp_print_string fmt s
      | Item { comp_unit; id } -> Format.fprintf fmt "%s.%d" comp_unit id

    let output oc t =
      let fmt = Format.formatter_of_out_channel oc in
      print fmt t
  end)

  let id = ref (-1)

  let reinit () = id := (-1)

  let mk  ~current_unit =
      incr id;
      Item { comp_unit = current_unit; id = !id }

  let of_compilation_unit_id id =
    if not (Ident.persistent id) then
      Misc.fatal_errorf "Types.Uid.of_compilation_unit_id %S" (Ident.name id);
    Compilation_unit (Ident.name id)

  let of_predef_id id =
    if not (Ident.is_predef id) then
      Misc.fatal_errorf "Types.Uid.of_predef_id %S" (Ident.name id);
    Predef (Ident.name id)

  let internal_not_actually_unique = Internal

  let for_actual_declaration = function
    | Item _ -> true
    | _ -> false
end

module Sig_component_kind = struct
  type t =
    | Value
    | Type
    | Module
    | Module_type
    | Extension_constructor
    | Class
    | Class_type

  let to_string = function
    | Value -> "value"
    | Type -> "type"
    | Module -> "module"
    | Module_type -> "module type"
    | Extension_constructor -> "extension constructor"
    | Class -> "class"
    | Class_type -> "class type"

  let can_appear_in_types = function
    | Value
    | Extension_constructor ->
        false
    | Type
    | Module
    | Module_type
    | Class
    | Class_type ->
        true
end

module Item = struct
  module T = struct
    type t = string * Sig_component_kind.t
    let compare = compare

    let make str ns = str, ns

    let value id = Ident.name id, Sig_component_kind.Value
    let type_ id = Ident.name id, Sig_component_kind.Type
    let module_ id = Ident.name id, Sig_component_kind.Module
    let module_type id = Ident.name id, Sig_component_kind.Module_type
    let extension_constructor id =
      Ident.name id, Sig_component_kind.Extension_constructor
    let class_ id =
      Ident.name id, Sig_component_kind.Class
    let class_type id =
      Ident.name id, Sig_component_kind.Class_type

    let print fmt (name, ns) =
      Format.fprintf fmt "%S[%s]"
        name
        (Sig_component_kind.to_string ns)
  end

  include T

  module Map = Map.Make(T)
end

type var = Ident.t
type t = { uid: Uid.t option; desc: desc }
and desc =
  | Var of var
  | Abs of var * t
  | App of t * t
  | Struct of t Item.Map.t
  | Leaf
  | Proj of t * Item.t
  | Comp_unit of string

let print fmt =
  let print_uid_opt =
    Format.pp_print_option (fun fmt -> Format.fprintf fmt "<%a>" Uid.print)
  in
  let rec aux fmt { uid; desc } =
    match desc with
    | Var id ->
        Format.fprintf fmt "%a%a" Ident.print id print_uid_opt uid
    | Abs (id, t) ->
        Format.fprintf fmt "Abs@[%a@,(@[%a,@ @[%a@]@])@]"
          print_uid_opt uid Ident.print id aux t
    | App (t1, t2) ->
        Format.fprintf fmt "@[%a(@,%a)%a@]" aux t1 aux t2
          print_uid_opt uid
    | Leaf ->
        Format.fprintf fmt "<%a>" (Format.pp_print_option Uid.print) uid
    | Proj (t, item) ->
        begin match uid with
        | None ->
            Format.fprintf fmt "@[%a@ .@ %a@]"
              aux t
              Item.print item
        | Some uid ->
            Format.fprintf fmt "@[(%a@ .@ %a)<%a>@]"
              aux t
              Item.print item
              Uid.print uid
        end
    | Comp_unit name -> Format.fprintf fmt "CU %s" name
    | Struct map ->
        let print_map fmt =
          Item.Map.iter (fun item t ->
              Format.fprintf fmt "@[<hv 4>%a ->@ %a;@]@,"
                Item.print item
                aux t
            )
        in
        Format.fprintf fmt "{@[<v>%a@,%a@]}" print_uid_opt uid print_map map
  in
  Format.fprintf fmt"@[%a@]@;" aux

let improve_uid uid t =
  match t.uid with
  | Some _ -> t
  | None -> { t with uid }

let fresh_var ?(name="shape-var") uid =
  let var = Ident.create_local name in
  var, { uid = Some uid; desc = Var var }

let for_unnamed_functor_param = Ident.create_local "()"

let var uid id =
  { uid = Some uid; desc = Var id }

let abs ?uid var body =
  { uid; desc = Abs (var, body) }

let str ?uid map =
  { uid; desc = Struct map }

let leaf uid =
  { uid = Some uid; desc = Leaf }

let proj ?uid t item =
  match t.desc with
  | Leaf ->
      (* When stuck projecting in a leaf we propagate the leaf
        as a best effort *)
      t
  | Struct map ->
      begin try Item.Map.find item map
      with Not_found -> t (* ill-typed program *)
      end
  | _ ->
      { uid; desc = Proj (t, item) }

let app ?uid f ~arg =
      { uid; desc = App (f, arg) }

module Make_reduce(Params : sig
  type env
  val fuel : int
  val read_unit_shape : unit_name:string -> t option
  val find_shape : env -> Ident.t -> t
end) = struct
  type strategy = Weak | Strong
  type local_env = t Ident.tbl

  type env = {
    fuel: int ref;
    global_env: Params.env;
    local_env: local_env;
    memo_table: (strategy * local_env * t, t) Hashtbl.t;
  }

  let bind env var shape =
    { env with local_env = Ident.add var shape env.local_env }

  let rec reduce_ strategy env t =
    let {fuel = _; global_env = _; local_env; memo_table} = env in
    let memo_key = (strategy, local_env, t) in
    match Hashtbl.find memo_table memo_key with
    | result -> result
    | exception Not_found ->
        let result = reduce__ strategy env t in
        Hashtbl.replace memo_table memo_key result;
        result

  and reduce__ strategy ({fuel; global_env; local_env; _} as env) t =
    let reduce env t = reduce_ strategy env t in
    if !fuel < 0 then
      t
    else
      match t.desc with
      | Comp_unit unit_name ->
          begin match Params.read_unit_shape ~unit_name with
          | Some t -> reduce env t
          | None -> t
          end
      | App(f, arg) ->
          let f = reduce_ Weak env f in
          let arg = reduce_ Strong env arg in
          begin match f.desc with
          | Abs(var, body) ->
              (* we only add Strong normal forms
                 to the environment. *)
              reduce (bind env var arg) body
              |> improve_uid t.uid
          | _ ->
              (* If f is well-typed at a function type, its Weak
                 normal forms are either Abs or a Strong normal form. *)
              { t with desc = App(f, arg) }
          end
      | Proj(str, item) ->
          let str = reduce env str in
          let nored = { t with desc = Proj(str, item) } in
          begin match str.desc with
          | Struct items ->
              begin match Item.Map.find item items with
              | exception Not_found -> nored
              | item -> item
              end
          | _ -> nored
          end
      | Abs(var, body) ->
          begin match strategy with
          | Weak -> t
          | Strong ->
              let env = bind env var { uid = None; desc = Var var } in
              let vbody = reduce env body in
              { t with desc = Abs(var, vbody) }
          end
      | Var id ->
          begin match Ident.find_same id local_env with
          | def ->
              if def.desc = Var id then t else def (* already in Strong normal form *)
          | exception Not_found ->
          match Params.find_shape global_env id with
          | res ->
              if res = t then
                (* reducing here would loop forever *)
                t
              else begin
                decr fuel;
                reduce env res
              end
          | exception Not_found ->
              t
          end
      | Leaf -> t
      | Struct m ->
          { t with desc = Struct (Item.Map.map (reduce env) m) }

  let reduce global_env t =
    let fuel = ref Params.fuel in
    let memo_table = Hashtbl.create 42 in
    let local_env = Ident.empty in
    reduce_ Strong { fuel; global_env; memo_table; local_env } t
end

module Local_reduce =
  Make_reduce(struct
    type env = unit
    let fuel = 10
    let read_unit_shape ~unit_name:_ = None
    let find_shape _env _id = raise Not_found
  end)

let local_reduce shape =
  Local_reduce.reduce () shape

let dummy_mod = { uid = None; desc = Struct Item.Map.empty }

let of_path ~find_shape ~namespace =
  let rec aux : Sig_component_kind.t -> Path.t -> t = fun ns -> function
    | Pident id -> find_shape ns id
    | Pdot (path, name) -> proj (aux Module path) (name, ns)
    | Papply (p1, p2) -> app (aux Module p1) ~arg:(aux Module p2)
  in
  aux namespace

let for_persistent_unit s =
  { uid = Some (Uid.of_compilation_unit_id (Ident.create_persistent s));
    desc = Comp_unit s }

let leaf_for_unpack = { uid = None; desc = Leaf }

let set_uid_if_none t uid =
  match t.uid with
  | None -> { t with uid = Some uid }
  | _ -> t

module Map = struct
  type shape = t
  type nonrec t = t Item.Map.t

  let empty = Item.Map.empty

  let add t item shape = Item.Map.add item shape t

  let add_value t id uid = Item.Map.add (Item.value id) (leaf uid) t
  let add_value_proj t id shape =
    let item = Item.value id in
    Item.Map.add item (proj shape item) t

  let add_type t id uid = Item.Map.add (Item.type_ id) (leaf uid) t
  let add_type_proj t id shape =
    let item = Item.type_ id in
    Item.Map.add item (proj shape item) t

  let add_module t id shape = Item.Map.add (Item.module_ id) shape t
  let add_module_proj t id shape =
    let item = Item.module_ id in
    Item.Map.add item (proj shape item) t

  let add_module_type t id uid =
    Item.Map.add (Item.module_type id) (leaf uid) t
  let add_module_type_proj t id shape =
    let item = Item.module_type id in
    Item.Map.add item (proj shape item) t

  let add_extcons t id uid =
    Item.Map.add (Item.extension_constructor id) (leaf uid) t
  let add_extcons_proj t id shape =
    let item = Item.extension_constructor id in
    Item.Map.add item (proj shape item) t

  let add_class t id uid = Item.Map.add (Item.class_ id) (leaf uid) t
  let add_class_proj t id shape =
    let item = Item.class_ id in
    Item.Map.add item (proj shape item) t

  let add_class_type t id uid = Item.Map.add (Item.class_type id) (leaf uid) t
  let add_class_type_proj t id shape =
    let item = Item.class_type id in
    Item.Map.add item (proj shape item) t
end
