module type IntegerDLS = sig
  type key
  val new_key : unit -> key
  val get : key -> int (* default value: 0 *)
  val set : key -> int -> unit
end

module BuiltinDLS : IntegerDLS = struct
  type key = int Domain.DLS.key
  let new_key () =
    Domain.DLS.new_key (fun () -> 0)
  let get k = Domain.DLS.get k
  let set k v = Domain.DLS.set k v
end

module IndexDLS : IntegerDLS = struct
  type key = int Atomic.t array Atomic.t

  let new_key () = Atomic.make [| |]

  let rec get_ref_slow key idx =
    let arr = Atomic.get key in
    if idx < Array.length arr then arr.(idx)
    else begin
      let new_arr =
        Array.init (max 1 (2 * idx)) (fun i ->
          if i < Array.length arr then arr.(i)
          else Atomic.make_contended 0
        )
      in
      if Atomic.compare_and_set key arr new_arr
      then new_arr.(idx)
      else get_ref_slow key idx
    end

  let[@inline always] get_ref key =
    let idx = Domain.self_index () in
    let arr = Atomic.get key in
    if idx < Array.length arr then arr.(idx)
    else get_ref_slow key idx

  let get key = Atomic.get (get_ref key)
  let set key v = Atomic.set (get_ref key) v
end

let on_n_doms n f =
  let doms = List.init (n - 1) (fun _ -> Domain.spawn f) in
  f ();
  List.iter Domain.join doms

let run_stdlib ~doms ~rounds =
  let counters = BuiltinDLS.new_key () in
  on_n_doms doms (fun () ->
    for _ = 1 to rounds do
      let cur = BuiltinDLS.get counters in
      BuiltinDLS.set counters (cur + 1)
    done
  )

let run_index ~doms ~rounds =
  let counters = IndexDLS.new_key () in
  on_n_doms doms (fun () ->
    for _ = 1 to rounds do
      let cur = IndexDLS.get counters in
      IndexDLS.set counters (cur + 1)
    done
  )

let usage () =
  Printf.eprintf
    "Usage: %s [stdlib | index] <domains> <rounds>\n%!"
    Sys.argv.(0)

let run_impl = match Sys.argv.(1) with
  | "stdlib" -> run_stdlib
  | "index" -> run_index
  | exception _ | _ -> usage (); exit 2

let num_doms =
  try int_of_string Sys.argv.(2)
  with _ -> usage (); exit 2

let num_rounds =
  try int_of_string Sys.argv.(3)
  with _ -> usage (); exit 2

let () =
  for i = 1 to 100 do
    run_impl ~doms:num_doms ~rounds:num_rounds
  done
