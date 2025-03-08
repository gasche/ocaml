(*
Build:
  ./runtime/ocamlrun ./ocamlc -nostdlib -I stdlib consume_large_marshal.ml -o consume_large_marshal.byte

Use:
  hyperfine -L mode steady,rampup \
    "./runtime/ocamlrun ./consume_large_marshal.byte data.bin 30 {mode}"
*)

let filename =
  try Sys.argv.(1) with
  | _ -> failwith "Excepted filename (string) as first command-line parameter"

let nb_iters =
  try int_of_string Sys.argv.(2) with
  | _ -> failwith "Excepted iteration count (int) as second command-line parameter"

let steady_or_rampup =
  match Sys.argv.(3) with
  | "steady" -> `Steady
  | "rampup" -> `Rampup
  | _ | exception _ ->
      failwith "Expected 'steady' or 'rampup' as third command-line parameter"

type data = int list

let get_payloads () =
  List.init nb_iters (fun _ ->
    In_channel.with_open_bin filename @@ fun ic ->
    (input_value ic : data)
  )

let payloads, suspended_work =
  match steady_or_rampup with
  | `Steady ->
      let v = get_payloads () in
      Gc.ramp_up (fun () -> v)
  | `Rampup ->
      Gc.ramp_up get_payloads

let work payload =
  (* do some lightweight allocations over the payload *)
  ignore (List.map succ payload)

let () =
  List.iter work payloads;
  Gc.ramp_down suspended_work;
  Gc.major ()
