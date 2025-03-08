(*
Build:
  ./runtime/ocamlrun ./ocamlc -nostdlib -I stdlib produce_large_marshal.ml -o produce_large_marshal.byte

Use:
  ./runtime/ocamlrun ./produce_large_marshal.byte data.bin 50_000
*)

let filename =
  try Sys.argv.(1) with
  | _ -> failwith "Excepted filename (string) as first command-line parameter"

let size =
  try int_of_string Sys.argv.(2) with
  | _ -> failwith "Excepted a size (integer) as second command-line parameter"

type data = int list

let payload : data =
  Random.init 42;
  List.init size (fun _ -> Random.int size)

let () =
  Out_channel.with_open_bin filename @@ fun oc ->
  output_value oc payload;
  flush oc
