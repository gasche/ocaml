(*
build:
  ../ocamlopt.opt -nostdlib -I ../stdlib linehist.ml -o linehist.exe

test:
  IMPL=hashtbl2 ITERS=32 COUNT=5 FILE=../typing/typecore.ml ./linehist.exe

bench:
  hyperfine -L impl hashtbl,hashtbl2 --command-name {impl} "IMPL={impl} ITERS=32 COUNT=5 FILE=../typing/typecore.ml ./linehist.exe"
*)

module type Hashtbl = sig
  type ('a, 'b) t
  val create : ?random:bool -> int -> ('a, 'b) t
  val find : ('a, 'b) t -> 'a -> 'b
  val add : ('a, 'b) t -> 'a -> 'b -> unit
  val replace : ('a, 'b) t -> 'a -> 'b -> unit
  val to_seq : ('a, 'b) t -> ('a * 'b) Seq.t
end

module Test(Hashtbl : Hashtbl) = struct
  let make_histogram lines =
    let tbl = Hashtbl.create 0 in
    lines |> List.iter (fun line ->
      match Hashtbl.find tbl line with
      | exception Not_found ->
        Hashtbl.add tbl line 1
      | count ->
        Hashtbl.replace tbl line (count + 1)
    );
    let histo =
      Hashtbl.to_seq tbl
      |> Seq.map (fun (line, count) -> (count, line))
      |> Array.of_seq in
    Array.sort (Pair.compare (Fun.flip Int.compare) String.compare) histo;
    histo
end

module Test1 = Test(Hashtbl)
module Test2 = Test(Hashtbl2)

let impls = [
  ("hashtbl", Test1.make_histogram);
  ("hashtbl2", Test2.make_histogram);
]

let file = Sys.getenv "FILE"
let niters = Sys.getenv "ITERS" |> int_of_string
let count = Sys.getenv "COUNT"
let make_histogram_impl = List.assoc (Sys.getenv "IMPL") impls


let () =
  let lines = In_channel.(with_open_bin file input_lines) in
  for _ = 1 to niters do
    ignore (Sys.opaque_identity (make_histogram_impl lines))
  done;
  let histo = make_histogram_impl lines in
  for i = 0 to min 4 (Array.length histo) do
    let (count, line) = histo.(i) in
    Printf.printf "%.3d: %S\n" count line 
  done
