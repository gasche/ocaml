(* TEST
   flags = "-I ${ocamlsrcdir}/parsing"
   include ocamlcommon
   * expect
*)

module L = Longident
[%%expect {|
module L = Longident
|}]

let flatten_ident = L.flatten (L.Lident "foo")
let flatten_dot = L.flatten (L.Ldot (L.Lident "M", "foo"))
let flatten_apply = L.flatten (L.Lapply (L.Lident "F", L.Lident "X"))
[%%expect {|
val flatten_ident : string list = ["foo"]
val flatten_dot : string list = ["M"; "foo"]
Exception: Misc.Fatal_error.
|}]

let unflatten_empty = L.unflatten []
let unflatten_sing = L.unflatten ["foo"]
let unflatten_dot = L.unflatten ["M"; "N"; "foo"]
[%%expect {|
val unflatten_empty : L.t option = None
val unflatten_sing : L.t option = Some (L.Lident "foo")
val unflatten_dot : L.t option =
  Some (L.Ldot (L.Ldot (L.Lident "M", "N"), "foo"))
|}]

let last_ident = L.last (L.lident "foo")
let last_dot = L.last (L.Ldot (L.lident "M", "foo"))
let last_apply = L.last (L.Lapply (L.Lident "F", L.Lident "X"))
let last_dot_apply = L.ldot (L.Lapply (L.Lident "F", L.Lident "X"), "foo")
[%%expect {|
Line _, characters 25-33:
  let last_ident = L.last (L.lident "foo")
                           ^^^^^^^^
Error: Unbound value L.lident
|}]

let parse_empty = L.parse ""
let parse_ident = L.parse "foo"
let parse_dot = L.parse "M.foo"
let parse_path = L.parse "M.N.foo"
let parse_complex = L.parse "M.F(M.N).N.foo"
[%%expect {|
val parse_empty : L.t = L.Lident ""
val parse_ident : L.t = L.Lident "foo"
val parse_dot : L.t = L.Ldot (L.Lident "M", "foo")
val parse_path : L.t = L.Ldot (L.Ldot (L.Lident "M", "N"), "foo")
val parse_complex : L.t =
  L.Ldot (L.Ldot (L.Ldot (L.Ldot (L.Lident "M", "F(M"), "N)"), "N"), "foo")
|}]
