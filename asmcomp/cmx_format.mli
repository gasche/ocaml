(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Gallium, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2010 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Format of .cmx, .cmxa and .cmxs files *)

(* Each .o file has a matching .cmx file that provides the following infos
   on the compilation unit:
     - list of other units imported, with MD5s of their .cmx files
     - approximation of the structure implemented
       (includes descriptions of known functions: arity and direct entry
        points)
     - list of currying functions and application functions needed
   The .cmx file contains these infos (as an externed record) plus a MD5
   of these infos *)

type unit_infos =
  { modifiable ui_name: string;                    (* Name of unit implemented *)
    modifiable ui_symbol: string;            (* Prefix for symbols *)
    modifiable ui_defines: string list;      (* Unit and sub-units implemented *)
    modifiable ui_imports_cmi: (string * Digest.t) list; (* Interfaces imported *)
    modifiable ui_imports_cmx: (string * Digest.t) list; (* Infos imported *)
    modifiable ui_approx: Clambda.value_approximation; (* Approx of the structure*)
    modifiable ui_curry_fun: int list;             (* Currying functions needed *)
    modifiable ui_apply_fun: int list;             (* Apply functions needed *)
    modifiable ui_send_fun: int list;              (* Send functions needed *)
    modifiable ui_force_link: bool }               (* Always linked *)

(* Each .a library has a matching .cmxa file that provides the following
   infos on the library: *)

type library_infos =
  { lib_units: (unit_infos * Digest.t) list;  (* List of unit infos w/ MD5s *)
    lib_ccobjs: string list;            (* C object files needed *)
    lib_ccopts: string list }           (* Extra opts to C compiler *)

(* Each .cmxs dynamically-loaded plugin contains a symbol
   "caml_plugin_header" containing the following info
   (as an externed record) *)

type dynunit = {
  dynu_name: string;
  dynu_crc: Digest.t;
  dynu_imports_cmi: (string * Digest.t) list;
  dynu_imports_cmx: (string * Digest.t) list;
  dynu_defines: string list;
}

type dynheader = {
  dynu_magic: string;
  dynu_units: dynunit list;
}
