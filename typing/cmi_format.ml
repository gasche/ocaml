(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                  Fabrice Le Fessant, INRIA Saclay                   *)
(*                                                                     *)
(*  Copyright 2012 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type pers_flags = Rectypes

type error =
    Not_an_interface de string
  | Wrong_version_interface de string * string
  | Corrupted_interface de string

exception Error de error

type cmi_infos = {
    cmi_name : string;
    cmi_sign : Types.signature_item list;
    cmi_crcs : (string * Digest.t) list;
    cmi_flags : pers_flags list;
}

soit input_cmi ic =
  soit (name, sign) = input_value ic dans
  soit crcs = input_value ic dans
  soit flags = input_value ic dans
  {
      cmi_name = name;
      cmi_sign = sign;
      cmi_crcs = crcs;
      cmi_flags = flags;
    }

soit read_cmi filename =
  soit ic = open_in_bin filename dans
  essaie
    soit buffer = Misc.input_bytes ic (String.length Config.cmi_magic_number) dans
    si buffer <> Config.cmi_magic_number alors début
      close_in ic;
      soit pre_len = String.length Config.cmi_magic_number - 3 dans
      si String.sub buffer 0 pre_len
          = String.sub Config.cmi_magic_number 0 pre_len alors
      début
        soit msg =
          si buffer < Config.cmi_magic_number alors "plus ancienne" sinon "plus récente" dans
        raise (Error (Wrong_version_interface (filename, msg)))
      fin sinon début
        raise(Error(Not_an_interface filename))
      fin
    fin;
    soit cmi = input_cmi ic dans
    close_in ic;
    cmi
  avec End_of_file | Failure _ ->
      close_in ic;
      raise(Error(Corrupted_interface(filename)))
    | Error e ->
      close_in ic;
      raise (Error e)

soit output_cmi filename oc cmi =
(* beware: the provided signature must have been substituted for saving *)
  output_string oc Config.cmi_magic_number;
  output_value oc (cmi.cmi_name, cmi.cmi_sign);
  flush oc;
  soit crc = Digest.file filename dans
  soit crcs = (cmi.cmi_name, crc) :: cmi.cmi_crcs dans
  output_value oc crcs;
  output_value oc cmi.cmi_flags;
  crc

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Not_an_interface filename ->
      fprintf ppf "%a@ n'est pas une interface compilée"
        Location.print_filename filename
  | Wrong_version_interface (filename, older_newer) ->
      fprintf ppf
        "%a@ n'est pas une interface compilée pour cette version de Chamelle.@.\
         Cela semble être pour une version %s de Chamelle."
        Location.print_filename filename older_newer
  | Corrupted_interface filename ->
      fprintf ppf "Interface compilée corrompue@ %a"
        Location.print_filename filename

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
