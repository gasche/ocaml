(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Pierre Weis && Damien Doligez, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 1998 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* When you change this, you need to update the documentation:
   - man/ocamlc.m   in ocaml
   - man/ocamlopt.m in ocaml
   - manual/cmds/comp.etex   in the doc sources
   - manual/cmds/native.etex in the doc sources
*)

type t =
  | Comment_start                           (*  1 *)
  | Comment_not_end                         (*  2 *)
  | Deprecated de string                    (*  3 *)
  | Fragile_match de string                 (*  4 *)
  | Partial_application                     (*  5 *)
  | Labels_omitted                          (*  6 *)
  | Method_override de string list          (*  7 *)
  | Partial_match de string                 (*  8 *)
  | Non_closed_record_pattern de string     (*  9 *)
  | Statement_type                          (* 10 *)
  | Unused_match                            (* 11 *)
  | Unused_pat                              (* 12 *)
  | Instance_variable_override de string list (* 13 *)
  | Illegal_backslash                       (* 14 *)
  | Implicit_public_methods de string list  (* 15 *)
  | Unerasable_optional_argument            (* 16 *)
  | Undeclared_virtual_method de string     (* 17 *)
  | Not_principal de string                 (* 18 *)
  | Without_principality de string          (* 19 *)
  | Unused_argument                         (* 20 *)
  | Nonreturning_statement                  (* 21 *)
  | Camlp4 de string                        (* 22 *)
  | Useless_record_with                     (* 23 *)
  | Bad_module_name de string               (* 24 *)
  | All_clauses_guarded                     (* 25 *)
  | Unused_var de string                    (* 26 *)
  | Unused_var_strict de string             (* 27 *)
  | Wildcard_arg_to_constant_constr         (* 28 *)
  | Eol_in_string                           (* 29 *)
  | Duplicate_definitions de string * string * string * string (*30 *)
  | Multiple_definition de string * string * string (* 31 *)
  | Unused_value_declaration de string      (* 32 *)
  | Unused_open de string                   (* 33 *)
  | Unused_type_declaration de string       (* 34 *)
  | Unused_for_index de string              (* 35 *)
  | Unused_ancestor de string               (* 36 *)
  | Unused_constructor de string * bool * bool  (* 37 *)
  | Unused_exception de string * bool       (* 38 *)
  | Unused_rec_flag                         (* 39 *)
  | Name_out_of_scope de string * string list * bool (* 40 *)
  | Ambiguous_name de string list * string list *  bool    (* 41 *)
  | Disambiguated_name de string            (* 42 *)
  | Nonoptional_label de string             (* 43 *)
  | Open_shadow_identifier de string * string (* 44 *)
  | Open_shadow_label_constructor de string * string (* 45 *)
  | Bad_env_variable de string * string     (* 46 *)
  | Attribute_payload de string * string    (* 47 *)
  | Eliminated_optional_arguments de string list (* 48 *)
;;

(* If you remove a warning, leave a hole in the numbering.  NEVER change
   the numbers of existing warnings.
   If you add a new warning, add it at the end with a new number;
   do NOT reuse one of the holes.
*)

soit number = fonction
  | Comment_start -> 1
  | Comment_not_end -> 2
  | Deprecated _ -> 3
  | Fragile_match _ -> 4
  | Partial_application -> 5
  | Labels_omitted -> 6
  | Method_override _ -> 7
  | Partial_match _ -> 8
  | Non_closed_record_pattern _ -> 9
  | Statement_type -> 10
  | Unused_match -> 11
  | Unused_pat -> 12
  | Instance_variable_override _ -> 13
  | Illegal_backslash -> 14
  | Implicit_public_methods _ -> 15
  | Unerasable_optional_argument -> 16
  | Undeclared_virtual_method _ -> 17
  | Not_principal _ -> 18
  | Without_principality _ -> 19
  | Unused_argument -> 20
  | Nonreturning_statement -> 21
  | Camlp4 _ -> 22
  | Useless_record_with -> 23
  | Bad_module_name _ -> 24
  | All_clauses_guarded -> 25
  | Unused_var _ -> 26
  | Unused_var_strict _ -> 27
  | Wildcard_arg_to_constant_constr -> 28
  | Eol_in_string -> 29
  | Duplicate_definitions _ -> 30
  | Multiple_definition _ -> 31
  | Unused_value_declaration _ -> 32
  | Unused_open _ -> 33
  | Unused_type_declaration _ -> 34
  | Unused_for_index _ -> 35
  | Unused_ancestor _ -> 36
  | Unused_constructor _ -> 37
  | Unused_exception _ -> 38
  | Unused_rec_flag -> 39
  | Name_out_of_scope _ -> 40
  | Ambiguous_name _ -> 41
  | Disambiguated_name _ -> 42
  | Nonoptional_label _ -> 43
  | Open_shadow_identifier _ -> 44
  | Open_shadow_label_constructor _ -> 45
  | Bad_env_variable _ -> 46
  | Attribute_payload _ -> 47
  | Eliminated_optional_arguments _ -> 48
;;

soit last_warning_number = 48
(* Must be the max number returned by the [number] function. *)

soit letter = fonction
  | 'a' ->
     soit rec loop i = si i = 0 alors [] sinon i :: loop (i - 1) dans
     loop last_warning_number
  | 'b' -> []
  | 'c' -> [1; 2]
  | 'd' -> [3]
  | 'e' -> [4]
  | 'f' -> [5]
  | 'g' -> []
  | 'h' -> []
  | 'i' -> []
  | 'j' -> []
  | 'k' -> [32; 33; 34; 35; 36; 37; 38; 39]
  | 'l' -> [6]
  | 'm' -> [7]
  | 'n' -> []
  | 'o' -> []
  | 'p' -> [8]
  | 'q' -> []
  | 'r' -> [9]
  | 's' -> [10]
  | 't' -> []
  | 'u' -> [11; 12]
  | 'v' -> [13]
  | 'w' -> []
  | 'x' -> [14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 30]
  | 'y' -> [26]
  | 'z' -> [27]
  | _ -> affirme faux
;;

soit active = Array.create (last_warning_number + 1) vrai;;
soit error = Array.create (last_warning_number + 1) faux;;

type state = bool array * bool array
soit backup () = (Array.copy active, Array.copy error)
soit restore (a, e) =
  affirme(Array.length a = Array.length active);
  affirme(Array.length e = Array.length error);
  Array.blit a 0 active 0 (Array.length active);
  Array.blit e 0 error 0 (Array.length error)

soit is_active x = active.(number x);;
soit is_error x = error.(number x);;

soit parse_opt flags s =
  soit set i = flags.(i) <- vrai dans
  soit clear i = flags.(i) <- faux dans
  soit set_all i = active.(i) <- vrai; error.(i) <- vrai dans
  soit error () = raise (Arg.Bad "Ill-formed list of warnings") dans
  soit rec get_num n i =
    si i >= String.length s alors i, n
    sinon filtre s.[i] avec
    | '0'..'9' -> get_num (10 * n + Char.code s.[i] - Char.code '0') (i + 1)
    | _ -> i, n
  dans
  soit get_range i =
    soit i, n1 = get_num 0 i dans
    si i + 2 < String.length s && s.[i] = '.' && s.[i + 1] = '.' alors
      soit i, n2 = get_num 0 (i + 2) dans
      si n2 < n1 alors error ();
      i, n1, n2
    sinon
      i, n1, n1
  dans
  soit rec loop i =
    si i >= String.length s alors () sinon
    filtre s.[i] avec
    | 'A' .. 'Z' ->
       List.iter set (letter (Char.lowercase s.[i]));
       loop (i+1)
    | 'a' .. 'z' ->
       List.iter clear (letter s.[i]);
       loop (i+1)
    | '+' -> loop_letter_num set (i+1)
    | '-' -> loop_letter_num clear (i+1)
    | '@' -> loop_letter_num set_all (i+1)
    | c -> error ()
  et loop_letter_num myset i =
    si i >= String.length s alors error () sinon
    filtre s.[i] avec
    | '0' .. '9' ->
        soit i, n1, n2 = get_range i dans
        pour n = n1 à min n2 last_warning_number faire myset n fait;
        loop i
    | 'A' .. 'Z' ->
       List.iter myset (letter (Char.lowercase s.[i]));
       loop (i+1)
    | 'a' .. 'z' ->
       List.iter myset (letter s.[i]);
       loop (i+1)
    | _ -> error ()
  dans
  loop 0
;;

soit parse_options errflag s = parse_opt (si errflag alors error sinon active) s;;

(* If you change these, don't forget to change them in man/ocamlc.m *)
soit defaults_w = "+a-4-6-7-9-27-29-32..39-41..42-44-45-48";;
soit defaults_warn_error = "-a";;

soit () = parse_options faux defaults_w;;
soit () = parse_options vrai defaults_warn_error;;

soit message = fonction
  | Comment_start -> "ceci est le début d'un commentaire."
  | Comment_not_end -> "ceci n'est pas la fin d'un commentaire."
  | Deprecated s -> "fonctionnalité dépréciée: " ^ s
  | Fragile_match "" ->
      "ce filtrage de motif est fragile."
  | Fragile_match s ->
      "ce filtrage de motif est fragile.\n\
       Il restera exhaustif lorsque des constructeur seront ajouté au type " ^ s ^ "."
  | Partial_application ->
      "cette application de fonction est partielle,\n\
       des argument manquent peut-être."
  | Labels_omitted ->
      "des labels ont été omis dans l'application de cette fonction."
  | Method_override [lab] ->
      "la méthode " ^ lab ^ " est redéfinie."
  | Method_override (cname :: slist) ->
      String.concat " "
        ("les méthodes suivantes sont redéfinies par la classe"
         :: cname  :: ":\n " :: slist)
  | Method_override [] -> affirme faux
  | Partial_match "" -> "ce filtrage de motif n'est pas exhaustif."
  | Partial_match s ->
      "ce filtrage de motif n'est pas exhaustif.\n\
       Ceci est un exemple de valeur qui n'est pas filtrée:\n" ^ s
  | Non_closed_record_pattern s ->
      "les labels suivants ne sont pas liés dans le motif d'enregistrement:\n" ^ s ^
      "\nVeillez soit lier ces label explicitement ou ajouter '; _' au motif."
  | Statement_type ->
      "cette expression devrait avoir le type unité."
  | Unused_match -> "ce cas de filtrage est inutile."
  | Unused_pat   -> "ce sous-filtrage est inutile."
  | Instance_variable_override [lab] ->
      "la variable d'instance " ^ lab ^ " est redéfinie.\n" ^
      "Le comportement a changé dans ocaml 3.10 (le comportement précédent était de cacher.)"
  | Instance_variable_override (cname :: slist) ->
      String.concat " "
        ("les variables d'instance suivantes sont redéfinies par la classe"
         :: cname  :: ":\n " :: slist) ^
      "\nLe comportement a changé dans ocaml 3.10 (le comportement précédant était de cacher.)"
  | Instance_variable_override [] -> affirme faux
  | Illegal_backslash -> "échappement par backslash illégal dans la chaîne."
  | Implicit_public_methods l ->
      "les méthodes privées suivantes ont été rendues publiques implicitement :\n "
      ^ String.concat " " l ^ "."
  | Unerasable_optional_argument -> "l'argument optionnel ne peut pas être supprimé."
  | Undeclared_virtual_method m -> "la méthode virtuelle "^m^" n'est pas déclarée."
  | Not_principal s -> s^" n'est pas principal."
  | Without_principality s -> s^" sans principalité."
  | Unused_argument -> "cet argument ne sera pas utilisé par la fonction."
  | Nonreturning_statement ->
      "cette instruction ne retourne jamais.)"
  | Camlp4 s -> s
  | Useless_record_with ->
      "tous les champs sont exlicitement listé dans cet enregistrement:\n\
       la clause 'with' est inutile."
  | Bad_module_name (modname) ->
      "nom de fichier source incorrect : \"" ^ modname ^ "\" n'est pas un nom de module valide."
  | All_clauses_guarded ->
      "mauvais style, toutes les clauses de ce filtrage de motif sont gardées."
  | Unused_var v | Unused_var_strict v -> "variable inutilisée " ^ v ^ "."
  | Wildcard_arg_to_constant_constr ->
     "motif joker donné en argument à un constructeur coonstant"
  | Eol_in_string ->
     "fin de ligne non échapée dans une constante de chaîne de caractères (code non portable)"
  | Duplicate_definitions (kind, cname, tc1, tc2) ->
      Printf.sprintf "le %s %s est défini dans les types %s et %s."
        kind cname tc1 tc2
  | Multiple_definition(modname, file1, file2) ->
      Printf.sprintf
        "les fichiers %s et %s définissent tous deux un module nommé %s"
        file1 file2 modname
  | Unused_value_declaration v -> "valeur inutilisée " ^ v ^ "."
  | Unused_open s -> "ouvrir inutile " ^ s ^ "."
  | Unused_type_declaration s -> "type inutilisé" ^ s ^ "."
  | Unused_for_index s -> "indice de boucle pour inutilisé " ^ s ^ "."
  | Unused_ancestor s -> "variable d'ancêtre inutilisée " ^ s ^ "."
  | Unused_constructor (s, faux, faux) -> "constructeur inutilisé " ^ s ^ "."
  | Unused_constructor (s, vrai, _) ->
      "le constructeur " ^ s ^
      " n'est jamais utilisé pour construire des valeurs.\n\
        (Cependant, ce constructeur apparaît dans des motifs.)"
  | Unused_constructor (s, faux, vrai) ->
      "le constructeur " ^ s ^
      " n'est jamais utilisé pour construire de valeurs.\n\
        Son type est exporté en tant que type privé."
  | Unused_exception (s, faux) ->
      "constructeur d'exception inutilisé " ^ s ^ "."
  | Unused_exception (s, vrai) ->
      "le constructeur d'exception " ^ s ^
      " n'est jamais levé ou utilisé pour construire des valeurs.\n\
        (Cependant, ce constructeur apparaît dans des motifs.)"
  | Unused_rec_flag ->
      "drapeau rec inutile."
  | Name_out_of_scope (ty, [nm], faux) ->
      nm ^ " a été selectionné depuis le type " ^ ty ^
      ".\nIl n'est pas visible dans la portée courante, et il ne sera pas \n\
       selectionné si le type devient inconnu."
  | Name_out_of_scope (_, _, faux) -> affirme faux
  | Name_out_of_scope (ty, slist, vrai) ->
      "cet enregistrement de type "^ ty ^" contient des champs qui ne sont \n\
       pas visible dans la portée courante : "
      ^ String.concat " " slist ^ ".\n\
       Ils ne seront plus selectionnés si le type devient inconnu."
  | Ambiguous_name ([s], tl, faux) ->
      s ^ " appartient à plusieurs types : " ^ String.concat " " tl ^
      "\nLe premier a été selectionné. Veuillez désambiguïser si cela est faux."
  | Ambiguous_name (_, _, faux) -> affirme faux
  | Ambiguous_name (slist, tl, vrai) ->
      "ces labels de champs appartiennent à plusieurs types : " ^
      String.concat " " tl ^
      "\nLe premier a été sélectionné? Veuillez désambiguïser si cela est faux."
  | Disambiguated_name s ->
      "cette utilisation de " ^ s ^ " a nécessité une désambiguïsation."
  | Nonoptional_label s ->
      "le label " ^ s ^ " n'est pas optionnel."
  | Open_shadow_identifier (kind, s) ->
      Printf.sprintf
        "cette instruction ouvrir cache l'identifiant de %s %s (qui est utilisé par la suite)"
        kind s
  | Open_shadow_label_constructor (kind, s) ->
      Printf.sprintf
        "cette instruction ouvrir cache le %s %s (qui est utilisé par la suite)"
        kind s
  | Bad_env_variable (var, s) ->
      Printf.sprintf "environnement de variable %s illégal : %s" var s
  | Attribute_payload (a, s) ->
      Printf.sprintf "charge utile illégale pour l'attribut '%s'.\n%s" a s
  | Eliminated_optional_arguments sl ->
      Printf.sprintf "élimination implicite d'argument optionnel%s %s"
        (si List.length sl = 1 alors "" sinon "s")
        (String.concat ", " sl)
;;

soit nerrors = ref 0;;

soit print ppf w =
  soit msg = message w dans
  soit num = number w dans
  soit newlines = ref 0 dans
  pour i = 0 à String.length msg - 1 faire
    si msg.[i] = '\n' alors incr newlines;
  fait;
  soit (out, flush, newline, space) =
    Format.pp_get_all_formatter_output_functions ppf ()
  dans
  soit countnewline x = incr newlines; newline x dans
  Format.pp_set_all_formatter_output_functions ppf out flush countnewline space;
  Format.fprintf ppf "%d: %s" num msg;
  Format.pp_print_flush ppf ();
  Format.pp_set_all_formatter_output_functions ppf out flush newline space;
  si error.(num) alors incr nerrors;
  !newlines
;;

exception Errors de int;;

soit check_fatal () =
  si !nerrors > 0 alors début
    soit e = Errors !nerrors dans
    nerrors := 0;
    raise e;
  fin;
;;

soit descriptions =
  [
    1, "Marque de début de commentaire suspecte.";
    2, "Marque de fin de commentaire suspecte.";
    3, "Fopnctionnalité dépréciée.";
    4, "Filtrage de mottif fragile : le filtrage restera complet même si\n\
   \    des constructeurs supplementaires sont ajoutés à l'un des types\n\
   \    sommes filtrés.";
    5, "Fonction appliquée partiellement : une expression dont le résultat\n\
   \    a un type de fonction et est ignoré.";
    6, "Label omis dans l'application de fonction.";
    7, "Méthode redéfinie.";
    8, "Filtrage partiel : cas manquant dans le filtrage de motif.";
    9, "Champs manquants dans un motif d'enregistrement.";
   10, "Expression au membre gauche d'une séquence qui n'a pas le type\n\
   \    \"unité\" (et qui n'est pas une fonction, voir avertissement n°5).";
   11, "Cas redondant dans un filtrage de motif (cas de filtrage inutilisé).";
   12, "Sous-motif redondant dans un filtrage de motif.";
   13, "Variable d'instance redéfinie.";
   14, "Échappement backslash illégal dans une constante de chaîne de caractères.";
   15, "Méthode privée rendue publique implicitement.";
   16, "Argument optionnel non effaçable.";
   17, "Méthodde virtuelle non déclarée.";
   18, "Type non principal.";
   19, "Type sans principalité.";
   20, "Argument de fonction inutilisé.";
   21, "Instruction ne retournant pas.";
   22, "Avertissement Chamellep4.";
   23, "Clause \"avec\" inutile dans un enregistrement.";
   24, "Nom de module incorrect : le nom du fichier source n'est pas un nome\n\
   \    de module Chamelle valide.";
   25, "Filtrage de motif dont toutes les clauses sont gardées. Le test\n\
   \    d'exhaustivité ne peut rien vérifier.";
   26, "Variable inutilisée suspecte : variable inutilisée qui est liée avec\n\
   \    \"soit\" ou \"comme\", et qui ne commence pas par un tiret bas (\"_\").";
   27, "Variable inutilisée innofensive : variable inutilisée qui n'est pas\n\
   \    liée avec \"soit\" ni \"comme\", et qui ne commence pas par un\n\
   \    tiret bas (\"_\").";
   28, "Motif joker donné en argument à un constructeur constant.";
   29, "Fin de line non échappée dans une constante de chaîne de caractères.";
   30, "Deux labels ou constructeurs de même nom sont définis dans deux types\n\
   \    mutuellement récursifs.";
   31, "Un module est lié deux fois dans le même exécutable.";
   32, "Déclaration de valeur inutilisée.";
   33, "Instruction ouvrir inutilisée.";
   34, "Déclaration de type inutilisée.";
   35, "Indice de boucle pour inutilisé.";
   36, "Variable d'ancêtre inutilisée.";
   37, "Constructeur inutilisé.";
   38, "Constructeur d'exception inutilisé.";
   39, "Drapeau rec inutilisé.";
   40, "Nom de constructeur ou de label utilisé hors de sa portée.";
   41, "Nom de constructeur ou de label ambigu.";
   42, "Nom de constructeur ou de labl désambiguïsé.";
   43, "Label non optionnel appliqué comme optionnel.";
   44, "L'instruction ouvrir cache un identifiant déjà défini.";
   45, "L'instruction ouvrir cache un label ou constructeur déjà défini.";
   46, "Variable d'environnement illégale.";
   47, "Charge utile d'attribut illégale.";
   48, "Élimination d'arguments optionnels implicite.";
  ]
;;

soit help_warnings () =
  List.iter (fonc (i, s) -> Printf.printf "%3i %s\n" i s) descriptions;
  print_endline "  A Tous les avertissements.";
  pour i = Char.code 'b' à Char.code 'z' faire
    soit c = Char.chr i dans
    filtre letter c avec
    | [] -> ()
    | [n] ->
        Printf.printf "  %c Synonyme pour l'avertissement %i.\n" (Char.uppercase c) n
    | l ->
        Printf.printf "  %c Ensemble d'avertissements %s.\n"
          (Char.uppercase c)
          (String.concat ", " (List.map string_of_int l))
  fait;
  exit 0
;;
