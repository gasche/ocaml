
(* Remove type annotation from functions which will not benefit from
   parameter type specialisation *)

val function_constraints : (Clambda.ufunction * Clambda.function_description) list -> unit

val specialised : Clambda.ufunction -> bool
val specialised' : Clambda.function_description -> bool
