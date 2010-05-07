open Names
open Term
open Pre_env
open Univ

val string_of_con : constant -> string

val translate : env -> constr -> MLast.expr

val opaque_const : constant -> MLast.expr

val assums : constr -> string list
