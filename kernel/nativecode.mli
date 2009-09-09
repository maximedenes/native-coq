open Names
open Term
open Environ
open Univ

val translate : env -> constr -> MLast.expr
val compile : env -> constr -> constr -> values * values
val compare : values * values -> Univ.constraints -> Univ.constraints
