open Names
open Term
open Pre_env
open Univ

val translate : env -> constr -> MLast.expr
