open Term
open Pre_env
open Univ
open Nativelib

val compile :
  env -> constr -> constr -> int

val compare :
  constraints -> constraints
