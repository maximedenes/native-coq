open Term
open Pre_env
open Univ
open Nativelib

val conv_val : Nativevalues.t -> Nativevalues.t -> unit

val compare :
  env -> constr -> constr -> constraints -> constraints
