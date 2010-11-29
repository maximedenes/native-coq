open Term
open Pre_env
open Univ
open Nativelib

val conv_val : int -> Nativevalues.t -> Nativevalues.t -> unit

val compare :
  env -> constr -> constr -> constraints -> constraints
