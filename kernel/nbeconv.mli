open Term
open Pre_env
open Univ
open Nativelib

val env_name : string
val terms_name : string

val include_dirs : string
val include_libs : string

val compile :
  env -> constr -> constr -> values * values

val compare :
  values * values -> constraints -> constraints

val dump_env :
  constr list -> env -> (MLast.str_item * Ploc.t) list * 
      (Names.id_key * NbeAnnotTbl.t) Util.Stringmap.t

val print_implem :
  string -> (MLast.str_item * Ploc.t) list -> unit

val compute_loc :
  (MLast.str_item * Ploc.t) list -> (MLast.str_item * Ploc.t) list
