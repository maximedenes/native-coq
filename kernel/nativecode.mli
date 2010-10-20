open Names
open Term
open Pre_env
open Univ
open Nativelib

val string_of_con : constant -> string

val translate : env -> id_key -> constr -> MLast.str_item list  * NbeAnnotTbl.t

val opaque_const : constant -> MLast.str_item list

val assums : env -> constr -> string list

val add_dummy_loc : MLast.str_item list -> (MLast.str_item * Ploc.t) list

val translate_ind : env ->
           Names.inductive ->
           Declarations.mutual_inductive_body *
           Declarations.one_inductive_body -> (MLast.str_item * Ploc.t) list
