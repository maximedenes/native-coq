open Names
open Term
open Pre_env
open Univ
open Nativelib

val string_of_con : constant -> string

val translate : env -> id_key -> constr -> MLast.expr * NbeAnnotTbl.t

val opaque_const : constant -> MLast.expr

val assums : env -> constr -> string list

val translate_ind : env ->
           Names.inductive ->
           Declarations.mutual_inductive_body *
           Declarations.one_inductive_body -> MLast.str_item * Ploc.t
