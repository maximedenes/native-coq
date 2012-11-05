(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Term
open Names
open Declarations
open Pre_env
open Nativelambda

type mllambda
type global

type gname

val relative_list_of_mp : module_path -> module_path -> string list

val compile_with_fv : env -> global list -> label option -> lambda ->
  global list * mllambda

val pp_gname : module_path option -> Format.formatter -> gname -> unit
val pp_mllam : module_path -> Format.formatter -> mllambda -> unit

val pp_global : module_path -> Format.formatter -> global -> unit
val pp_global_aux : module_path -> Format.formatter -> global -> global list -> unit
val pp_globals : module_path -> Format.formatter -> global list -> unit

val mk_open : string -> global
val mk_internal_let : string -> mllambda -> global

type symbol

val get_value : symbol array -> int -> Nativevalues.t

val get_sort : symbol array -> int -> sorts

val get_name : symbol array -> int -> name

val get_const : symbol array -> int -> constant

val get_match : symbol array -> int -> Nativevalues.annot_sw

val get_ind : symbol array -> int -> inductive

val get_symbols_tbl : unit -> symbol array

type code_location_update
type code_location_updates
type linkable_code = global list * code_location_updates

val compile_constant : env -> module_path -> label ->
  constr_substituted constant_def -> global * global list * native_name

val compile_constant_field : env -> module_path -> label ->
  symbol list -> constant_body ->
    global * global list * symbol list * code_location_update

val compile_mind_sig : mutual_inductive_body -> mutual_inductive ->
  (global * gname list) list -> (global * gname list) list

val compile_mind_field : mutual_inductive_body -> mutual_inductive ->
  symbol list -> code_location_update list ->
    global list * symbol list * code_location_update list

val optimize_stk : global list -> global list
val mk_conv_code : env -> constr -> constr -> linkable_code
val mk_norm_code : env -> constr -> linkable_code

val mk_library_header : dir_path -> global list -> global list

val mod_uid_of_dirpath : dir_path -> string

val compile_deps : Pre_env.env -> linkable_code -> Term.constr -> linkable_code

val update_location : code_location_update -> unit
val update_locations : code_location_updates -> unit
