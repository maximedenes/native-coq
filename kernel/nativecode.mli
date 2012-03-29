open Names
open Declarations
open Pre_env
open Nativelambda

type mllambda
type global

type gname

val gname_of_con : constant -> gname

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

val compile_constant : env -> module_path -> label ->
  constant_body -> global * global list

val compile_constant_field : env -> module_path -> label ->
  Nativevalues.t list -> constant_body -> global * global list * Nativevalues.t list

val compile_mind : mutual_inductive_body -> mutual_inductive ->
  global list -> global list
val compile_mind_sig : mutual_inductive_body -> mutual_inductive ->
  (global * gname list) list -> (global * gname list) list

val compile_mind_field : mutual_inductive_body -> mutual_inductive ->
  global list -> Nativevalues.t list -> global list * Nativevalues.t list


val optimize_stk : global list -> global list
val mk_conv_code : env -> lambda -> lambda -> global list * global list
val mk_norm_code : env -> lambda -> global list * global list

val mk_library_header : dir_path -> global list -> global list

val mod_uid_of_dirpath : dir_path -> string

val get_values_tbl : unit -> Nativevalues.t array
