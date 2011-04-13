open Names
open Declarations
open Pre_env
open Nativelambda

type mllambda
type global

type gname

val gname_of_con : constant -> gname

val relative_list_of_mp : module_path -> module_path -> string list

val mllambda_of_lambda : global list -> label option -> lambda -> global list *
   ((identifier * mllambda) list * (int * mllambda) list) * mllambda

val pp_gname : module_path option -> Format.formatter -> gname -> unit
val pp_mllam : module_path -> Format.formatter -> mllambda -> unit

val pp_global : module_path -> Format.formatter -> global -> unit
val pp_global_aux : module_path -> Format.formatter -> global -> global list -> unit
val pp_globals : module_path -> Format.formatter -> global list -> unit

val mk_open : string -> global
val mk_internal_let : string -> mllambda -> global

val compile_constant : env -> module_path -> label ->
  constant_body -> global * global list

val compile_mind : mutual_inductive_body -> mutual_inductive ->
  global list -> global list
val compile_mind_sig : mutual_inductive_body -> mutual_inductive ->
  (global * gname list) list -> (global * gname list) list


val optimize_stk : global list -> global list
val conv_main_code : global list
val norm_main_code : global list

val mod_uid_of_dirpath : dir_path -> string
