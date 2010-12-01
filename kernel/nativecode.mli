open Names
open Declarations
open Pre_env
open Nativelambda

type mllambda
type global

val mllambda_of_lambda : lambda -> global list *
   ((identifier * mllambda) list * (int * mllambda) list) * mllambda

val pp_mllam : module_path -> Format.formatter -> mllambda -> unit

val pp_globals : module_path -> Format.formatter -> global list -> unit

val mk_opens : string list -> global list
val mk_internal_let : string -> mllambda -> global

val compile_constant : env -> module_path -> label -> constant_body -> global
val compile_mind : 'a -> Names.mutual_inductive -> global

val conv_main_code : global list

val mod_uid_of_dirpath : dir_path -> string
