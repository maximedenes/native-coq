open Names
open Declarations
open Environ
open Nativecode

type mod_field
type mod_expr

val dump_library : module_path -> env -> struct_expr_body ->
  mod_field list * symbol array

val pp_mod_fields : module_path -> Format.formatter -> mod_field list -> unit

val compile_library :
  dir_path -> mod_field list -> module_path -> string list -> string -> int
