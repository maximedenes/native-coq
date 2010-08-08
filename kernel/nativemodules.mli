open Names
open Declarations
open Environ

val dump_library : module_path -> env -> struct_expr_body ->
  MLast.str_item list * Nativelib.NbeAnnotTbl.t
