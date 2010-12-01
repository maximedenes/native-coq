open Names
open Declarations
open Environ
open Nativecode

val dump_library : module_path -> env -> struct_expr_body -> global list
