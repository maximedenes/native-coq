open Names
open Term
open Pre_env
open Declarations
open Univ
open Nativelib

val lid_of_con : module_path -> constant -> MLast.expr * string

val const_lid_of_id : identifier -> string

val mod_uid_of_dirpath : dir_path -> string

val translate :
  ?annots:Nativelib.NbeAnnotTbl.t -> module_path ->
  env -> MLast.expr * string -> constr ->
    MLast.str_item list  * NbeAnnotTbl.t

val opaque_const : module_path -> constant -> MLast.str_item list

val assums : module_path -> env -> constr -> string list

val translate_mind : 
   mutual_inductive_body -> MLast.str_item list

val dump_env :
  constr list -> env -> MLast.str_item list * 
      (Names.id_key * NbeAnnotTbl.t) Util.Stringmap.t

val dump_library : module_path -> env -> struct_expr_body ->
  MLast.str_item list * Nativelib.NbeAnnotTbl.t

