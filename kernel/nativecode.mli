open Names
open Term
open Pre_env
open Declarations
open Univ
open Nativelib

val const_lid : module_path -> constant -> MLast.expr * string

val mind_lid : module_path -> module_path * identifier -> MLast.ctyp * string

val mod_uid_of_dirpath : dir_path -> string

val relative_mp_of_mp : module_path -> module_path -> MLast.module_expr

val translate :
  ?annots:Nativelib.NbeAnnotTbl.t -> ?lift : int -> module_path ->
  env -> string -> constr ->
    MLast.str_item list  * NbeAnnotTbl.t

val opaque_const : module_path -> constant -> MLast.str_item list

val assums : module_path -> env -> constr -> string list

val translate_mind : 
   mutual_inductive_body -> MLast.str_item list

val compile_constant :
   Names.module_path -> env ->
   Names.constant -> Declarations.constant_body -> unit

val compile_mind : mutual_inductive_body -> unit

val translate_constant : env -> module_path -> label ->
   constant_body -> MLast.str_item list * Nativelib.NbeAnnotTbl.t


