open Names
open Term
open Pre_env
open Univ
open Nativelib

val lid_of_con : constant -> string

val const_lid_of_id : identifier -> string

val mod_uid_of_dirpath : dir_path -> string

val translate :
  ?annots:Nativelib.NbeAnnotTbl.t ->
  env -> string -> constr -> MLast.str_item list  * NbeAnnotTbl.t

val opaque_const : constant -> MLast.str_item list

val assums : env -> constr -> string list

val translate_ind : 
   Declarations.mutual_inductive_body *
   Declarations.one_inductive_body -> MLast.str_item list

val dump_env :
  constr list -> env -> MLast.str_item list * 
      (Names.id_key * NbeAnnotTbl.t) Util.Stringmap.t
