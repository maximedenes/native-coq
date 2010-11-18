open Names
open Term
open Pre_env
open Declarations
open Univ

type constr_name = string

type lname = string

type global_name = string

type primitive =
  | Mk_prod of lname
  | Mk_sort of sorts
  | Is_accu
  | Is_int

type mllambda =
  | Lrel          of (lname * int)
  | Lglobal       of global_name 
  | Lprimitive    of primitive
  | Llam          of lname array * mllambda 
  | Lletrec       of (lname * lname array * mllambda) array * mllambda
  | Llet          of lname * mllambda * mllambda
  | Lapp          of mllambda * mllambda array
  | Lif           of mllambda * mllambda * mllambda
  | Lmatch        of mllambda * (constr_name * lname array * mllambda) array
  | Lconstruct    of constr_name * mllambda array
  | Lint          of int
  | Lparray       of mllambda array


(*
val const_lid : module_path -> constant -> MLast.expr * string

val mind_lid : module_path -> module_path * identifier -> MLast.ctyp * string

val mod_uid_of_dirpath : dir_path -> string

val relative_mp_of_mp : module_path -> module_path -> MLast.module_expr

val translate :
  > ?lift : int -> module_path ->
  env -> string -> constr ->
    MLast.str_item list  * NbeAnnotTbl.t

val opaque_const : module_path -> constant -> MLast.str_item list

val assums : module_path -> env -> constr -> string list

val translate_mind : 
   mutual_inductive_body -> mutual_inductive -> MLast.str_item list

val compile_constant :
   Names.module_path -> env ->
   Names.constant -> Declarations.constant_body -> unit

val compile_mind : mutual_inductive_body -> mutual_inductive -> unit

val translate_constant : env -> module_path -> label ->
   constant_body -> MLast.str_item list * Nativelib.NbeAnnotTbl.t
*)
