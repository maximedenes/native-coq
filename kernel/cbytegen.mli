open Names
open Cbytecodes
open Cemitcodes 
open Term
open Declarations
open Pre_env


val compile : env -> constr -> bytecodes * bytecodes * fv
                              (** init, fun, fv *)

val compile_constant_body : env -> constr_substituted constant_def -> body_code

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : constant -> body_code
