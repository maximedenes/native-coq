(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
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
