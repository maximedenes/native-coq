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

val dump_library : module_path -> dir_path -> env -> struct_expr_body ->
  mod_field list * symbol array * code_location_update list

val compile_library :
  dir_path -> mod_field list -> string list -> string -> int
