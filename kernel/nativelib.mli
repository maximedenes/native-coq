(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Term
open Nativevalues
open Nativecode
open Nativemodules
open Pre_env

(* This file provides facilities to access the native code compiler *)

val include_dirs : string

val load_paths : string list ref
val imports : string list ref

val compiler_name : string
val init_opens : global list

val load_obj : (string -> unit) ref

val topological_sort :
  Util.Stringset.elt list ->
  ('a * 'b * 'c list * Util.Stringset.elt list) Util.Stringmap.t ->
  'c list * ('a * 'b) Util.Stringmap.t

val call_compiler :
  module_path -> global list -> int * string * string

val call_linker :
  env -> string -> string option -> code_location_updates option -> unit

val rt1 : Nativevalues.t ref
val rt2 : Nativevalues.t ref

val extern_state : string -> unit
val intern_state : string -> unit
