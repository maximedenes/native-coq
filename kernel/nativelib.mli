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
open Pre_env

(* This file provides facilities to access the native code compiler *)

val get_load_paths : (unit -> string list) ref

val load_obj : (string -> unit) ref

val get_ml_filename : unit -> string * string

val write_ml_code : string ->
  ?header:Nativecode.global list -> global list -> unit

val call_compiler : string -> string list -> bool * string

val compile : string -> global list -> bool * string

val call_linker :
  string -> string -> code_location_updates option -> unit

val rt1 : Nativevalues.t ref
val rt2 : Nativevalues.t ref
