open Names
open Term
open Nativevalues
open Nativecode
open Nativemodules

exception NotConvertible

val include_dirs : string

val load_paths : string list ref
val imports : string list ref

val compiler_name : string
val comp_result : (int * string * string) option ref

val load_obj : (string -> unit) ref

val topological_sort :
  Util.Stringset.elt list ->
  ('a * 'b * 'c list * Util.Stringset.elt list) Util.Stringmap.t ->
  'c list * ('a * 'b) Util.Stringmap.t

val push_comp_stack :
  global -> global list -> unit

val compile_terms :
  module_path -> global list -> global list -> int * string * string

val call_linker :
  string -> unit

exception Bug of string

type nbe_annotation =
  | CaseAnnot of case_info
  | SortAnnot of sorts

module NbeAnnotTbl :
  sig
   type t

   val empty : t
   val add : nbe_annotation -> t -> t * int

   val find : int -> t -> nbe_annotation

  end


val rt1 : Nativevalues.t ref
val rt2 : Nativevalues.t ref

val extern_state : string -> unit
val intern_state : string -> unit
