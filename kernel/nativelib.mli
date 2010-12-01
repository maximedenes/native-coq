open Names
open Term
open Nativevalues
open Nativecode

exception NotConvertible

val load_paths : string list ref
val imports : string list ref

val topological_sort :
  Util.Stringset.elt list ->
  ('a * 'b * 'c list * Util.Stringset.elt list) Util.Stringmap.t ->
  'c list * ('a * 'b) Util.Stringmap.t

val compile_module :
  mllambda -> string list -> string -> int

val push_comp_stack :
  mllambda list -> unit

val compile_terms :
  module_path -> global list -> int * string * string

val call_linker :
  string -> string -> unit

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

type tag

type lam = 
  | Lam of lam
  | Rel of int
  | Constant of constant
  | Ind of inductive
  | Sort of sorts
  | Var of identifier
  | App of lam * lam array
  | Const_int of int
  | Const_block of int * lam array
  | Case of lam * lam * lam array * case_info
  | Prod of name * lam * lam
  | Fix of name * rec_pos * lam * lam 
  | Array of lam array

val rnorm : lam ref

(*val array_iter2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> unit
val string_of_term : int -> term -> string
val bug : term -> 'a
val app1 : term -> term -> term
val app2 : term -> term -> term -> term
val app3 : term -> term -> term -> term -> term
val app4 : term -> term -> term -> term -> term -> term
val app5 : term -> term -> term -> term -> term -> term -> term
val app6 : term -> term -> term -> term -> term -> term -> term -> term
val app : term -> term -> term
val compare : int -> term -> term -> unit
val normalize : int -> term -> term*)
val print_nf : Nativevalues.t Lazy.t -> unit
val lazy_norm : Nativevalues.t Lazy.t -> lam

val extern_state : string -> unit
val intern_state : string -> unit

val compile_mind : 'a -> 'b -> 'c
