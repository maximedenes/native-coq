open Names
open Term


(* Global utilies for interface with OCaml *)
val print_implem :
  string -> (MLast.str_item * MLast.loc) list -> unit

val topological_sort :
  Util.Stringset.elt list ->
  ('a * 'b * 'c list * Util.Stringset.elt list) Util.Stringmap.t ->
  'c list * ('a * 'b) Util.Stringmap.t

val compile_module :
  values list -> string list -> string list -> string -> int

val call_compiler :
  MLast.str_item list -> MLast.str_item list -> int


exception Bug of string

type nbe_annotation =
  | CaseAnnot of case_info

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
  | Id of string
  | Var of identifier
  | App of lam * lam array
  | Const_int of int
  | Const_block of int * lam array
  | Case of string * int * lam * lam * lam array
  | Prod of lam * lam
  | Fix of int * lam 

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
