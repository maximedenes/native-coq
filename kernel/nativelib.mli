open Names
open Term

exception Bug of string

type term =
    Rel of int
  | Con of string
  | Lam1 of (term -> term)
  | Lam2 of (term -> term -> term)
  | Lam3 of (term -> term -> term -> term)
  | Lam4 of (term -> term -> term -> term -> term)
  | Lam5 of (term -> term -> term -> term -> term -> term)
  | Lam6 of (term -> term -> term -> term -> term -> term -> term)
  | Prod of (term * (term -> term))
  | App of term list
  | Match of (id_key * int * term array)
  | Set
  | Prop
  | Type of int
  | Const of (int * term array)
  | Var of identifier
  | Lambda of term
  | Product of (term * term)

type nbe_annotation =
  | CaseAnnot of case_info

module NbeAnnotTbl :
  sig
   type t

   val empty : t
   val add : nbe_annotation -> t -> t * int

  end


val array_iter2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> unit
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
val normalize : int -> term -> term
val print_nf : term -> unit
