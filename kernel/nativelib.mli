open Names
open Term

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
    Lam of lam
  | Var of int
  | App of lam * lam array
  | Const_int of int
  | Const_block of int * lam array
  | Case of lam * (tag * int array * lam) array
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
