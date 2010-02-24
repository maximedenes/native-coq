type term = Con of string
	    | Lam of (term -> term)
	    | Prod of term * (term -> term)
	    | App of term * term
	    | Set
	    | Prop
	    | Type of int
	    | Const of int * term array

val app : term -> term -> term
val compare : int -> term -> term -> unit
val bug : term -> 'a
