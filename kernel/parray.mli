val max_array_length32 : int
type 'a t
val length  : 'a t -> Uint63.t
val get     : 'a t -> Uint63.t -> 'a
val set     : 'a t -> Uint63.t -> 'a -> 'a t
val default : 'a t -> 'a 
val make    : Uint63.t -> 'a -> 'a t
val init    : Uint63.t -> (int -> 'a) -> 'a -> 'a t
val copy    : 'a t -> 'a t
val reroot  : 'a t -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t
  
    (* /!\ Unsafe function *)
val of_array : 'a array -> 'a t

