val max_array_length32 : int
type 'a t
val length  : 'a t -> Uint31.t
val get     : 'a t -> Uint31.t -> 'a
val set     : 'a t -> Uint31.t -> 'a -> 'a t
val default : 'a t -> 'a 
val make    : Uint31.t -> 'a -> 'a t
val init    : Uint31.t -> (int -> 'a) -> 'a -> 'a t
val copy    : 'a t -> 'a t
val reroot  : 'a t -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t
  
    (* /!\ Unsafe function *)
val of_array : 'a array -> 'a t

