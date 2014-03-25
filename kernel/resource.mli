type t

val eq : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val make : Uint63.t array -> t
val getc : t -> Uint63.t -> Uint63.t
val geti32 : t -> Uint63.t -> Uint63.t

