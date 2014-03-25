(* -------------------------------------------------------------------- *)
type t
<<<<<<< HEAD

val eq : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val make : Uint63.t array -> t
val getc : t -> Uint63.t -> Uint63.t
val geti32 : t -> Uint63.t -> Uint63.t
=======

(* -------------------------------------------------------------------- *)
val eq      : t -> t -> bool
val compare : t -> t -> int
val hash    : t -> int
>>>>>>> e20d93a203ac379b21f8558265f2c7089b9d360f

(* -------------------------------------------------------------------- *)
val create  : string -> t
val get1    : t -> int
val getle32 : t -> int
