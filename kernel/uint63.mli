type t

val uint_size : int
val maxuint31 : t

      (* conversion to int *)
val of_int : int -> t
val to_int : t -> int
val to_int2 : t -> int * int (* msb, lsb *)
val of_int64 : Int64.t -> t
(*
val of_uint : int -> t
*)

     (* convertion to a string *)
val to_string : t -> string
val of_string : string -> t

val compile : t -> string

(* constants *)
val zero    : t

      (* logical operations *)
val l_sl    : t -> t -> t
val l_sr    : t -> t -> t
val l_and   : t -> t -> t
val l_xor   : t -> t -> t
val l_or    : t -> t -> t

      (* Arithmetic operations *) 
val add     : t -> t -> t
val sub     : t -> t -> t
val mul     : t -> t -> t
val div     : t -> t -> t
val rem     : t -> t -> t
      
      (* Specific arithmetic operations *)
val mulc    : t -> t -> t * t
val addmuldiv : t -> t -> t -> t
val div21   : t -> t -> t -> t * t
      
      (* comparison *)
val lt      : t -> t -> bool
val eq      : t -> t -> bool
val le      : t -> t -> bool
val compare : t -> t -> int

      (* head and tail *)
val head0   : t -> t
val tail0   : t -> t
  
val foldi_cont :
  (t -> ('a -> 'b) -> 'a -> 'b) -> t -> t -> ('a -> 'b) -> 'a -> 'b
val foldi_down_cont :
  (t -> ('a -> 'b) -> 'a -> 'b) -> t -> t -> ('a -> 'b) -> 'a -> 'b
val print_uint : t -> t
