open Names

type t = t -> t

type accumulator

type tag = int
type arity = int

type kind_of_constructor = KOCconst of tag | KOCblock of tag * arity

type case_tbl = kind_of_constructor array
      
type rec_pos = int

type atom =
  | Arel of int
  | Aid of string
  | Avar of identifier
  | Acase of accumulator * (t -> t) * case_tbl
  | Afix of t * (t -> t) * rec_pos

(* Constructors *)

val mk_accu : atom -> t
val mk_rel_accu : int -> t
val mk_id_accu : string -> t
val mk_var_accu : identifier -> t
val mk_sw_accu : accumulator -> (t -> t) -> case_tbl -> t
val mk_fix_accu : atom -> t

val mk_const : tag -> t
val mk_block : tag -> t array -> t

(* Functions over accumulators *)

val dummy_atom : atom    
val atom_of_accu : accumulator -> atom
val arg_of_accu : accumulator -> int -> t
val accu_nargs : accumulator -> int

val cast_accu : t -> accumulator
(* Functions over block: i.e constructors *)
    
type block
      
val block_size : block -> int
val block_field : block -> int -> t
val block_tag : block -> int

(* kind_of_value *)

type kind_of_value =
    Vaccu of accumulator
  | Vfun of (t -> t)
  | Vconst of int
  | Vblock of block

val kind_of_value : t -> kind_of_value

(* *)
val is_accu : t -> bool
