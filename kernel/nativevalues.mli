open Names

type t = t -> t

type accumulator

type tag = int
type arity = int

type reloc_table = (tag * arity) array

type case_annot = string * int * reloc_table

type sort_annot = string * int
      
type rec_pos = int

type atom =
  | Arel of int
  | Aid of string
  | Asort of sort_annot
  | Avar of identifier
  | Acase of accumulator * t * (t -> t) * case_annot
  | Afix of t * (t -> t) * rec_pos
  | Aprod of t * (t -> t)

(* Constructors *)

val mk_accu : atom -> t
val mk_rel_accu : int -> t
val mk_id_accu : string -> t
val mk_sort_accu : sort_annot -> t
val mk_var_accu : identifier -> t
val mk_sw_accu : accumulator -> t -> (t -> t) -> case_annot -> t
val mk_prod_accu : t -> t -> t
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
