open Term
open Names

type t = t -> t

type accumulator

type tag = int
type arity = int

type reloc_table = (tag * arity) array

type sort_annot = string * int
      
type rec_pos = int

type atom =
  | Arel of int
  | Aconstant of constant
  | Aind of inductive
  | Asort of sorts
  | Avar of identifier
  | Acase of accumulator * t * (t -> t) * reloc_table * case_info
  | Afix of t * (t -> t) * rec_pos
  | Aprod of name * t * (t -> t)

type atom_fix = atom 
val dummy_atom_fix : t -> int -> (*int -> int ->*) atom_fix
val upd_fix_atom : atom_fix -> t -> unit

(* Constructors *)

val mk_accu : atom -> t
val mk_rel_accu : int -> t
val mk_constant_accu : constant -> t
val mk_ind_accu : inductive -> t
val mk_sort_accu : sorts -> t
val mk_var_accu : identifier -> t
val mk_sw_accu : accumulator -> t -> (t -> t) -> reloc_table -> case_info -> t
val mk_prod_accu : name -> t -> t -> t
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
