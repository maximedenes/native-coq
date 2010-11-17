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
  | Afix of t * (t -> t) * rec_pos * name * t
  | Aprod of name * t * (t -> t)

type atom_fix = atom 
val dummy_atom_fix : t -> int -> name -> t -> atom_fix
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

val mk_uint : int -> t

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
  | Vaccu of accumulator
  | Vfun of (t -> t)
  | Vconst of int
  | Vblock of block
  | Varray of t Native.Parray.t 

val kind_of_value : t -> kind_of_value

(* *)
val is_accu : t -> bool

(*** Primitive sur les entiers *)

val head0 : t -> t -> t
val tail0 : t -> t -> t

val add : t -> t -> t -> t
val sub : t -> t -> t -> t
val mul : t -> t -> t -> t
val div : t -> t -> t -> t
val rem : t -> t -> t -> t

val l_sr  : t -> t -> t -> t
val l_sl  : t -> t -> t -> t
val l_and : t -> t -> t -> t
val l_xor : t -> t -> t -> t
val l_or  : t -> t -> t -> t

val addc      : t -> t -> t -> t
val subc      : t -> t -> t -> t
val addCarryC : t -> t -> t -> t
val subCarryC : t -> t -> t -> t

val mulc    : t -> t -> t -> t
val diveucl : t -> t -> t -> t

val div21     : t -> t -> t -> t -> t
val addMulDiv : t -> t -> t -> t -> t

val eq      : t -> t -> t -> t
val lt      : t -> t -> t -> t
val le      : t -> t -> t -> t
val compare : t -> t -> t -> t 

val eqb_correct : t -> t -> t -> t -> t

val print : t -> t -> t
val foldi_cont : t -> t -> t -> t -> t -> t -> t -> t
val foldi_down_cont : t -> t -> t -> t -> t -> t -> t -> t

val arraymake    : t -> t -> t -> t -> t      (* accu A n def *)
val arrayget     : t -> t -> t -> t -> t      (* accu A t n *)
val arraydefault : t -> t -> t -> t           (* accu A t *)
val arrayset     : t -> t -> t -> t -> t -> t (* accu A t n v *)
val arraycopy    : t -> t -> t -> t           (* accu A t *)
val arrayreroot  : t -> t -> t -> t           (* accu A t *)
val arraylength  : t -> t -> t -> t           (* accu A t *)
