type caml_prim =
  (* Int31 operations *)
  | Int31print
 
  (* Array operations *)
  | ArrayMake
  | ArrayGet
  | ArrayGetdefault
  | ArraySet
  | ArrayCopy
  | ArrayReroot
  | ArrayLength
  | ArrayInit
  | ArrayMap

type iterator =
  | Int31foldi
  | Int31foldi_down
 
type prim_op = 
  | Int31head0
  | Int31tail0

  | Int31add
  | Int31sub
  | Int31mul
  | Int31div
  | Int31mod
  | Int31lsr
  | Int31lsl
  | Int31land
  | Int31lor
  | Int31lxor

  | Int31addc
  | Int31subc
  | Int31addCarryC
  | Int31subCarryC

  | Int31mulc
  | Int31diveucl
  | Int31div21

  | Int31addMulDiv

  | Int31eq
  | Int31lt
  | Int31le

  | Int31compare
  | Int31eqb_correct

type op =
  | Oprim of prim_op
  | Ocaml_prim of caml_prim
  | Oiterator of iterator



let caml_prim_to_string = function
  | Int31print -> "print"
  | ArrayMake -> "make"
  | ArrayGet -> "get"
  | ArrayGetdefault -> "default"
  | ArraySet -> "set"
  | ArrayCopy -> "copy"
  | ArrayReroot -> "reroot"
  | ArrayLength -> "length"
  | ArrayInit -> "init"
  | ArrayMap -> "map"
  
let iterator_to_string = function
  | Int31foldi -> "foldi"
  | Int31foldi_down -> "foldi_down"

let prim_to_string = function 
  | Int31head0     -> "head0"
  | Int31tail0     -> "tail0"
  | Int31add       -> "add"
  | Int31sub       -> "sub"
  | Int31mul       -> "mul"
  | Int31div       -> "div"
  | Int31mod       -> "mod"
  | Int31lsr       -> "lsr"
  | Int31lsl       -> "lsl"
  | Int31land      -> "land"
  | Int31lor       -> "lor"
  | Int31lxor      -> "lxor"

  | Int31addc      -> "addc"
  | Int31subc      -> "subc"
  | Int31addCarryC -> "addcarryc"
  | Int31subCarryC -> "subcarryc"

  | Int31mulc      -> "mulc"
  | Int31diveucl   -> "diveucl"
  | Int31div21     -> "div21"

  | Int31addMulDiv -> "addmuldiv"

  | Int31eq        -> "eq"
  | Int31lt        -> "lt"
  | Int31le        -> "le"

  | Int31compare   -> "compare"
  | Int31eqb_correct -> "eqb_correct"

let to_string = function
  | Ocaml_prim op -> caml_prim_to_string op
  | Oiterator op  -> iterator_to_string op
  | Oprim op      -> prim_to_string op

type arg_kind =
  | Kparam (* not needed for the elavuation of the primitive*)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf *)

type args_red = arg_kind list

(* Invariant only argument of type int31, array or an inductive can
   have kind Kwhnf *)

let caml_prim_kind = function
  | Int31print  -> [Kwhnf] 
  | ArrayMake   -> [Kparam;Kwhnf;Karg]
  | ArrayGet    -> [Kparam;Kwhnf;Kwhnf]
  | ArraySet    -> [Kparam;Kwhnf;Kwhnf;Karg]
  | ArrayGetdefault | ArrayCopy | ArrayReroot 
  | ArrayLength -> [Kparam;Kwhnf]
  | ArrayInit -> [Kparam;Kwhnf;Karg;Karg]
  | ArrayMap -> [Kparam;Kparam;Karg;Kwhnf]
	
let iterator_kind _ = [Kparam;Kparam;Karg;Kwhnf;Kwhnf;Karg]
    
let prim_kind = function
  | Int31head0 | Int31tail0 -> [Kwhnf]
	
  | Int31add | Int31sub | Int31mul 
  | Int31div | Int31mod
  | Int31lsr | Int31lsl
  | Int31land | Int31lor | Int31lxor
  | Int31addc | Int31subc
  | Int31addCarryC | Int31subCarryC  | Int31mulc | Int31diveucl
  | Int31eq | Int31lt | Int31le | Int31compare -> [Kwhnf; Kwhnf]

  | Int31div21 | Int31addMulDiv -> [Kwhnf; Kwhnf; Kwhnf]
  | Int31eqb_correct -> [Karg;Karg;Kwhnf]

let op_kind = function
  | Ocaml_prim op -> caml_prim_kind op
  | Oiterator op  -> iterator_kind op
  | Oprim op      -> prim_kind op
	
	
let caml_prim_arity = function
  | ArrayMake -> (1,2)
  | ArrayGet -> (1,2)
  | ArrayGetdefault -> (1,1)
  | ArraySet -> (1,3)
  | ArrayCopy | ArrayReroot -> (1,1)
  | ArrayLength -> (1,1)
  | Int31print -> (0,1)
  | ArrayInit -> (1,3)
  | ArrayMap -> (2,2)
	
let iterator_arity _ = (2, 4)
    
let prim_arity = function
  | Int31head0 | Int31tail0 -> (0,1)
  | Int31add | Int31sub | Int31mul 
  | Int31div | Int31mod
  | Int31lsr | Int31lsl
  | Int31land | Int31lor | Int31lxor
  | Int31addc | Int31subc
  | Int31addCarryC | Int31subCarryC  | Int31mulc | Int31diveucl 
  | Int31eq | Int31lt | Int31le  
  | Int31compare -> (0,2)
	
  | Int31div21 | Int31addMulDiv -> (0,3)
  | Int31eqb_correct -> (0,3)

let arity = function
  | Ocaml_prim op -> caml_prim_arity op
  | Oiterator op  -> iterator_arity op
  | Oprim op      -> prim_arity op
  
module type PARRAY = 
  sig 
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

 end

let max_array_length32 = Parray.max_array_length32
	    
module Narray : PARRAY with type 'a t = 'a array =
  struct
    type 'a t = 'a array

    let of_array t = assert false

    let length p = Uint31.of_int (Array.length p - 1)

    let get p i = 
      let i = Uint31.to_int i in
      if 0 <= i && i < Array.length p then p.(i)
      else p.(Array.length p - 1)

    let set p i a = 
      let i = Uint31.to_int i in
      if 0 <= i && i < Array.length p - 1 then
	let p' = Array.copy p in p'.(i) <- a; p'
      else p

    let default p = p.(Array.length p - 1)

    let make n def = 
      let n = Uint31.to_int n in
      let n = 
	if 0 <= n && n < max_array_length32 then n + 1 
	else max_array_length32 in
      Array.make n def
	
    let init n f def =
      let n = Uint31.to_int n in
      let n = 
	if 0 <= n && n < max_array_length32 then n + 1 
	else max_array_length32 in
      let t = Array.make n def in
      for i = 0 to n - 2 do t.(i) <- f i done;
      t

    let copy p = p
    let reroot p = p

    let map = Array.map

  end


(** Special Entries for Register **)

type prim_ind =
  | PIT_bool
  | PIT_carry
  | PIT_pair
  | PIT_cmp
  | PIT_eq

type prim_type =
  | PT_int31
  | PT_array

type retro_action =
  | Retro_ind of prim_ind
  | Retro_type of prim_type
  | Retro_inline 

type op_or_type = 
  | OT_op of op
  | OT_type of prim_type


let prim_ind_to_string = function
  | PIT_bool -> "bool"
  | PIT_carry -> "carry"
  | PIT_pair -> "pair"
  | PIT_cmp -> "cmp"
  | PIT_eq -> "eq"

let prim_type_to_string = function
  | PT_int31 -> "int31"
  | PT_array -> "array"

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t

