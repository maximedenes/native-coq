(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
type caml_prim =
  (* Int63 operations *)
  | Int63print
 
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
  
  (* Resource Operations *)
  | ResourceMake
  | ResourceGetc
  | ResourceGeti32

type iterator =
  | Int63foldi
  | Int63foldi_down
 
type prim_op = 
  | Int63head0
  | Int63tail0

  | Int63add
  | Int63sub
  | Int63mul
  | Int63div
  | Int63mod
  | Int63lsr
  | Int63lsl
  | Int63land
  | Int63lor
  | Int63lxor

  | Int63addc
  | Int63subc
  | Int63addCarryC
  | Int63subCarryC

  | Int63mulc
  | Int63diveucl
  | Int63div21

  | Int63addMulDiv

  | Int63eq
  | Int63lt
  | Int63le

  | Int63compare
  | Int63eqb_correct

type op =
  | Oprim of prim_op
  | Ocaml_prim of caml_prim
  | Oiterator of iterator



let caml_prim_to_string = function
  | Int63print -> "print"
  | ArrayMake -> "make"
  | ArrayGet -> "get"
  | ArrayGetdefault -> "default"
  | ArraySet -> "set"
  | ArrayCopy -> "copy"
  | ArrayReroot -> "reroot"
  | ArrayLength -> "length"
  | ArrayInit -> "init"
  | ArrayMap -> "map"
  | ResourceMake -> "rmake"
  | ResourceGetc -> "rgetc"
  | ResourceGeti32 -> "rgeti32"
  
let iterator_to_string = function
  | Int63foldi -> "foldi"
  | Int63foldi_down -> "foldi_down"

let prim_to_string = function 
  | Int63head0     -> "head0"
  | Int63tail0     -> "tail0"
  | Int63add       -> "add"
  | Int63sub       -> "sub"
  | Int63mul       -> "mul"
  | Int63div       -> "div"
  | Int63mod       -> "mod"
  | Int63lsr       -> "lsr"
  | Int63lsl       -> "lsl"
  | Int63land      -> "land"
  | Int63lor       -> "lor"
  | Int63lxor      -> "lxor"

  | Int63addc      -> "addc"
  | Int63subc      -> "subc"
  | Int63addCarryC -> "addcarryc"
  | Int63subCarryC -> "subcarryc"

  | Int63mulc      -> "mulc"
  | Int63diveucl   -> "diveucl"
  | Int63div21     -> "div21"

  | Int63addMulDiv -> "addmuldiv"

  | Int63eq        -> "eq"
  | Int63lt        -> "lt"
  | Int63le        -> "le"

  | Int63compare   -> "compare"
  | Int63eqb_correct -> "eqb_correct"

let to_string = function
  | Ocaml_prim op -> caml_prim_to_string op
  | Oiterator op  -> iterator_to_string op
  | Oprim op      -> prim_to_string op

type arg_kind =
  | Kparam (* not needed for the elavuation of the primitive*)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf *)

type args_red = arg_kind list

(* Invariant only argument of type int63, array or an inductive can
   have kind Kwhnf *)

let caml_prim_kind = function
  | Int63print  -> [Kwhnf] 
  | ArrayMake   -> [Kparam;Kwhnf;Karg]
  | ArrayGet    -> [Kparam;Kwhnf;Kwhnf]
  | ArraySet    -> [Kparam;Kwhnf;Kwhnf;Karg]
  | ArrayGetdefault | ArrayCopy | ArrayReroot 
  | ArrayLength -> [Kparam;Kwhnf]
  | ArrayInit -> [Kparam;Kwhnf;Karg;Karg]
  | ArrayMap -> [Kparam;Kparam;Karg;Kwhnf]
  | ResourceMake -> [Kwhnf]
  | ResourceGetc -> [Kwhnf;Kwhnf]
  | ResourceGeti32 -> [Kwhnf;Kwhnf]
	
let iterator_kind _ = [Kparam;Kparam;Karg;Kwhnf;Kwhnf;Karg]
    
let prim_kind = function
  | Int63head0 | Int63tail0 -> [Kwhnf]
	
  | Int63add | Int63sub | Int63mul 
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor
  | Int63addc | Int63subc
  | Int63addCarryC | Int63subCarryC  | Int63mulc | Int63diveucl
  | Int63eq | Int63lt | Int63le | Int63compare -> [Kwhnf; Kwhnf]

  | Int63div21 | Int63addMulDiv -> [Kwhnf; Kwhnf; Kwhnf]
  | Int63eqb_correct -> [Karg;Karg;Kwhnf]

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
  | Int63print -> (0,1)
  | ArrayInit -> (1,3)
  | ArrayMap -> (2,2)
  | ResourceMake -> (0,1)
  | ResourceGetc -> (0,2)
  | ResourceGeti32 -> (0,2)
	
let iterator_arity _ = (2, 4)
    
let prim_arity = function
  | Int63head0 | Int63tail0 -> (0,1)
  | Int63add | Int63sub | Int63mul 
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor
  | Int63addc | Int63subc
  | Int63addCarryC | Int63subCarryC  | Int63mulc | Int63diveucl 
  | Int63eq | Int63lt | Int63le  
  | Int63compare -> (0,2)
	
  | Int63div21 | Int63addMulDiv -> (0,3)
  | Int63eqb_correct -> (0,3)

let arity = function
  | Ocaml_prim op -> caml_prim_arity op
  | Oiterator op  -> iterator_arity op
  | Oprim op      -> prim_arity op
  
module type PARRAY = 
  sig 
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

 end

module Narray : PARRAY with type 'a t = 'a array =
  struct
    type 'a t = 'a array

    let of_array t = assert false

    let length p = Uint63.of_int (Array.length p - 1)

    let get p i = 
      let len = Uint63.of_int (Array.length p) in
      if Uint63.le Uint63.zero i && Uint63.lt i len then p.(Uint63.to_int i)
      else p.(Array.length p - 1)

    let set p i a = 
      let len = Uint63.of_int (Array.length p - 1) in
      if Uint63.le Uint63.zero i && Uint63.lt i len then
	let p' = Array.copy p in p'.(Uint63.to_int i) <- a; p'
      else p

    let default p = p.(Array.length p - 1)

    let make n def = 
      Array.make (Parray.trunc_size n) def
	
    let init n f def =
      let n = Parray.trunc_size n in
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
  | PT_int63
  | PT_array
  | PT_resource

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
  | PT_int63 -> "int63"
  | PT_array -> "array"
  | PT_resource -> "resource"

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t

