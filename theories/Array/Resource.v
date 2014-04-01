Require Import Int63Native.
Require Import PArray.
Require Import String.
Require Import Ascii.
Local Open Scope int63_scope.


Register resource : Set as resource_type.
Register make : array int -> resource as resource_make.
Register getc : resource -> int -> int as resource_getc.
Register geti : resource -> int -> int as resource_geti32.

Definition int_of_bool (b:bool) := if b then 1 else 0.

Definition int_of_char (c:ascii) :=
  let (b0,b1,b2,b3,b4,b5,b6,b7) := c in 
  let i := int_of_bool b7 in
  let i := lsl i 1 + int_of_bool b6 in
  let i := lsl i 1 + int_of_bool b5 in
  let i := lsl i 1 + int_of_bool b4 in
  let i := lsl i 1 + int_of_bool b3 in
  let i := lsl i 1 + int_of_bool b2 in
  let i := lsl i 1 + int_of_bool b1 in
           lsl i 1 + int_of_bool b0.

Fixpoint fill (t:array int) (p:int) (s:string) :=
  match s with
  | EmptyString => t 
  | String c s => let t := set t p (int_of_char c) in fill t (p+1) s
  end.

Fixpoint slength (s:string) : int := 
  match s with
  | EmptyString => 0
  | String _ s => slength s + 1
  end.
  
Coercion ints_of_string s := 
  let len := slength s in
  fill (PArray.make len 0) 0 s.



