(* Check that "where" clause behaves as if given independently of the  *)
(* definition (variant of bug #1132 submitted by Assia Mahboubi) *)

Fixpoint plus1 (n m:nat) {struct n} : nat :=
   match n with
   | O => m
   | S p => S (p+m)
   end
 where "n + m" := (plus1 n m) : nat_scope.

(* Check behaviour wrt yet empty levels (see Stephane's bug #1850) *)

Parameter P : Type -> Type -> Type -> Type.
Notation "e |= t --> v" := (P e t v)     (at level 100, t at level 54).
Check (nat |= nat --> nat).

(* Check that first non empty definition at an empty level can be of any
   associativity *)

Definition marker := O.
Notation "x +1" := (S x) (at level 8, left associativity).
Reset marker.
Notation "x +1" := (S x) (at level 8, right associativity).

(* Check that empty levels (here 8 and 2 in pattern) are added in the
   right order *)

Notation "' 'C_' G ( A )" := (A,G) (at level 8, G at level 2).

(* Check import of notations from within a section *)

Notation "+1 x" := (S x) (at level 25, x at level 9).
Section A. Require Import make_notation. End A.

(* Check use of "$" (see bug #1961) *)

Notation "$ x" := (id x) (at level 30).
Check ($ 5).

(* Check regression of bug #2087 *)

Notation "'exists' x , P" := (x, P)
   (at level 200, x ident, right associativity,	only parsing).

Definition foo P := let '(exists x, Q) := P in x = Q :> nat.

(* Check empty levels when extending binder_constr *)

Notation "'exists' x >= y , P" := (exists x, x >= y /\ P)%nat
   (at level 200, x ident, right associativity, y at level 69).

(* This used to loop at some time before r12491 *)

Notation R x := (@pair _ _ x).
Check (fun x:nat*nat => match x with R x y => (x,y) end).

(* Check multi-tokens recursive notations *)

Local Notation "[ a  # ; ..  # ; b ]" := (a + .. (b + 0) ..).   
Check [ 0 ].
Check [ 0 # ; 1 ].

(* Check well-scoping of alpha-renaming of private binders *)
(* see bug #2248 (thanks to Marc Lasson) *)

Notation "{ q , r | P }" := (fun (p:nat*nat), let (q, r) := p in P).
Check (fun p, {q,r| q + r = p}).

