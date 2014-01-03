Require Import Int63 List.

Import ListNotations.

Set Implicit Arguments.

Open Scope int63_scope.

Definition f (i : int) k (x : int) := i :: k (x+i).

Check (eq_refl : foldi_down_cont f 3 5 (fun x => [x]) = fun a : int => [a]).
Check (eq_refl (fun a : int => [a]) <: foldi_down_cont f 3 5 (fun x => [x]) = fun a : int => [a]).
Check (eq_refl (fun a : int => [a]) <<: foldi_down_cont f 3 5 (fun x => [x]) = fun a : int => [a]).
Definition compute1 := foldi_down_cont f 3 5 (fun x => [x]).
Check (eq_refl compute1 : (fun a : int => [a]) = (fun a : int => [a])).

Eval compute in foldi_down_cont f 5 3 (fun x => [x]).
Check (eq_refl : foldi_down_cont f 5 3 (fun x => [x]) = fun a : int => [5; 4; 3; a + 5 + 4 + 3]).
Check (eq_refl (fun a : int => [5; 4; 3; a + 5 + 4 + 3]) <: foldi_down_cont f 5 3 (fun x => [x]) = fun a : int => [5; 4; 3; a + 5 + 4 + 3]).
Check (eq_refl (fun a : int => [5; 4; 3; a + 5 + 4 + 3]) <<: foldi_down_cont f 5 3 (fun x => [x]) = fun a : int => [5; 4; 3; a + 5 + 4 + 3]).
Definition compute2 := foldi_down_cont f 5 3 (fun x => [x]).
Check (eq_refl compute2 : (fun a : int => [5; 4; 3; a + 5 + 4 + 3]) = (fun a : int => [5; 4; 3; a + 5 + 4 + 3])).