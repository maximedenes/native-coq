Require Import Int63 List.

Import ListNotations.

Set Implicit Arguments.

Open Scope int63_scope.

Definition f (i : int) k (x : int) := i :: k (x+i).

Check (eq_refl : foldi_cont f 3 5 (fun x => [x]) = fun a : int => [3; 4; 5; a + 3 + 4 + 5]).
Check (eq_refl (fun a : int => [3; 4; 5; a + 3 + 4 + 5]) <: foldi_cont f 3 5 (fun x => [x]) = fun a : int => [3; 4; 5; a + 3 + 4 + 5]).
Check (eq_refl (fun a : int => [3; 4; 5; a + 3 + 4 + 5]) <<: foldi_cont f 3 5 (fun x => [x]) = fun a : int => [3; 4; 5; a + 3 + 4 + 5]).
Definition compute1 := foldi_cont f 3 5 (fun x => [x]).
Check (eq_refl compute1 : (fun a : int => [3; 4; 5; a + 3 + 4 + 5]) = (fun a : int => [3; 4; 5; a + 3 + 4 + 5])).

Check (eq_refl : foldi_cont f 5 3 (fun x => [x]) = fun a : int => [a]).
Check (eq_refl (fun a : int => [a]) <: foldi_cont f 5 3 (fun x => [x]) = fun a : int => [a]).
Check (eq_refl (fun a : int => [a]) <<: foldi_cont f 5 3 (fun x => [x]) = fun a : int => [a]).
Definition compute2 := foldi_cont f 5 3 (fun x => [x]).
Check (eq_refl compute2 : (fun a : int => [a]) = (fun a : int => [a])).