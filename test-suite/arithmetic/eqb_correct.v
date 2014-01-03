Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : eqb_correct 1 1 eq_refl = eq_refl).
Check (eq_refl (eq_refl 1) <: eqb_correct 1 1 eq_refl = eq_refl).
Check (eq_refl (eq_refl 1) <<: eqb_correct 1 1 eq_refl = eq_refl).
Definition compute1 := Eval compute in eqb_correct 1 1 eq_refl.
Check (eq_refl compute1 : eq_refl = eq_refl).