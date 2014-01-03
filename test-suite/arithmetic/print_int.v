Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : print_int 1 = 1).
Check (eq_refl 1 <: print_int 1 = 1).
Check (eq_refl 1 <<: print_int 1 = 1).
Definition compute1 := Eval compute in print_int 1.
Check (eq_refl compute1 : 1 = 1).

Check (eq_refl : print_int 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: print_int 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: print_int 9223372036854775807 = 9223372036854775807).

Definition compute2 := Eval compute in print_int 9223372036854775807.
Check (eq_refl compute2 : 9223372036854775807 = 9223372036854775807).