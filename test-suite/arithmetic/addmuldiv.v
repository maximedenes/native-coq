Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.


Eval compute in 5 << 50.
Eval compute in 5629499534213120 >> 31.
Eval compute in addmuldiv 32 3 5629499534213120.
Eval compute in addmuldiv_def 32 3 5629499534213120.

Check (eq_refl : addmuldiv 32 3 5629499534213120 = 12887523328).
Check (eq_refl 12887523328 <: addmuldiv 32 3 5629499534213120 = 12887523328).
Check (eq_refl 12887523328 <<: addmuldiv 32 3 5629499534213120 = 12887523328).
Definition compute2 := Eval compute in addmuldiv 32 3 5629499534213120.
Check (eq_refl compute2 : 12887523328 = 12887523328).