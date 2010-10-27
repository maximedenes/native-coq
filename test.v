Require Import Int31.
Open Scope int31_scope.

Definition is_prim x :=
 if x <= 1 then false
 else negb (existsb (fun p => x \% p == 0) 2 (x - 1)).

 
Eval native_compute in is_prim 2.

Eval native_compute in is_prim 3.

Eval native_compute in is_prim 4.

Time Eval native_compute in is_prim 12553.
(* Finished transaction in 0. secs (0.005999u,0.009999s) *)
Time Eval vm_compute in is_prim 12553.
(* Finished transaction in 0. secs (0.001u,0.s) *)

Time Eval native_compute in is_prim 200075999.
(*Finished transaction in 19. secs (18.771146u,0.012998s)*)
Time Eval vm_compute in is_prim 200075999.
(*Finished transaction in 14. secs (14.288828u,0.002s) *)

Eval native_compute in is_prim 1859843159.

