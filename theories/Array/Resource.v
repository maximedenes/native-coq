Require Import Int31Native.
Require Import PArray.

Register resource : Set as resource_type.
Register make : array int -> resource as resource_make.
Register getc : resource -> int -> int as resource_getc.
Register geti : resource -> int -> int as resource_geti32.



