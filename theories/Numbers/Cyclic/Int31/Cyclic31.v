(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Int31 numbers defines indeed a cyclic structure : Z/(2^31)Z *)

(**
Author: Arnaud Spiwack (+ Pierre Letouzey)
*)
Require Import CyclicAxioms.
Require Export ZArith.
Require Export Int31Properties.

Local Open Scope int31_scope.
(** {2 Operators } **)

Definition Pdigits := Eval compute in P_of_succ_nat (size - 1).

Fixpoint positive_to_int_rec (n:nat) (p:positive) :=
  match n, p with 
  | O, _ => (Npos p, 0)
  | S n, xH => (0%N, 1)
  | S n, xO p => 
    let (N,i) := positive_to_int_rec n p in
    (N, i << 1)
  | S n, xI p =>
    let (N,i) := positive_to_int_rec n p in
    (N, (i << 1) + 1) 
  end.

Definition positive_to_int := positive_to_int_rec size.

Definition mulc_WW x y :=
  let (h, l) := mulc x y in
  if is_zero h then 
    if is_zero l then W0
    else WW h l
  else WW h l.
Notation "n '*c' m" := (mulc_WW n m) (at level 40, no associativity) : int31_scope.

Definition pos_mod p x := 
  if p <= digits then
    let p := digits - p in
    (x << p) >> p
  else x.

Instance int_ops : ZnZ.Ops int :=
{
 digits      := Pdigits; (* number of digits *)
 zdigits     := digits; (* number of digits *)
 to_Z        := to_Z; (* conversion to Z *)
 of_pos      := positive_to_int; (* positive -> N*int31 :  p => N,i
                                      where p = N*2^31+phi i *)
 head0       := head0;  (* number of head 0 *)
 tail0       := tail0;  (* number of tail 0 *)
 zero        := 0;
 one         := 1;
 minus_one   := max_int;
 compare     := compare;
 eq0         := is_zero;
 opp_c       := oppc;
 opp         := opp;
 opp_carry   := oppcarry;
 succ_c      := succc;
 add_c       := addc;
 add_carry_c := addcarryc;
 succ        := succ;
 add         := add;
 add_carry   := addcarry;
 pred_c      := predc;
 sub_c       := subc;
 sub_carry_c := subcarryc;
 pred        := pred;
 sub         := sub;
 sub_carry   := subcarry;
 mul_c       := mulc_WW;
 mul         := mul;
 square_c    := fun x => mulc_WW x x;
 div21       := diveucl_21;
 div_gt      := diveucl; (* this is supposed to be the special case of
                         division a/b where a > b *)
 div         := diveucl;
 modulo_gt   := Int31Native.mod;
 modulo      := Int31Native.mod;
 gcd_gt      := gcd;
 gcd         := gcd;
 add_mul_div := addmuldiv;
 pos_mod     := pos_mod;
 is_even     := is_even;
 sqrt2       := sqrt2;
 sqrt        := sqrt
}.

Local Open Scope Z_scope.

Lemma is_zero_spec_aux : forall x : int, is_zero x = true -> [|x|] = 0%Z.
Proof.
 intros x;rewrite is_zero_spec;intros H;rewrite H;trivial.
Qed.

Lemma positive_to_int_spec :
  forall p : positive,
    Zpos p =
      Z_of_N (fst (positive_to_int p)) * wB + to_Z (snd (positive_to_int p)).
Proof.
 assert (H: (wB <= wB) -> forall p : positive,
  Zpos p = Z_of_N (fst (positive_to_int p)) * wB + [|snd (positive_to_int p)|] /\
  [|snd (positive_to_int p)|] < wB).
  2: intros p; case (H (Zle_refl wB) p); auto.
 unfold positive_to_int, wB at 1 3 4.
 elim size.
 intros _ p; simpl;
   rewrite to_Z_0, Pmult_1_r; split; auto with zarith; apply refl_equal.
 intros n; rewrite inj_S; unfold Zsucc; rewrite Zpower_exp, Zpower_1_r; auto with zarith.
 intros IH Hle p.
 assert (F1: 2 ^ Z_of_nat n <= wB); auto with zarith.
  assert (0 <= 2 ^ Z_of_nat n); auto with zarith.
 case p; simpl.
 intros p1.
 generalize (IH F1 p1); case positive_to_int_rec; simpl.
 intros n1 i (H1,H2).
 rewrite Zpos_xI, H1.
 replace [|i << 1  + 1|] with ([|i|] * 2 + 1).
 split; auto with zarith; ring.
 rewrite add_spec, lsl_spec, Zplus_mod_idemp_l, to_Z_1, Zpower_1_r, Zmod_small; auto.
 case (to_Z_bounded i); split; auto with zarith.
 intros p1.
 generalize (IH F1 p1); case positive_to_int_rec; simpl.
 intros n1 i (H1,H2).
 rewrite Zpos_xO, H1.
 replace [|i << 1|] with ([|i|] * 2).
 split; auto with zarith; ring.
 rewrite lsl_spec, to_Z_1, Zpower_1_r, Zmod_small; auto.
 case (to_Z_bounded i); split; auto with zarith.
 rewrite to_Z_1; assert (0 < 2^ Z_of_nat n); auto with zarith.
Qed.

Lemma mulc_WW_spec :
   forall x y,[|| x *c y ||] = [|x|] * [|y|].
Proof.
 intros x y;unfold mulc_WW.
 generalize (mulc_spec x y);destruct (mulc x y);simpl;intros Heq;rewrite Heq.
 case_eq (is_zero i);intros;trivial.
 apply is_zero_spec in H;rewrite H, to_Z_0.
 case_eq (is_zero i0);intros;trivial.
 apply is_zero_spec in H0;rewrite H0, to_Z_0, Zmult_comm;trivial.
Qed.

Lemma squarec_spec : 
  forall x,
    [||x *c x||] = [|x|] * [|x|].
Proof (fun x => mulc_WW_spec x x).

Lemma diveucl_spec_aux : forall a b, 0 < [|b|] ->
  let (q,r) := diveucl a b in
  [|a|] = [|q|] * [|b|] + [|r|] /\
  0 <= [|r|] < [|b|].
Proof.
 intros a b H;assert (W:= diveucl_spec a b).
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod [|a|] [|b|] H0).
 destruct (diveucl a b);destruct (Zdiv_eucl [|a|] [|b|]).
 inversion W;rewrite Zmult_comm;trivial.
Qed.

Lemma diveucl_21_spec_aux : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := diveucl_21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b H1 H2;assert (W:= diveucl_21_spec a1 a2 b).
 assert (W1:= to_Z_bounded a1).
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod ([|a1|]*wB+[|a2|]) [|b|] H).
 destruct (diveucl_21 a1 a2 b);destruct (Zdiv_eucl ([|a1|]*wB+[|a2|]) [|b|]).
 inversion W;rewrite (Zmult_comm [|b|]);trivial.
Qed.

Lemma shift_unshift_mod_3:
  forall n p a : Z,
  0 <= p <= n ->
  (a * 2 ^ (n - p)) mod 2 ^ n / 2 ^ (n - p) = a mod 2 ^ p.
Proof.
 intros;rewrite <- (shift_unshift_mod_2 n p a);[ | auto with zarith].
 symmetry;apply Zmod_small.
 generalize (a * 2 ^ (n - p));intros w.
 assert (2 ^ n > 0) by (auto with zarith).
 assert (H1 := Z_mod_lt w _ H0).
 split;[apply div_le_0| apply div_lt];auto with zarith.
Qed.

Lemma pos_mod_spec : forall w p,
       [|pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
Proof.
 unfold pos_mod;intros.
 assert (W:=to_Z_bounded p);assert (W':=to_Z_bounded digits);assert (W'' := to_Z_bounded w).
 case_eq (p <= digits)%int31;intros Heq.
 rewrite leb_spec in Heq.
 rewrite lsr_spec, lsl_spec.
 assert (0 <= [|p|] <= [|digits|]) by (auto with zarith).
 rewrite <- (shift_unshift_mod_3 [|digits|] [|p|] [|w|] H).
 replace ([|digits|] - [|p|]) with [|digits - p|];trivial.
 rewrite sub_spec, Zmod_small;auto with zarith.
 symmetry;apply Zmod_small.
 rewrite <- Bool.not_true_iff_false, leb_spec in Heq.
 assert (2 ^ [|digits|] < 2 ^ [|p|]);[ apply Zpower_lt_monotone | ];auto with zarith.
 change wB with (2 ^ [|digits|]) in *;auto with zarith.
Qed.

Axiom sqrt2_spec : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].

(** {2 Specification and proof} **)
Global Instance int_specs : ZnZ.Specs int_ops := {
    spec_to_Z   := to_Z_bounded;
    spec_of_pos := positive_to_int_spec;
    spec_zdigits := refl_equal _;
    spec_more_than_1_digit:= refl_equal _;
    spec_0 := to_Z_0;
    spec_1 := to_Z_1;
    spec_m1 := refl_equal _;
    spec_compare := compare_spec;
    spec_eq0 := is_zero_spec_aux;
    spec_opp_c := oppc_spec;
    spec_opp := opp_spec;
    spec_opp_carry := oppcarry_spec;
    spec_succ_c := succc_spec;
    spec_add_c := addc_spec;
    spec_add_carry_c := addcarryc_spec;
    spec_succ := succ_spec;
    spec_add := add_spec;
    spec_add_carry := addcarry_spec;
    spec_pred_c := predc_spec;
    spec_sub_c := subc_spec;
    spec_sub_carry_c := subcarryc_spec;
    spec_pred := pred_spec;
    spec_sub := sub_spec;
    spec_sub_carry := subcarry_spec;
    spec_mul_c := mulc_WW_spec;
    spec_mul := mul_spec;
    spec_square_c := squarec_spec;
    spec_div21 := diveucl_21_spec_aux;
    spec_div_gt := fun a b _ => diveucl_spec_aux a b;
    spec_div := diveucl_spec_aux;
    spec_modulo_gt := fun a b _ _ => mod_spec a b;
    spec_modulo := fun a b _ => mod_spec a b;
    spec_gcd_gt := fun a b _ => gcd_spec a b;
    spec_gcd := gcd_spec;
    spec_head00 := head00_spec;
    spec_head0 := head0_spec;
    spec_tail00 := tail00_spec;
    spec_tail0 := tail0_spec;
    spec_add_mul_div := addmuldiv_spec;
    spec_pos_mod := pos_mod_spec;
    spec_is_even := is_even_spec;
    spec_sqrt2 := sqrt2_spec;
    spec_sqrt := sqrt_spec }.



Module Int31Cyclic <: CyclicType.
  Definition t := int.
  Definition ops := int_ops.
  Definition specs := int_specs.
End Int31Cyclic.

