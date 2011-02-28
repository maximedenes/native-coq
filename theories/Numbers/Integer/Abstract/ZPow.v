(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Properties of the power function *)

Require Import Bool ZAxioms ZMulOrder ZParity ZSgnAbs NZPow.

Module ZPowProp (Import Z : ZAxiomsSig')(Import ZM : ZMulOrderProp Z)
 (Import ZP : ZParityProp Z ZM)(Import ZS : ZSgnAbsProp Z ZM).
 Include NZPowProp Z ZM Z.

(** Many results are directly the same as in NZPow, hence
    the Include above. We extend nonetheless a few of them,
    and add some results concerning negative first arg.
*)

Lemma pow_mul_l' : forall a b c, (a*b)^c == a^c * b^c.
Proof.
 intros a b c. destruct (le_gt_cases 0 c). now apply pow_mul_l.
 rewrite !pow_neg by trivial. now nzsimpl.
Qed.

Lemma pow_nonneg : forall a b, 0<=a -> 0<=a^b.
Proof.
 intros a b Ha. destruct (le_gt_cases 0 b).
 now apply pow_nonneg_nonneg.
 rewrite !pow_neg by trivial. order.
Qed.

Lemma pow_le_mono_l' : forall a b c, 0<=a<=b -> a^c <= b^c.
Proof.
 intros a b c. destruct (le_gt_cases 0 c). now apply pow_le_mono_l.
 rewrite !pow_neg by trivial. order.
Qed.

(** NB: since 0^0 > 0^1, the following result isn't valid with a=0 *)

Lemma pow_le_mono_r' : forall a b c, 0<a -> b<=c -> a^b <= a^c.
Proof.
 intros a b c. destruct (le_gt_cases 0 b).
 intros. apply pow_le_mono_r; try split; trivial.
 rewrite !pow_neg by trivial.
 intros. apply pow_nonneg. order.
Qed.

Lemma pow_le_mono' : forall a b c d, 0<a<=c -> b<=d ->
 a^b <= c^d.
Proof.
 intros a b c d. destruct (le_gt_cases 0 b).
 intros. apply pow_le_mono. trivial. split; trivial.
 rewrite !pow_neg by trivial.
 intros. apply pow_nonneg. intuition order.
Qed.

(** Parity of power *)

Lemma even_pow : forall a b, 0<b -> even (a^b) = even a.
Proof.
 intros a b Hb. apply lt_ind with (4:=Hb). solve_predicate_wd.
 now nzsimpl.
 clear b Hb. intros b Hb IH. nzsimpl; [|order].
 rewrite even_mul, IH. now destruct (even a).
Qed.

Lemma odd_pow : forall a b, 0<b -> odd (a^b) = odd a.
Proof.
 intros. now rewrite <- !negb_even_odd, even_pow.
Qed.

(** Properties of power of negative numbers *)

Lemma pow_opp_even : forall a b, Even b -> (-a)^b == a^b.
Proof.
 intros a b (c,H). rewrite H.
 destruct (le_gt_cases 0 c).
 assert (0 <= 2) by (apply le_le_succ_r, le_0_1).
 rewrite 2 pow_mul_r; trivial.
 rewrite 2 pow_2_r.
 now rewrite mul_opp_opp.
 assert (2*c < 0).
  apply mul_pos_neg; trivial. rewrite lt_succ_r. apply le_0_1.
 now rewrite !pow_neg.
Qed.

Lemma pow_opp_odd : forall a b, Odd b -> (-a)^b == -(a^b).
Proof.
 intros a b (c,H). rewrite H.
 destruct (le_gt_cases 0 c) as [LE|GT].
 assert (0 <= 2*c).
  apply mul_nonneg_nonneg; trivial.
  apply le_le_succ_r, le_0_1.
 rewrite add_succ_r, add_0_r, !pow_succ_r; trivial.
 rewrite pow_opp_even by (now exists c).
 apply mul_opp_l.
 apply double_above in GT. rewrite mul_0_r in GT.
 rewrite !pow_neg by trivial. now rewrite opp_0.
Qed.

Lemma pow_even_abs : forall a b, Even b -> a^b == (abs a)^b.
Proof.
 intros. destruct (abs_eq_or_opp a) as [EQ|EQ]; rewrite EQ.
 reflexivity.
 symmetry. now apply pow_opp_even.
Qed.

Lemma pow_even_nonneg : forall a b, Even b -> 0 <= a^b.
Proof.
 intros. rewrite pow_even_abs by trivial.
 apply pow_nonneg, abs_nonneg.
Qed.

Lemma pow_odd_abs_sgn : forall a b, Odd b -> a^b == sgn a * (abs a)^b.
Proof.
 intros a b H.
 destruct (sgn_spec a) as [(LT,EQ)|[(EQ',EQ)|(LT,EQ)]]; rewrite EQ.
 nzsimpl.
 rewrite abs_eq; order.
 rewrite <- EQ'. nzsimpl.
 destruct (le_gt_cases 0 b).
 apply pow_0_l.
 assert (b~=0) by
  (contradict H; now rewrite H, <-odd_spec, <-negb_even_odd, even_0).
 order.
 now rewrite pow_neg.
 rewrite abs_neq by order.
 rewrite pow_opp_odd; trivial.
 now rewrite mul_opp_opp, mul_1_l.
Qed.

Lemma pow_odd_sgn : forall a b, 0<=b -> Odd b -> sgn (a^b) == sgn a.
Proof.
 intros a b Hb H.
 destruct (sgn_spec a) as [(LT,EQ)|[(EQ',EQ)|(LT,EQ)]]; rewrite EQ.
 apply sgn_pos. apply pow_pos_nonneg; trivial.
 rewrite <- EQ'. rewrite pow_0_l. apply sgn_0.
 assert (b~=0) by
  (contradict H; now rewrite H, <-odd_spec, <-negb_even_odd, even_0).
 order.
 apply sgn_neg.
 rewrite <- (opp_involutive a). rewrite pow_opp_odd by trivial.
 apply opp_neg_pos.
 apply pow_pos_nonneg; trivial.
 now apply opp_pos_neg.
Qed.

End ZPowProp.
