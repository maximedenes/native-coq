(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Bool ZArith Nnat ZAxioms ZSig.

(** * The interface [ZSig.ZType] implies the interface [ZAxiomsSig] *)

Module ZTypeIsZAxioms (Import Z : ZType').

Hint Rewrite
 spec_0 spec_1 spec_2 spec_add spec_sub spec_pred spec_succ
 spec_mul spec_opp spec_of_Z spec_div spec_modulo spec_sqrt
 spec_compare spec_eq_bool spec_max spec_min spec_abs spec_sgn
 spec_pow spec_log2 spec_even spec_odd spec_gcd spec_quot spec_rem
 spec_testbit spec_shiftl spec_shiftr
 spec_land spec_lor spec_ldiff spec_lxor spec_div2
 : zsimpl.

Ltac zsimpl := autorewrite with zsimpl.
Ltac zcongruence := repeat red; intros; zsimpl; congruence.
Ltac zify := unfold eq, lt, le in *; zsimpl.

Instance eq_equiv : Equivalence eq.
Proof. unfold eq. firstorder. Qed.

Local Obligation Tactic := zcongruence.

Program Instance succ_wd : Proper (eq ==> eq) succ.
Program Instance pred_wd : Proper (eq ==> eq) pred.
Program Instance add_wd : Proper (eq ==> eq ==> eq) add.
Program Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
Program Instance mul_wd : Proper (eq ==> eq ==> eq) mul.

Theorem pred_succ : forall n, pred (succ n) == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem one_succ : 1 == succ 0.
Proof.
now zify.
Qed.

Theorem two_succ : 2 == succ 1.
Proof.
now zify.
Qed.

Section Induction.

Variable A : Z.t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (succ n).

Let B (z : Z) := A (of_Z z).

Lemma B0 : B 0.
Proof.
unfold B; simpl.
rewrite <- (A_wd 0); auto.
zify. auto.
Qed.

Lemma BS : forall z : Z, B z -> B (z + 1).
Proof.
intros z H.
unfold B in *. apply -> AS in H.
setoid_replace (of_Z (z + 1)) with (succ (of_Z z)); auto.
zify. auto.
Qed.

Lemma BP : forall z : Z, B z -> B (z - 1).
Proof.
intros z H.
unfold B in *. rewrite AS.
setoid_replace (succ (of_Z (z - 1))) with (of_Z z); auto.
zify. auto with zarith.
Qed.

Lemma B_holds : forall z : Z, B z.
Proof.
intros; destruct (Z_lt_le_dec 0 z).
apply natlike_ind; auto with zarith.
apply B0.
intros; apply BS; auto.
replace z with (-(-z))%Z in * by (auto with zarith).
remember (-z)%Z as z'.
pattern z'; apply natlike_ind.
apply B0.
intros; rewrite Zopp_succ; unfold Zpred; apply BP; auto.
subst z'; auto with zarith.
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (of_Z (to_Z n)).
apply B_holds.
zify. auto.
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem add_succ_l : forall n m, (succ n) + m == succ (n + m).
Proof.
intros. zify. auto with zarith.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem sub_succ_r : forall n m, n - (succ m) == pred (n - m).
Proof.
intros. zify. auto with zarith.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem mul_succ_l : forall n m, (succ n) * m == n * m + m.
Proof.
intros. zify. ring.
Qed.

(** Order *)

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
 intros. zify. destruct (Zcompare_spec [x] [y]); auto.
Qed.

Definition eqb := eq_bool.

Lemma eqb_eq : forall x y, eq_bool x y = true <-> x == y.
Proof.
 intros. zify. symmetry. apply Zeq_is_eq_bool.
Qed.

Instance compare_wd : Proper (eq ==> eq ==> Logic.eq) compare.
Proof.
intros x x' Hx y y' Hy. rewrite 2 spec_compare, Hx, Hy; intuition.
Qed.

Instance lt_wd : Proper (eq ==> eq ==> iff) lt.
Proof.
intros x x' Hx y y' Hy; unfold lt; rewrite Hx, Hy; intuition.
Qed.

Theorem lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros. zify. omega.
Qed.

Theorem lt_irrefl : forall n, ~ n < n.
Proof.
intros. zify. omega.
Qed.

Theorem lt_succ_r : forall n m, n < (succ m) <-> n <= m.
Proof.
intros. zify. omega.
Qed.

Theorem min_l : forall n m, n <= m -> min n m == n.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem min_r : forall n m, m <= n -> min n m == m.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem max_l : forall n m, m <= n -> max n m == n.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem max_r : forall n m, n <= m -> max n m == m.
Proof.
intros n m. zify. omega with *.
Qed.

(** Part specific to integers, not natural numbers *)

Theorem succ_pred : forall n, succ (pred n) == n.
Proof.
intros. zify. auto with zarith.
Qed.

(** Opp *)

Program Instance opp_wd : Proper (eq ==> eq) opp.

Theorem opp_0 : - 0 == 0.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem opp_succ : forall n, - (succ n) == pred (- n).
Proof.
intros. zify. auto with zarith.
Qed.

(** Abs / Sgn *)

Theorem abs_eq : forall n, 0 <= n -> abs n == n.
Proof.
intros n. zify. omega with *.
Qed.

Theorem abs_neq : forall n, n <= 0 -> abs n == -n.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_null : forall n, n==0 -> sgn n == 0.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_pos : forall n, 0<n -> sgn n == 1.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_neg : forall n, n<0 -> sgn n == opp 1.
Proof.
intros n. zify. omega with *.
Qed.

(** Power *)

Program Instance pow_wd : Proper (eq==>eq==>eq) pow.

Lemma pow_0_r : forall a, a^0 == 1.
Proof.
 intros. now zify.
Qed.

Lemma pow_succ_r : forall a b, 0<=b -> a^(succ b) == a * a^b.
Proof.
 intros a b. zify. intros Hb.
 rewrite Zpower_exp; auto with zarith.
 simpl. unfold Zpower_pos; simpl. ring.
Qed.

Lemma pow_neg_r : forall a b, b<0 -> a^b == 0.
Proof.
 intros a b. zify. intros Hb.
 destruct [b]; reflexivity || discriminate.
Qed.

Lemma pow_pow_N : forall a b, 0<=b -> a^b == pow_N a (Zabs_N (to_Z b)).
Proof.
 intros a b. zify. intros Hb.
 now rewrite spec_pow_N, Z_of_N_abs, Zabs_eq.
Qed.

Lemma pow_pos_N : forall a p, pow_pos a p == pow_N a (Npos p).
Proof.
 intros a b. red. now rewrite spec_pow_N, spec_pow_pos.
Qed.

(** Sqrt *)

Lemma sqrt_spec : forall n, 0<=n ->
 (sqrt n)*(sqrt n) <= n /\ n < (succ (sqrt n))*(succ (sqrt n)).
Proof.
 intros n. zify. apply Zsqrt_spec.
Qed.

Lemma sqrt_neg : forall n, n<0 -> sqrt n == 0.
Proof.
 intros n. zify. apply Zsqrt_neg.
Qed.

(** Log2 *)

Lemma log2_spec : forall n, 0<n ->
 2^(log2 n) <= n /\ n < 2^(succ (log2 n)).
Proof.
 intros n. zify. apply Zlog2_spec.
Qed.

Lemma log2_nonpos : forall n, n<=0 -> log2 n == 0.
Proof.
 intros n. zify. apply Zlog2_nonpos.
Qed.

(** Even / Odd *)

Definition Even n := exists m, n == 2*m.
Definition Odd n := exists m, n == 2*m+1.

Lemma even_spec : forall n, even n = true <-> Even n.
Proof.
 intros n. unfold Even. zify.
 rewrite Zeven_bool_iff, Zeven_ex_iff.
 split; intros (m,Hm).
 exists (of_Z m). now zify.
 exists [m]. revert Hm. now zify.
Qed.

Lemma odd_spec : forall n, odd n = true <-> Odd n.
Proof.
 intros n. unfold Odd. zify.
 rewrite Zodd_bool_iff, Zodd_ex_iff.
 split; intros (m,Hm).
 exists (of_Z m). now zify.
 exists [m]. revert Hm. now zify.
Qed.

(** Div / Mod *)

Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(div a b) + (modulo a b).
Proof.
intros a b. zify. intros. apply Z_div_mod_eq_full; auto.
Qed.

Theorem mod_pos_bound :
 forall a b, 0 < b -> 0 <= modulo a b /\ modulo a b < b.
Proof.
intros a b. zify. intros. apply Z_mod_lt; auto with zarith.
Qed.

Theorem mod_neg_bound :
 forall a b, b < 0 -> b < modulo a b /\ modulo a b <= 0.
Proof.
intros a b. zify. intros. apply Z_mod_neg; auto with zarith.
Qed.

Definition mod_bound_pos :
 forall a b, 0<=a -> 0<b -> 0 <= modulo a b /\ modulo a b < b :=
 fun a b _ H => mod_pos_bound a b H.

(** Quot / Rem *)

Program Instance quot_wd : Proper (eq==>eq==>eq) quot.
Program Instance rem_wd : Proper (eq==>eq==>eq) rem.

Theorem quot_rem : forall a b, ~b==0 -> a == b*(quot a b) + rem a b.
Proof.
intros a b _. zify. apply Z_quot_rem_eq.
Qed.

Theorem rem_bound_pos :
 forall a b, 0<=a -> 0<b -> 0 <= rem a b /\ rem a b < b.
Proof.
intros a b. zify. intros. now apply Zrem_bound.
Qed.

Theorem rem_opp_l : forall a b, ~b==0 -> rem (-a) b == -(rem a b).
Proof.
intros a b _. zify. apply Zrem_opp_l.
Qed.

Theorem rem_opp_r : forall a b, ~b==0 -> rem a (-b) == rem a b.
Proof.
intros a b _. zify. apply Zrem_opp_r.
Qed.

(** Gcd *)

Definition divide n m := exists p, n*p == m.
Local Notation "( x | y )" := (divide x y) (at level 0).

Lemma spec_divide : forall n m, (n|m) <-> Zdivide' [n] [m].
Proof.
 intros n m. split.
 intros (p,H). exists [p]. revert H; now zify.
 intros (z,H). exists (of_Z z). now zify.
Qed.

Lemma gcd_divide_l : forall n m, (gcd n m | n).
Proof.
 intros n m. apply spec_divide. zify. apply Zgcd_divide_l.
Qed.

Lemma gcd_divide_r : forall n m, (gcd n m | m).
Proof.
 intros n m. apply spec_divide. zify. apply Zgcd_divide_r.
Qed.

Lemma gcd_greatest : forall n m p, (p|n) -> (p|m) -> (p|gcd n m).
Proof.
 intros n m p. rewrite !spec_divide. zify. apply Zgcd_greatest.
Qed.

Lemma gcd_nonneg : forall n m, 0 <= gcd n m.
Proof.
 intros. zify. apply Zgcd_nonneg.
Qed.

(** Bitwise operations *)

Lemma testbit_spec : forall a n, 0<=n ->
  exists l, exists h, (0<=l /\ l<2^n) /\
    a == l + ((if testbit a n then 1 else 0) + 2*h)*2^n.
Proof.
 intros a n. zify. intros H.
 destruct (Ztestbit_spec [a] [n] H) as (l & h & Hl & EQ).
 exists (of_Z l), (of_Z h).
 destruct Ztestbit; zify; now split.
Qed.

Lemma testbit_neg_r : forall a n, n<0 -> testbit a n = false.
Proof.
 intros a n. zify. apply Ztestbit_neg_r.
Qed.

Lemma shiftr_spec : forall a n m, 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros a n m. zify. apply Zshiftr_spec.
Qed.

Lemma shiftl_spec_high : forall a n m, 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 intros a n m. zify. intros Hn H.
 now apply Zshiftl_spec_high.
Qed.

Lemma shiftl_spec_low : forall a n m, m<n ->
 testbit (shiftl a n) m = false.
Proof.
 intros a n m. zify. intros H. now apply Zshiftl_spec_low.
Qed.

Lemma land_spec : forall a b n,
 testbit (land a b) n = testbit a n && testbit b n.
Proof.
 intros a n m. zify. now apply Zand_spec.
Qed.

Lemma lor_spec : forall a b n,
 testbit (lor a b) n = testbit a n || testbit b n.
Proof.
 intros a n m. zify. now apply Zor_spec.
Qed.

Lemma ldiff_spec : forall a b n,
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof.
 intros a n m. zify. now apply Zdiff_spec.
Qed.

Lemma lxor_spec : forall a b n,
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
 intros a n m. zify. now apply Zxor_spec.
Qed.

Lemma div2_spec : forall a, div2 a == shiftr a 1.
Proof.
 intros a. zify. now apply Zdiv2_spec.
Qed.

End ZTypeIsZAxioms.

Module ZType_ZAxioms (Z : ZType)
 <: ZAxiomsSig <: HasCompare Z <: HasEqBool Z <: HasMinMax Z
 := Z <+ ZTypeIsZAxioms.
