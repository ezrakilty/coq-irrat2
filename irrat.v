(** The theorem is about reals. *)
Require Import Coq.Reals.Reals.

(** An irrational number x is one for which there do not exist
    integers a, b for which a/b = x. (IZR converts integers to reals.) *)
Definition irrat x :=
  ~exists (a:Z), exists (b:Z), (b > 0)%Z /\ (IZR a / IZR b)%R = x.

(** The heart of the proof will reason about how many "rightmost
    zeros" are in the binary representation of various numbers.
    Luckily the representation of integers (via the [positive] type)
    is already based on binary. *)
Fixpoint RightmostZeros (x:positive) : nat :=
  match x with
    | 1%positive => 0
    | (x'~0)%positive => S (RightmostZeros x')
    | (x'~1)%positive => 0
  end.

(** Doubling a [positive] number gives you one additional rightmost zero. *)
Lemma rmz_mult_2 : forall x, RightmostZeros (2*x) = S (RightmostZeros x).
 induction x; simpl; auto.
Qed.

(** [NPeano] defines the [even] function. *)
Require Coq.Numbers.Natural.Peano.NPeano.

(** A square [positive] number has an [even] number of rightmost zeros. *)
Lemma rmz_sqr : forall x, NPeano.even (RightmostZeros (x*x)) = true.
 induction x.
   simpl; auto.
  simpl.
  replace (x~0)%positive with (2*x)%positive by auto.
  replace (x * (2 * x))%positive with (2 * (x * x))%positive.
  rewrite rmz_mult_2.
  replace (RightmostZeros (x*x) + 1) with (S (RightmostZeros (x*x))) by omega.
  auto.
  rewrite Pos.mul_assoc.
  rewrite Pos.mul_comm.
  auto.
 simpl.
 auto.
Qed.

(** Now we must lift the rightmost-zero theory to integers [Z]. *)
Fixpoint RightmostZerosZ (x:Z) : nat :=
  match x with
    | Z0 => 0
    | Zpos x => RightmostZeros x
    | Zneg x => RightmostZeros x
  end.

(** Lifted rmz_mult_2. *)
Lemma rmzz_mult_2 : forall (x:Z),
  (x <> 0)%Z -> RightmostZerosZ (2*x) = S (RightmostZerosZ x).
 destruct x;  (intuition || apply rmz_mult_2).
Qed.

(** Lifted rmz_sqr. *)
Lemma rmzz_sqr : forall x, NPeano.even (RightmostZerosZ (x*x)) = true.
 destruct x; (auto || apply rmz_sqr).
Qed.

(** Incrementing a number negates its [even] status. *)
Lemma even_odd: forall x, NPeano.even x = negb (NPeano.even (S x)).
Proof.
 induction x.
  auto.
 unfold NPeano.even at 2.
 fold NPeano.even.
 rewrite IHx.
 Require Coq.Bool.Bool.
 rewrite Bool.negb_involutive.
 auto.
Qed.

(** The square root of two is irrational. *)
Theorem rad2_irrat : irrat (sqrt 2%R)%R.
Proof.
 simpl.
 unfold irrat.
 intros [a [b [H_b_gt_0 H_a_over_b_eq_rad2]]].
 assert (H_main : (a*a = 2 * b * b)%Z).
  assert (H_a_eq_rad2_mult_b : (IZR a = sqrt 2 * IZR b)%R).
   rewrite <- H_a_over_b_eq_rad2.
   replace (IZR a / IZR b)%R with (IZR a * / IZR b)%R by auto.
   rewrite Rmult_assoc.
   rewrite Rinv_l.
    auto with real.
   assert (IZR b > 0)%R.
    apply Rlt_gt.
    replace 0%R with (IZR 0) by solve [auto].
    apply IZR_lt.
    auto with zarith.
   auto with real.
  assert (H0 : (IZR a * IZR a = (sqrt 2 * IZR b) * (sqrt 2 * IZR b))%R).
   congruence.
  replace (sqrt 2 * IZR b * (sqrt 2 * IZR b))%R
     with ((sqrt 2 * sqrt 2) * IZR b * IZR b)%R in H0.
   replace (sqrt 2 * sqrt 2)%R with 2%R in H0.
    rewrite <- mult_IZR in H0.
    replace 2%R with (IZR 2) in H0 by auto.
    rewrite <- mult_IZR in H0.
    rewrite <- mult_IZR in H0.
    apply eq_IZR in H0.
    trivial.
   symmetry; apply sqrt_def.
   auto with real.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite <- Rmult_assoc.
  replace (IZR b * sqrt 2)%R with (sqrt 2 * IZR b)%R.
   auto.
  apply Rmult_comm.
 (** (Now we've reduced it to a problem in Z. And now comes the
    interesting part of the proof.) *)
 assert (H_a_rmzz_even : NPeano.even (RightmostZerosZ (a*a)) = true).
  apply rmzz_sqr.
 assert (H_b_rmzz_even : NPeano.even (RightmostZerosZ (b*b)) = true).
  apply rmzz_sqr.
 assert (H_a_rmzz_eq_S_b_rmzz : (RightmostZerosZ (a*a)) = S (RightmostZerosZ (b*b))).
  rewrite <- rmzz_mult_2.
   rewrite H_main.
   rewrite Z.mul_assoc.
   trivial.
  assert (b*b > 0)%Z.
   auto with zarith.
  auto with zarith.
 rewrite H_a_rmzz_eq_S_b_rmzz in H_a_rmzz_even.
 rewrite even_odd in H_b_rmzz_even.
 rewrite H_a_rmzz_even in H_b_rmzz_even.
 simpl in H_b_rmzz_even.
 discriminate.
Qed.

