(** The theorem is about reals. *)
Require Import Coq.Reals.Reals.

(** An irrational number x is one for which there do not exist
    integers a, b for which a/b = x. (IZR converts integers to reals.) *)
Definition irrat x :=
  ~exists (a:Z), exists (b:Z), (b > 0)%Z /\ (IZR a / IZR b)%R = x.

(** The heart of the proof will reason about how many "rightmost
    zeros" are in the binary representation of various numbers.
    Luckily the representation of [positive] integers is already
    based on binary. *)
Fixpoint RightmostZeros (x:positive) : nat :=
  match x with
    | 1%positive => 0   (** The number 1 has zero rightmost zeros. *)
    (** Bits ending in 0 (an even number) have one more than the butlast bits. *)
    | (bits~0)%positive => S (RightmostZeros bits)
    | (x'~1)%positive => 0  (** Bits ending in 1 have no rightmost zeros. *)
  end.

(** Doubling a [positive] number gives you one additional rightmost zero. *)
Lemma rmz_mult_2 : forall x, RightmostZeros (2*x) = S (RightmostZeros x).
 auto.
Qed.

(** [NPeano] defines the [even] function. *)
Require Coq.Numbers.Natural.Peano.NPeano.

(** A square [positive] number has an [even] number of rightmost zeros. *)
Lemma rmz_sqr : forall x, NPeano.even (RightmostZeros (x*x)) = true.
 induction x.
 (* x~1 * x~1 *)
   auto.
 (* x~0 * x~0 *)
  simpl.
  rewrite Pos.mul_comm.
  auto.
 (* 1 * 1 *)
 auto.
Qed.

(** Now we must lift the rightmost-zero theory to integers [Z]. *)
Fixpoint RightmostZerosZ (x:Z) : nat :=
  match x with
    | Z0 => 0
    | Zpos x => RightmostZeros x
    | Zneg x => RightmostZeros x
  end.

(** Lifted rmz_mult_2 (for nonzero integers). *)
Lemma rmzZ_mult_2 : forall (x:Z),
  (x <> 0)%Z -> RightmostZerosZ (2*x) = S (RightmostZerosZ x).
 destruct x;  (intuition || apply rmz_mult_2).
Qed.

(** Lifted rmz_sqr. *)
Lemma rmzZ_sqr : forall x, NPeano.even (RightmostZerosZ (x*x)) = true.
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

Lemma sqrt_mul_sqrt_eq_n :
  forall x, (0 <= x)%R -> (sqrt x * sqrt x)%R = x%R.
Proof.
 intros.
 apply sqrt_def; auto.
Qed.

(** The square root of two is irrational. *)
Theorem rad2_irrat : irrat (sqrt 2%R)%R.
Proof.
 simpl.
 unfold irrat.
 (* The goal is now:
    ~exists a b : X, b > 0 /\ IZR a / IZR b = sqrt 2) *)

 (* Prove the negation by contraction; call that contrary hypothesis H *)
 intro H.

 (* H asserts the existence of numbers a and b governed by some assertions;
    name the numbers and assertions. *)
 destruct H as [a [b [H_b_gt_0 H_a_over_b_eq_rad2]]].

 assert (H_main : (a*a = 2 * b * b)%Z).
  (* Proof of H_main. *)

  (* In H_a_over_b_eq_rad2, we'd like to move the IZR b to the rhs. *)
  assert (H_a_eq_rad2_mult_b : (IZR a = sqrt 2 * IZR b)%R).
   (* Proof of H_a_eq_rad2_mult_b. *)

   (* Lift our fact that b > 0 to reals *)
   assert (IZR b > 0)%R.
    replace 0%R with (IZR 0) by solve [auto].
    Hint Resolve Rlt_gt : real.
    Hint Resolve IZR_lt : zarith.
    auto with real zarith.

   (* Now we do some equational substitutions. *)
   rewrite <- H_a_over_b_eq_rad2.
   field.
   Hint Resolve Rgt_not_eq : real.
   auto with real.

  (* Back to proving H_main: a * a = 2 * b * b. *)
  assert (H0 : (IZR a * IZR a = (sqrt 2 * IZR b) * (sqrt 2 * IZR b))%R).
   congruence.

  replace (sqrt 2 * IZR b * (sqrt 2 * IZR b))%R
     with ((sqrt 2 * sqrt 2) * IZR b * IZR b)%R in H0
     (* This substitution is shown by assoc/comm normalizing, tactic "ring" *)
     by ring.
  rewrite sqrt_mul_sqrt_eq_n in H0 by (auto with real).
  replace 2%R with (IZR 2) in H0 by auto.
  repeat (rewrite <- mult_IZR in H0).
  apply eq_IZR; trivial.

 clear H_a_over_b_eq_rad2.

 (** (Now we've reduced it to a problem in Z. And now comes the
     interesting part of the proof.) The next three assertions will
     given us some equations on the number of zeros in a*a and b*b
     that can't all be satisfied. *)
 assert (H_a_rmzZ_even : NPeano.even (RightmostZerosZ (a*a)) = true).
  apply rmzZ_sqr.
 assert (H_b_rmzZ_even : NPeano.even (RightmostZerosZ (b*b)) = true).
  apply rmzZ_sqr.
 assert (H_a_rmzZ_eq_S_b_rmzZ : (RightmostZerosZ (a*a)) = S (RightmostZerosZ (b*b))).
  rewrite <- rmzZ_mult_2.
   rewrite H_main.
   rewrite Z.mul_assoc.
   trivial.
  (* Using rmzZ_mult_2 gave us an obligation that b*b <> 0 *)
  assert (b*b > 0)%Z by (auto with zarith).
  auto with zarith.

 (* Now we have those three equations and we can derive a contradiction. *)
 rewrite H_a_rmzZ_eq_S_b_rmzZ in H_a_rmzZ_even.
 rewrite even_odd in H_b_rmzZ_even.
 rewrite H_a_rmzZ_even in H_b_rmzZ_even.
 simpl in H_b_rmzZ_even.
 (* We have derived a bogus equation, false = true. Coq knows what to do from
    here. *)
 discriminate.
Qed.
