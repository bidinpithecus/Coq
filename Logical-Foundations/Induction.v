(** * Induction: Proof by Induction *)

From MYCOQ Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
n + 0 = n.
Proof.
	intros n.
	simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry : forall n:nat,
	n + 0 = n.
Proof.
	intros n. destruct n as [| n'] eqn:E.
	- (* n = 0 *)
		reflexivity. (* so far so good... *)
	- (* n = S n' *)
		simpl.       (* ...but here we are stuck again *)
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
intros n. induction n.
	- (* n = 0 *)    reflexivity.
	- (* n = S n' *) simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem minus_n_n : forall n,
	minus n n = 0.
Proof.
	induction n as [| n' IHn'].
	- (* n = 0 *)
		simpl. reflexivity.
	- (* n = S n' *)
		simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
	n * 0 = 0.
Proof.
	induction n.
	- simpl. reflexivity.
	- simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
	S (n + m) = n + (S m).
Proof.
	induction n.
	- simpl. reflexivity.
	- intros m. simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
	n + m = m + n.
Proof.
	induction n.
	- intros m. simpl. rewrite add_0_r. reflexivity.
	- intros m. simpl. rewrite <- plus_n_Sm. rewrite IHn. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
	n + (m + p) = (n + m) + p.
Proof.
	induction n.
	- intros m p. simpl. reflexivity.
	- intros m p. simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
	match n with
	| O => O
	| S n' => S (S (double n'))
	end.

Lemma double_plus : forall n, double n = n + n .
Proof.
	induction n.
	- simpl. reflexivity.
	- simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
	(n =? n) = true.
Proof.
	induction n.
	- simpl. reflexivity.
	- simpl. rewrite IHn. reflexivity.
Qed.

Theorem even_S : forall n : nat,
	even (S n) = negb (even n).
Proof.
	induction n.
	- simpl. reflexivity.
	- rewrite IHn. simpl. rewrite negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
	(n + 0 + 0) * m = n * m.
Proof.
	intros n m.
	assert (H: n + 0 + 0 = n).
		{ rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
	rewrite -> H.
	reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
	(n + m) + (p + q) = (m + n) + (p + q).
Proof.
	intros n m p q.
	(* We just need to swap (n + m) for (m + n)... seems
		 like add_comm should do the trick! *)
	rewrite add_comm.
	(* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
	(n + m) + (p + q) = (m + n) + (p + q).
Proof.
	intros n m p q.
	assert (H: n + m = m + n).
	{ rewrite add_comm. reflexivity. }
	rewrite H. reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
	n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
	simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_assoc'' : forall n m p : nat,
	n + (m + p) = (n + m) + p.
Proof.
	intros n m p. induction n as [| n' IHn'].
	- (* n = 0 *)
		reflexivity.
	- (* n = S n' *)
		simpl. rewrite IHn'. reflexivity.
Qed.

Definition manual_grade_for_add_comm_informal : option (nat*string) := None.

Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.

Theorem add_shuffle3 : forall n m p : nat,
	n + (m + p) = m + (n + p).
Proof.
	intros.
	rewrite add_assoc.
	rewrite add_assoc.
	assert (n + m = m + n). {
		rewrite add_comm. reflexivity.
	}
	rewrite H.
	reflexivity.
Qed.

Theorem mul_n_sm : forall n m : nat,
	n + n * m = n * S m.
Proof.
	intros. induction n.
	- reflexivity.
	- simpl. rewrite <- IHn. rewrite add_shuffle3. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
	m * n = n * m.
Proof.
	intros n m.
	induction n.
	- rewrite mul_0_r. reflexivity.
	- simpl. rewrite <- mul_n_sm. rewrite IHn. reflexivity.
Qed.

Check leb.

Theorem n_plus_m_gt_n: forall n m: nat,
	n <=? n + m = true.
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
	n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
	intros. induction p.
	- simpl. rewrite H. reflexivity.
	- simpl. rewrite IHp. reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
	(n <=? n) = true.
Proof.
	intros. induction n.
	- reflexivity.
	- simpl. rewrite IHn. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
	0 =? (S n) = false.
Proof.
	intros. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
	andb b false = false.
Proof.
	intros. destruct b.
	- reflexivity.
	- reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
	(S n) =? 0 = false.
Proof.
	intros. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
	intros. simpl. rewrite add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
	orb
		(andb b c)
		(orb (negb b)
				 (negb c))
	= true.
Proof.
	intros. destruct b.
	- destruct c.
		+ simpl. reflexivity.
		+ simpl. reflexivity.
	- destruct c.
	+ simpl. reflexivity.
	+ simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
	(n + m) * p = (n * p) + (m * p).
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- simpl. rewrite <- add_assoc. rewrite IHn. simpl. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
	n * (m * p) = (n * m) * p.
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- simpl. rewrite IHn. rewrite mult_plus_distr_r. simpl. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
	n + (m + p) = m + (n + p).
Proof.
	intros. rewrite add_assoc. rewrite add_assoc. replace (n + m) with (m + n).
	- reflexivity.
	- rewrite add_comm. reflexivity.
Qed.

(* Binary Section *)

Inductive bin: Type :=
	| Z
	| B0 (n : bin)
	| B1 (n : bin)
.

Fixpoint incr (m: bin): bin :=
	match m with
	| Z => B1 Z
	| B0 b => B1 b
	| B1 b => B0 (incr b)
	end
.

Fixpoint bin_to_nat (m: bin): nat :=
	match m with
	| Z => O
	| B0 b => 2 * (bin_to_nat b)
	| B1 b => S (2 * (bin_to_nat b))
	end
.

Theorem bin_to_nat_pres_incr: forall b: bin,
	bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
	intros. induction b.
	- simpl. reflexivity.
	- simpl. reflexivity.
	- simpl. rewrite add_0_r.
		rewrite add_0_r. rewrite IHb.
		simpl. rewrite add_comm.
		assert (S (bin_to_nat b) + bin_to_nat b = S (bin_to_nat b + bin_to_nat b)).
			{
				simpl. reflexivity.
			}
		rewrite H. reflexivity.
Qed.

Fixpoint nat_to_bin (n: nat): bin :=
	match n with
	| O => Z
	| S n' => incr (nat_to_bin n')
	end
.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- simpl. rewrite bin_to_nat_pres_incr. simpl. rewrite IHn. reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- rewrite IHn. simpl. reflexivity.
Qed.

Definition double_bin (b: bin): bin :=
	match b with
	| Z => Z
	| b' => B0 b'
	end
.

Example double_bin_zero : double_bin Z = Z.
Proof.
	intros. simpl. reflexivity.
Qed.

Lemma double_incr_bin : forall b,
		double_bin (incr b) = incr (incr (double_bin b)).
Proof.
	intros. destruct b.
	- simpl. reflexivity.
	- simpl. reflexivity.
	- simpl. reflexivity.
Qed.

Fixpoint normalize (b: bin) : bin :=
	match b with
	| Z => Z
	| B0 b' => double_bin (normalize (b'))
	| B1 b' => B1 (normalize (b'))
	end
.

Lemma equivalent_doubles: forall n,
	nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
	intros. induction n.
	- simpl. reflexivity.
	- simpl. rewrite IHn.
		rewrite double_incr_bin.
		reflexivity.
Qed.

Lemma incr_of_double_bin: forall b,
	incr (double_bin b) = B1 b.
Proof.
	destruct b.
	- simpl. reflexivity.
	- simpl. reflexivity.
	- simpl. reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
	intros. induction b.
	- simpl. reflexivity.
	- simpl. rewrite add_0_r.
		rewrite <- double_plus. rewrite equivalent_doubles.
		rewrite IHb. reflexivity.
	- simpl. rewrite add_0_r.
		rewrite <- double_plus. rewrite equivalent_doubles.
		rewrite incr_of_double_bin. rewrite IHb.
		reflexivity.
Qed.
