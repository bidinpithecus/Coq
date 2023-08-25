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

Inductive bin : Type :=
	| Z
	| B0 (n : bin)
	| B1 (n : bin)
.

Fixpoint incr (m:bin) : bin
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Fixpoint bin_to_nat (m:bin) : nat
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** In [Basics], we did some unit testing of [bin_to_nat], but we
		didn't prove its correctness. Now we'll do so. *)

(** **** Exercise: 3 stars, standard, especially useful (binary_commute)

		Prove that the following diagram commutes:

														incr
							bin ----------------------> bin
							 |                           |
		bin_to_nat |                           |  bin_to_nat
							 |                           |
							 v                           v
							nat ----------------------> nat
														 S

		That is, incrementing a binary number and then converting it to
		a (unary) natural number yields the same result as first converting
		it to a natural number and then incrementing.

		If you want to change your previous definitions of [incr] or [bin_to_nat]
		to make the property easier to prove, feel free to do so! *)

Theorem bin_to_nat_pres_incr : forall b : bin,
	bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
	(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (nat_bin_nat) *)

(** Write a function to convert natural numbers to binary numbers. *)

Fixpoint nat_to_bin (n:nat) : bin
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Prove that, if we start with any [nat], convert it to [bin], and
		convert it back, we get the same [nat] which we started with.

		Hint: This proof should go through smoothly using the previous
		exercise about [incr] as a lemma. If not, revisit your definitions
		of the functions involved and consider whether they are more
		complicated than necessary: the shape of a proof by induction will
		match the recursive structure of the program being verified, so
		make the recursions as simple as possible. *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
	(* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Bin to Nat and Back to Bin (Advanced) *)

(** The opposite direction -- starting with a [bin], converting to [nat],
		then converting back to [bin] -- turns out to be problematic. That
		is, the following theorem does not hold. *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** Let's explore why that theorem fails, and how to prove a modified
		version of it. We'll start with some lemmas that might seem
		unrelated, but will turn out to be relevant. *)

(** **** Exercise: 2 stars, advanced (double_bin) *)

(** Prove this lemma about [double], which we defined earlier in the
		chapter. *)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
	(* FILL IN HERE *) Admitted.

(** Now define a similar doubling function for [bin]. *)

Definition double_bin (b:bin) : bin
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Check that your function correctly doubles zero. *)

Example double_bin_zero : double_bin Z = Z.
(* FILL IN HERE *) Admitted.

(** Prove this lemma, which corresponds to [double_incr]. *)

Lemma double_incr_bin : forall b,
		double_bin (incr b) = incr (incr (double_bin b)).
Proof.
	(* FILL IN HERE *) Admitted.

(** [] *)

(** Let's return to our desired theorem: *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** The theorem fails because there are some [bin] such that we won't
		necessarily get back to the _original_ [bin], but instead to an
		"equivalent" [bin].  (We deliberately leave that notion undefined
		here for you to think about.)

		Explain in a comment, below, why this failure occurs. Your
		explanation will not be graded, but it's important that you get it
		clear in your mind before going on to the next part. If you're
		stuck on this, think about alternative implementations of
		[double_bin] that might have failed to satisfy [double_bin_zero]
		yet otherwise seem correct. *)

(* FILL IN HERE *)

(** To solve that problem, we can introduce a _normalization_ function
		that selects the simplest [bin] out of all the equivalent
		[bin]. Then we can prove that the conversion from [bin] to [nat] and
		back again produces that normalized, simplest [bin]. *)

(** **** Exercise: 4 stars, advanced (bin_nat_bin) *)

(** Define [normalize]. You will need to keep its definition as simple
		as possible for later proofs to go smoothly. Do not use
		[bin_to_nat] or [nat_to_bin], but do use [double_bin].

		Hint: Structure the recursion such that it _always_ reaches the
		end of the [bin] and process each bit only once. Do not try to
		"look ahead" at future bits. *)

Fixpoint normalize (b:bin) : bin
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** It would be wise to do some [Example] proofs to check that your definition of
		[normalize] works the way you intend before you proceed. They won't be graded,
		but fill them in below. *)

(* FILL IN HERE *)

(** Finally, prove the main theorem. The inductive cases could be a
		bit tricky.

		Hint: Start by trying to prove the main statement, see where you
		get stuck, and see if you can find a lemma -- perhaps requiring
		its own inductive proof -- that will allow the main proof to make
		progress. We have one lemma for the [B0] case (which also makes
		use of [double_incr_bin]) and another for the [B1] case. *)

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
	(* FILL IN HERE *) Admitted.

(** [] *)

(* 2023-03-25 11:11 *)
