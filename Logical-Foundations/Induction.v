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

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
		broken into a sequence of theorems, with later proofs referring to
		earlier theorems.  But sometimes a proof will involve some
		miscellaneous fact that is too trivial and of too little general
		interest to bother giving it its own top-level name.  In such
		cases, it is convenient to be able to simply state and prove the
		needed "sub-theorem" right at the point where it is used.  The
		[assert] tactic allows us to do this. *)

Theorem mult_0_plus' : forall n m : nat,
	(n + 0 + 0) * m = n * m.
Proof.
	intros n m.
	assert (H: n + 0 + 0 = n).
		{ rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
	rewrite -> H.
	reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
		the assertion itself; by prefixing it with [H:] we name the
		assertion [H].  (We can also name the assertion with [as] just as
		we did above with [destruct] and [induction], i.e., [assert (n + 0
		+ 0 = n) as H].)  Note that we surround the proof of this
		assertion with curly braces [{ ... }], both for readability and so
		that, when using Coq interactively, we can see more easily when we
		have finished this sub-proof.  The second goal is the same as the
		one at the point where we invoke [assert] except that, in the
		context, we now have the assumption [H] that [n + 0 + 0 = n].
		That is, [assert] generates one subgoal where we must prove the
		asserted fact and a second subgoal where we can use the asserted
		fact to make progress on whatever we were trying to prove in the
		first place. *)

(** As another example, suppose we want to prove that [(n + m)
		+ (p + q) = (m + n) + (p + q)]. The only difference between the
		two sides of the [=] is that the arguments [m] and [n] to the
		first inner [+] are swapped, so it seems we should be able to use
		the commutativity of addition ([add_comm]) to rewrite one into the
		other.  However, the [rewrite] tactic is not very smart about
		_where_ it applies the rewrite.  There are three uses of [+] here,
		and it turns out that doing [rewrite -> add_comm] will affect only
		the _outer_ one... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
	(n + m) + (p + q) = (m + n) + (p + q).
Proof.
	intros n m p q.
	(* We just need to swap (n + m) for (m + n)... seems
		 like add_comm should do the trick! *)
	rewrite add_comm.
	(* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

(** To use [add_comm] at the point where we need it, we can introduce
		a local lemma stating that [n + m = m + n] (for the _particular_ [m]
		and [n] that we are talking about here), prove this lemma using
		[add_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
	(n + m) + (p + q) = (m + n) + (p + q).
Proof.
	intros n m p q.
	assert (H: n + m = m + n).
	{ rewrite add_comm. reflexivity. }
	rewrite H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "_Informal proofs are algorithms; formal proofs are code_." *)

(** What constitutes a successful proof of a mathematical claim?
		The question has challenged philosophers for millennia, but a
		rough and ready definition could be this: A proof of a
		mathematical proposition [P] is a written (or spoken) text that
		instills in the reader or hearer the certainty that [P] is true --
		an unassailable argument for the truth of [P].  That is, a proof
		is an act of communication.

		Acts of communication may involve different sorts of readers.  On
		one hand, the "reader" can be a program like Coq, in which case
		the "belief" that is instilled is that [P] can be mechanically
		derived from a certain set of formal logical rules, and the proof
		is a recipe that guides the program in checking this fact.  Such
		recipes are _formal_ proofs.

		Alternatively, the reader can be a human being, in which case the
		proof will be written in English or some other natural language,
		and will thus necessarily be _informal_.  Here, the criteria for
		success are less clearly specified.  A "valid" proof is one that
		makes the reader believe [P].  But the same proof may be read by
		many different readers, some of whom may be convinced by a
		particular way of phrasing the argument, while others may not be.
		Some readers may be particularly pedantic, inexperienced, or just
		plain thick-headed; the only way to convince them will be to make
		the argument in painstaking detail.  But other readers, more
		familiar in the area, may find all this detail so overwhelming
		that they lose the overall thread; all they want is to be told the
		main ideas, since it is easier for them to fill in the details for
		themselves than to wade through a written presentation of them.
		Ultimately, there is no universal standard, because there is no
		single way of writing an informal proof that is guaranteed to
		convince every conceivable reader.

		In practice, however, mathematicians have developed a rich set of
		conventions and idioms for writing about complex mathematical
		objects that -- at least within a certain community -- make
		communication fairly reliable.  The conventions of this stylized
		form of communication give a fairly clear standard for judging
		proofs good or bad.

		Because we are using Coq in this course, we will be working
		heavily with formal proofs.  But this doesn't mean we can
		completely forget about informal ones!  Formal proofs are useful
		in many ways, but they are _not_ very efficient ways of
		communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem add_assoc' : forall n m p : nat,
	n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
	simpl. rewrite IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this.  For a human, however, it
		is difficult to make much sense of it.  We can use comments and
		bullets to show the structure a little more clearly... *)

Theorem add_assoc'' : forall n m p : nat,
	n + (m + p) = (n + m) + p.
Proof.
	intros n m p. induction n as [| n' IHn'].
	- (* n = 0 *)
		reflexivity.
	- (* n = S n' *)
		simpl. rewrite IHn'. reflexivity.   Qed.

(** ... and if you're used to Coq you might be able to step
		through the tactics one after the other in your mind and imagine
		the state of the context and goal stack at each point, but if the
		proof were even a little bit more complicated this would be next
		to impossible.

		A (pedantic) mathematician might write the proof something like
		this: *)

(** - _Theorem_: For any [n], [m] and [p],

			n + (m + p) = (n + m) + p.

		_Proof_: By induction on [n].

		- First, suppose [n = 0].  We must show that

				0 + (m + p) = (0 + m) + p.

			This follows directly from the definition of [+].

		- Next, suppose [n = S n'], where

				n' + (m + p) = (n' + m) + p.

			We must now show that

				(S n') + (m + p) = ((S n') + m) + p.

			By the definition of [+], this follows from

				S (n' + (m + p)) = S ((n' + m) + p),

			which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar, and of
		course this is no accident: Coq has been designed so that its
		[induction] tactic generates the same sub-goals, in the same
		order, as the bullet points that a mathematician would write.  But
		there are significant differences of detail: the formal proof is
		much more explicit in some ways (e.g., the use of [reflexivity])
		but much less explicit in others (in particular, the "proof state"
		at any given point in the Coq proof is completely implicit,
		whereas the informal proof reminds the reader several times where
		things stand). *)

(** **** Exercise: 2 stars, advanced, especially useful (add_comm_informal)

		Translate your solution for [add_comm] into an informal proof:

		Theorem: Addition is commutative.

		Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl_informal)

		Write an informal proof of the following theorem, using the
		informal proof of [add_assoc] as a model.  Don't just
		paraphrase the Coq tactics into English!

		Theorem: [(n =? n) = true] for any [n].

		Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (mul_comm)

		Use [assert] to help prove [add_shuffle3].  You don't need to
		use induction yet. *)

Theorem add_shuffle3 : forall n m p : nat,
	n + (m + p) = m + (n + p).
Proof.
	(* FILL IN HERE *) Admitted.

(** Now prove commutativity of multiplication.  You will probably want
		to look for (or define and prove) a "helper" theorem to be used in
		the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
	m * n = n * m.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (plus_leb_compat_l)

		If a hypothesis has the form [H: P -> a = b], then [rewrite H] will
		rewrite [a] to [b] in the goal, and add [P] as a new subgoal. Use
		that in the inductive step of this exercise. *)

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
	n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
	(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_exercises)

		Take a piece of paper.  For each of the following theorems, first
		_think_ about whether (a) it can be proved using only
		simplification and rewriting, (b) it also requires case
		analysis ([destruct]), or (c) it also requires induction.  Write
		down your prediction.  Then fill in the proof.  (There is no need
		to turn in your piece of paper; this is just to encourage you to
		reflect before you hack!) *)

Theorem leb_refl : forall n:nat,
	(n <=? n) = true.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem zero_neqb_S : forall n:nat,
	0 =? (S n) = false.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
	andb b false = false.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem S_neqb_0 : forall n:nat,
	(S n) =? 0 = false.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
	orb
		(andb b c)
		(orb (negb b)
				 (negb c))
	= true.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
	(n + m) * p = (n * p) + (m * p).
Proof.
	(* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
	n * (m * p) = (n * m) * p.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (add_shuffle3')

		The [replace] tactic allows you to specify a particular subterm to
	 rewrite and what you want it rewritten to: [replace (t) with (u)]
	 replaces (all copies of) expression [t] in the goal by expression
	 [u], and generates [t = u] as an additional subgoal. This is often
	 useful when a plain [rewrite] acts on the wrong part of the goal.

	 Use the [replace] tactic to do a proof of [add_shuffle3'], just like
	 [add_shuffle3] but without needing [assert]. *)

Theorem add_shuffle3' : forall n m p : nat,
	n + (m + p) = m + (n + p).
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Nat to Bin and Back to Nat *)

(** Recall the [bin] type we defined in [Basics]: *)

Inductive bin : Type :=
	| Z
	| B0 (n : bin)
	| B1 (n : bin)
.
(** Before you start working on the next exercise, replace the stub
		definitions of [incr] and [bin_to_nat], below, with your solution
		from [Basics].  That will make it possible for this file to
		be graded on its own. *)

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
