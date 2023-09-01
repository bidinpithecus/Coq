From MYCOQ Require Export Induction.
Module NatList.

Inductive natprod : Type :=
	| pair (n1 n2 : nat)
.

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
	match p with
	| pair x y => x
	end
.

Definition snd (p : natprod) : nat :=
	match p with
	| pair x y => y
	end
.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
	match p with
	| (x,y) => x
	end
.

Definition snd' (p : natprod) : nat :=
	match p with
	| (x,y) => y
	end
.

Definition swap_pair (p : natprod) : natprod :=
	match p with
	| (x,y) => (y,x)
	end
.

Theorem surjective_pairing' : forall (n m : nat),
	(n,m) = (fst (n,m), snd (n,m)).
Proof.
	reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
	p = (fst p, snd p).
Proof.
	simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
	p = (fst p, snd p).
Proof.
	intros p. destruct p as [n m].
	simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
	(snd p, fst p) = swap_pair p.
Proof.
	intros. destruct p as [n m].
	simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
	fst (swap_pair p) = snd p.
Proof.
	intros. destruct p as [n m].
	simpl. reflexivity.
Qed.

Inductive natlist : Type :=
	| nil
	| cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
										 (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
	match count with
	| O => nil
	| S count' => n :: (repeat n count')
	end
.

Fixpoint length (l: natlist) : nat :=
	match l with
	| nil => O
	| h :: t => S (length t)
	end
.

Fixpoint app (l1 l2: natlist) : natlist :=
	match l1 with
	| nil    => l2
	| h :: t => h :: (app t l2)
	end
.

Notation "x ++ y" := (app x y)
										 (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default: nat) (l: natlist): nat :=
	match l with
	| nil => default
	| h :: t => h
	end
.

Definition tl (l: natlist): natlist :=
	match l with
	| nil => nil
	| h :: t => t
	end
.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l: natlist) : natlist :=
	match l with
	| nil => nil
	| 0 :: t => nonzeros t
	| h :: t => h :: nonzeros t
	end
.

Example test_nonzeros:
	nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
	intros. simpl.
	reflexivity.
Qed.

Fixpoint oddmembers (l: natlist) : natlist :=
	match l with
	| nil => nil
	| h :: t => match (odd h) with
							| true => h :: (oddmembers t)
							| false => oddmembers t
							end
	end
.

Example test_oddmembers:
	oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
	intros. simpl.
	reflexivity.
Qed.

Definition countoddmembers (l: natlist) : nat :=
	length (oddmembers l).

Example test_countoddmembers1:
	countoddmembers [1;0;3;1;4;5] = 4.
Proof.
	intros. simpl.
	reflexivity.
Qed.

Example test_countoddmembers2:
	countoddmembers [0;2;4] = 0.
Proof.
	intros. simpl.
	reflexivity.
Qed.

Example test_countoddmembers3:
	countoddmembers nil = 0.
Proof.
	intros. simpl.
	reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
	match l1, l2 with
	| nil, t => t
	| t, nil => t
	| h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
	end
.

Example test_alternate1:
	alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
	intros. simpl.
	reflexivity.
Qed.

Example test_alternate2:
	alternate [1] [4;5;6] = [1;4;5;6].
Proof.
	intros. simpl.
	reflexivity.
Qed.

Example test_alternate3:
	alternate [1;2;3] [4] = [1;4;2;3].
Proof.
	reflexivity.
Qed.

Example test_alternate4:
	alternate [] [20;30] = [20;30].
Proof.
	reflexivity.
Qed.

Definition bag := natlist.

Fixpoint count (v: nat) (s: bag): nat :=
	match s with
	| nil => O
	| h :: t => if (h =? v) then S (count v t)
							else (count v t)
	end
.

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof.
	reflexivity.
Qed.

Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof.
	reflexivity.
Qed.

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
		the elements of [a] and of [b].  (Mathematicians usually define
		[union] on multisets a little bit differently -- using max instead
		of sum -- which is why we don't call this operation [union].)

		We've deliberately given you a header that does not give explicit
		names to the arguments.  Implement [sum] with an already-defined
		function without changing the header. *)

Definition sum : bag -> bag -> bag :=
	app
.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
	reflexivity.
Qed.

Definition add (v : nat) (s : bag) : bag :=
	v :: s
.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof.
	reflexivity.
Qed.

Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof.
	reflexivity.
Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
	match s with
	| nil => false
	| h :: t => if (h =? v) then true
							else (member v t)
	end
.

Example test_member1:             member 1 [1;4;1] = true.
Proof.
	reflexivity.
Qed.

Example test_member2:             member 2 [1;4;1] = false.
Proof.
	reflexivity.
Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
	match s with
	| [] => []
	| h :: t => if (h =? v) then t
							else h :: (remove_one v t)
	end
.

Example test_remove_one1:
	count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
	reflexivity.
Qed.

Example test_remove_one2:
	count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
	reflexivity.
Qed.

Example test_remove_one3:
	count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof.
	simpl. reflexivity.
Qed.

Example test_remove_one4:
	count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof.
	reflexivity.
Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
	match s with
	| [] => []
	| h :: t => if (h =? v) then (remove_all v t)
							else h :: (remove_all v t)
	end
.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof.
	reflexivity.
Qed.

Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof.
	reflexivity.
Qed.

Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof.
	reflexivity.
Qed.

Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof.
	reflexivity.
Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
	match s1 with
	| [] => true
	| h :: t => if (member h s2) then (included t (remove_one h s2))
							else false
	end
.

Example test_included1:              included [1;2] [2;1;4;1] = true.
Proof.
	reflexivity.
Qed.
Example test_included2:              included [1;2;2] [2;1;4;1] = false.
Proof.
	simpl. reflexivity.
Qed.

Definition manual_grade_for_add_inc_count : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As with numbers, simple facts about list-processing
		functions can sometimes be proved entirely by simplification.  For
		example, just the simplification performed by [reflexivity] is
		enough for this theorem... *)

Theorem nil_app : forall l : natlist,
	[] ++ l = l.
Proof. reflexivity. Qed.

(** ...because the [[]] is substituted into the
		"scrutinee" (the expression whose value is being "scrutinized" by
		the match) in the definition of [app], allowing the match itself
		to be simplified. *)

(** Also, as with numbers, it is sometimes helpful to perform case
		analysis on the possible shapes (empty or non-empty) of an unknown
		list. *)

Theorem tl_length_pred : forall l:natlist,
	pred (length l) = length (tl l).
Proof.
	intros l. destruct l as [| n l'].
	- (* l = nil *)
		reflexivity.
	- (* l = cons n l' *)
		reflexivity.  Qed.

(** Here, the [nil] case works because we've chosen to define
		[tl nil = nil]. Notice that the [as] annotation on the [destruct]
		tactic here introduces two names, [n] and [l'], corresponding to
		the fact that the [cons] constructor for lists takes two
		arguments (the head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
		induction for their proofs.  We'll see how to do this next. *)

(** (Micro-Sermon: As we get deeper into this material, simply
		_reading_ proof scripts will not get you very far!  It is
		important to step through the details of each one using Coq and
		think about what each step achieves.  Otherwise it is more or less
		guaranteed that the exercises will make no sense when you get to
		them.  'Nuff said.) *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Proofs by induction over datatypes like [natlist] are a
		little less familiar than standard natural number induction, but
		the idea is equally simple.  Each [Inductive] declaration defines
		a set of data values that can be built up using the declared
		constructors.  For example, a boolean can be either [true] or
		[false]; a number can be either [O] or [S] applied to another
		number; and a list can be either [nil] or [cons] applied to a
		number and a list.   Moreover, applications of the declared
		constructors to one another are the _only_ possible shapes
		that elements of an inductively defined set can have.

		This last fact directly gives rise to a way of reasoning about
		inductively defined sets: a number is either [O] or else it is [S]
		applied to some _smaller_ number; a list is either [nil] or else
		it is [cons] applied to some number and some _smaller_ list;
		etc. So, if we have in mind some proposition [P] that mentions a
		list [l] and we want to argue that [P] holds for _all_ lists, we
		can reason as follows:

			- First, show that [P] is true of [l] when [l] is [nil].

			- Then show that [P] is true of [l] when [l] is [cons n l'] for
				some number [n] and some smaller list [l'], assuming that [P]
				is true for [l'].

		Since larger lists can always be broken down into smaller ones,
		eventually reaching [nil], these two arguments together establish
		the truth of [P] for all lists [l].  Here's a concrete example: *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
	(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
	intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
	- (* l1 = nil *)
		reflexivity.
	- (* l1 = cons n l1' *)
		simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Notice that, as when doing induction on natural numbers, the
		[as...] clause provided to the [induction] tactic gives a name to
		the induction hypothesis corresponding to the smaller list [l1']
		in the [cons] case.

		Once again, this Coq proof is not especially illuminating as a
		static document -- it is easy to see what's going on if you are
		reading the proof in an interactive Coq session and you can see
		the current goal and context at each point, but this state is not
		visible in the written-down parts of the Coq proof.  So a
		natural-language proof -- one written for human readers -- will
		need to include more explicit signposts; in particular, it will
		help the reader stay oriented if we remind them exactly what the
		induction hypothesis is in the second case. *)

(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
							 [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

	 _Proof_: By induction on [l1].

	 - First, suppose [l1 = []].  We must show

			 ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

		 which follows directly from the definition of [++].

	 - Next, suppose [l1 = n::l1'], with

			 (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

		 (the induction hypothesis). We must show

			 ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

		 By the definition of [++], this follows from

			 n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

		 which is immediate from the induction hypothesis.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** For a slightly more involved example of inductive proof over
		lists, suppose we use [app] to define a list-reversing
		function [rev]: *)

Fixpoint rev (l:natlist) : natlist :=
	match l with
	| nil    => nil
	| h :: t => rev t ++ [h]
	end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** For something a bit more challenging than the proofs
		we've seen so far, let's prove that reversing a list does not
		change its length.  Our first attempt gets stuck in the successor
		case... *)

Theorem rev_length_firsttry : forall l : natlist,
	length (rev l) = length l.
Proof.
	intros l. induction l as [| n l' IHl'].
	- (* l = nil *)
		reflexivity.
	- (* l = n :: l' *)
		(* This is the tricky case.  Let's begin as usual
			 by simplifying. *)
		simpl.
		(* Now we seem to be stuck: the goal is an equality
			 involving [++], but we don't have any useful equations
			 in either the immediate context or in the global
			 environment!  We can make a little progress by using
			 the IH to rewrite the goal... *)
		rewrite <- IHl'.
		(* ... but now we can't go any further. *)
Abort.

(** So let's take the equation relating [++] and [length] that
		would have enabled us to make progress at the point where we got
		stuck and state it as a separate lemma. *)

Theorem app_length : forall l1 l2 : natlist,
	length (l1 ++ l2) = (length l1) + (length l2).
Proof.
	(* WORKED IN CLASS *)
	intros l1 l2. induction l1 as [| n l1' IHl1'].
	- (* l1 = nil *)
		reflexivity.
	- (* l1 = cons *)
		simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Note that, to make the lemma as general as possible, we
		quantify over _all_ [natlist]s, not just those that result from an
		application of [rev].  This should seem natural, because the truth
		of the goal clearly doesn't depend on the list having been
		reversed.  Moreover, it is easier to prove the more general
		property. *)

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
	length (rev l) = length l.
Proof.
	intros l. induction l as [| n l' IHl'].
	- (* l = nil *)
		reflexivity.
	- (* l = cons *)
		simpl. rewrite -> app_length.
		simpl. rewrite -> IHl'. rewrite add_comm.
		reflexivity.
Qed.

(** For comparison, here are informal proofs of these two theorems:

		_Theorem_: For all lists [l1] and [l2],
			 [length (l1 ++ l2) = length l1 + length l2].

		_Proof_: By induction on [l1].

		- First, suppose [l1 = []].  We must show

				length ([] ++ l2) = length [] + length l2,

			which follows directly from the definitions of
			[length], [++], and [plus].

		- Next, suppose [l1 = n::l1'], with

				length (l1' ++ l2) = length l1' + length l2.

			We must show

				length ((n::l1') ++ l2) = length (n::l1') + length l2.

			This follows directly from the definitions of [length] and [++]
			together with the induction hypothesis. [] *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

		_Proof_: By induction on [l].

			- First, suppose [l = []].  We must show

					length (rev []) = length [],

				which follows directly from the definitions of [length]
				and [rev].

			- Next, suppose [l = n::l'], with

					length (rev l') = length l'.

				We must show

					length (rev (n :: l')) = length (n :: l').

				By the definition of [rev], this follows from

					length ((rev l') ++ [n]) = S (length l')

				which, by the previous lemma, is the same as

					length (rev l') + length [n] = S (length l').

				This follows directly from the induction hypothesis and the
				definition of [length]. [] *)

(** The style of these proofs is rather longwinded and pedantic.
		After reading a couple like this, we might find it easier to
		follow proofs that give fewer details (which we can easily work
		out in our own minds or on scratch paper if necessary) and just
		highlight the non-obvious steps.  In this more compressed style,
		the above proof might look like this: *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

		_Proof_: First, observe that [length (l ++ [n]) = S (length l)]
		 for any [l], by a straightforward induction on [l].  The main
		 property again follows by induction on [l], using the observation
		 together with the induction hypothesis in the case where [l =
		 n'::l']. [] *)

(** Which style is preferable in a given situation depends on
		the sophistication of the expected audience and how similar the
		proof at hand is to ones that they will already be familiar with.
		The more pedantic style is a good default for our present
		purposes. *)

(* ================================================================= *)
(** ** [Search] *)

(** We've seen that proofs can make use of other theorems we've
		already proved, e.g., using [rewrite].  But in order to refer to a
		theorem, we need to know its name!  Indeed, it is often hard even
		to remember what theorems have been proven, much less what they
		are called.

		Coq's [Search] command is quite helpful with this.  Let's say
		you've forgotten the name of a theorem about [rev].  The command
		[Search rev] will cause Coq to display a list of all theorems
		involving [rev]. *)

Search rev.

(** Or say you've forgotten the name of the theorem showing that plus
		is commutative.  You can use a pattern to search for all theorems
		involving the equality of two additions. *)

Search (_ + _ = _ + _).

(** You'll see a lot of results there, nearly all of them from the
		standard library.  To restrict the results, you can search inside
		a particular module: *)

Search (_ + _ = _ + _) inside Induction.

(** You can also make the search more precise by using variables in
		the search pattern instead of wildcards: *)

Search (?x + ?y = ?y + ?x).

(** The question mark in front of the variable is needed to indicate
		that it is a variable in the search pattern, rather than a
		variable that is expected to be in scope currently. *)

(** Keep [Search] in mind as you do the following exercises and
		throughout the rest of the book; it can save you a lot of time!

		Your IDE likely has its own functionality to help with searching.
		For example, in ProofGeneral, you can run [Search] with [C-c C-a
		C-a], and paste its response into your buffer with [C-c C-;]. *)

(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars, standard (list_exercises)

		More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
	l ++ [] = l.
Proof.
	(* FILL IN HERE *) Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
	rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
	(* FILL IN HERE *) Admitted.

(** An _involution_ is a function that is its own inverse. That is,
		applying the function twice yield the original input. *)
Theorem rev_involutive : forall l : natlist,
	rev (rev l) = l.
Proof.
	(* FILL IN HERE *) Admitted.

(** There is a short solution to the next one.  If you find yourself
		getting tangled up, step back and try to look for a simpler
		way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
	l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
	(* FILL IN HERE *) Admitted.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
	nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (eqblist)

		Fill in the definition of [eqblist], which compares
		lists of numbers for equality.  Prove that [eqblist l l]
		yields [true] for every list [l]. *)

Fixpoint eqblist (l1 l2 : natlist) : bool
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_eqblist1 :
	(eqblist nil nil = true).
 (* FILL IN HERE *) Admitted.

Example test_eqblist2 :
	eqblist [1;2;3] [1;2;3] = true.
(* FILL IN HERE *) Admitted.

Example test_eqblist3 :
	eqblist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem eqblist_refl : forall l:natlist,
	true = eqblist l l.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** List Exercises, Part 2 *)

(** Here are a couple of little theorems to prove about your
		definitions about bags above. *)

(** **** Exercise: 1 star, standard (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
	1 <=? (count 1 (1 :: s)) = true.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(** The following lemma about [leb] might help you in the next
		exercise (it will also be useful in later chapters). *)

Theorem leb_n_Sn : forall n,
	n <=? (S n) = true.
Proof.
	intros n. induction n as [| n' IHn'].
	- (* 0 *)
		simpl.  reflexivity.
	- (* S n' *)
		simpl.  rewrite IHn'.  reflexivity.  Qed.

(** Before doing the next exercise, make sure you've filled in the
	 definition of [remove_one] above. *)
(** **** Exercise: 3 stars, advanced (remove_does_not_increase_count) *)
Theorem remove_does_not_increase_count: forall (s : bag),
	(count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bag_count_sum)

		Write down an interesting theorem [bag_count_sum] about bags
		involving the functions [count] and [sum], and prove it using
		Coq.  (You may find that the difficulty of the proof depends on
		how you defined [count]!  Hint: If you defined [count] using
		[=?] you may find it useful to know that [destruct] works on
		arbitrary expressions, not just simple identifiers.)
*)
(* FILL IN HERE

		[] *)

(** **** Exercise: 3 stars, advanced (involution_injective) *)

(** Prove that every involution is injective. Involutions were defined
		above in [rev_involutive]. An _injective_ function is one-to-one:
		it maps distinct inputs to distinct outputs, without any
		collisions. *)

Theorem involution_injective : forall (f : nat -> nat),
		(forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
	(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, advanced (rev_injective)

		Prove that [rev] is injective. Do not prove this by induction --
		that would be hard. Instead, re-use the same proof technique that
		you used for [involution_injective]. Do not try to use that
		exercise directly as a lemma: the types are not the same. *)

Theorem rev_injective : forall (l1 l2 : natlist),
	rev l1 = rev l2 -> l1 = l2.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Options *)

(** Suppose we want to write a function that returns the [n]th
		element of some list.  If we give it type [nat -> natlist -> nat],
		then we'll have to choose some number to return when the list is
		too short... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
	match l with
	| nil => 42
	| a :: l' => match n with
							 | 0 => a
							 | S n' => nth_bad l' n'
							 end
	end.

(** This solution is not so good: If [nth_bad] returns [42], we
		can't tell whether that value actually appears on the input
		without further processing. A better alternative is to change the
		return type of [nth_bad] to include an error value as a possible
		outcome. We call this type [natoption]. *)

Inductive natoption : Type :=
	| Some (n : nat)
	| None.

(** We can then change the above definition of [nth_bad] to
		return [None] when the list is too short and [Some a] when the
		list has enough members and [a] appears at position [n]. We call
		this new function [nth_error] to indicate that it may result in an
		error. As we see here, constructors of inductive definitions can
		be capitalized. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
	match l with
	| nil => None
	| a :: l' => match n with
							 | O => Some a
							 | S n' => nth_error l' n'
							 end
	end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** (In the HTML version, the boilerplate proofs of these
		examples are elided.  Click on a box if you want to see one.)
*)

(** The function below pulls the [nat] out of a [natoption], returning
		a supplied default in the [None] case. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
	match o with
	| Some n' => n'
	| None => d
	end.

(** **** Exercise: 2 stars, standard (hd_error)

		Using the same idea, fix the [hd] function from earlier so we don't
		have to pass a default element for the [nil] case.  *)

Definition hd_error (l : natlist) : natoption
	(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (option_elim_hd)

		This exercise relates your new [hd_error] to the old [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
	hd default l = option_elim default (hd_error l).
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
		Coq, here is a simple _partial map_ data type, analogous to the
		map or dictionary data structures found in most programming
		languages. *)

(** First, we define a new inductive datatype [id] to serve as the
		"keys" of our partial maps. *)

Inductive id : Type :=
	| Id (n : nat).

(** Internally, an [id] is just a number.  Introducing a separate type
		by wrapping each nat with the tag [Id] makes definitions more
		readable and gives us flexibility to change representations later
		if we want to. *)

(** We'll also need an equality test for [id]s: *)

Definition eqb_id (x1 x2 : id) :=
	match x1, x2 with
	| Id n1, Id n2 => n1 =? n2
	end.

(** **** Exercise: 1 star, standard (eqb_id_refl) *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
	(* FILL IN HERE *) Admitted.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
Export NatList.  (* make the definitions from NatList available here *)

Inductive partial_map : Type :=
	| empty
	| record (i : id) (v : nat) (m : partial_map).

(** This declaration can be read: "There are two ways to construct a
		[partial_map]: either using the constructor [empty] to represent an
		empty partial map, or applying the constructor [record] to
		a key, a value, and an existing [partial_map] to construct a
		[partial_map] with an additional key-to-value mapping." *)

(** The [update] function overrides the entry for a given key in a
		partial map by shadowing it with a new one (or simply adds a new
		entry if the given key is not already present). *)

Definition update (d : partial_map)
									(x : id) (value : nat)
									: partial_map :=
	record x value d.

(** Last, the [find] function searches a [partial_map] for a given
		key.  It returns [None] if the key was not found and [Some val] if
		the key was associated with [val]. If the same key is mapped to
		multiple values, [find] will return the first one it
		encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
	match d with
	| empty         => None
	| record y v d' => if eqb_id x y
										 then Some v
										 else find x d'
	end.

(** **** Exercise: 1 star, standard (update_eq) *)
Theorem update_eq :
	forall (d : partial_map) (x : id) (v: nat),
		find x (update d x v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (update_neq) *)
Theorem update_neq :
	forall (d : partial_map) (x y : id) (o: nat),
		eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)
End PartialMap.

(** **** Exercise: 2 stars, standard, optional (baz_num_elts)

		Consider the following inductive definition: *)

Inductive baz : Type :=
	| Baz1 (x : baz)
	| Baz2 (y : baz) (b : bool).

(** How _many_ elements does the type [baz] have? (Explain in words,
		in a comment.) *)

(* FILL IN HERE *)

(** [] *)

(* 2023-03-25 11:11 *)
