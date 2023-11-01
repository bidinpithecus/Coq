Require Export Coq.Lists.List.
Import ListNotations.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Lemma eq_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
  intros X l1 l2 x.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof. intros X Y l. induction l as [|h l IH].
  - intros l1 l2 H. 
    inversion H. reflexivity.
  - intros [|h1 l1] [|h2 l2] H.
    + simpl in H. destruct (split l), h in H.
    inversion H.
    + simpl in H. destruct (split l), h in H.
    inversion H.
    + simpl in H. destruct (split l), h in H.
    inversion H.
    + simpl in H. destruct h.
    destruct (split l). inversion H.
    replace l with (combine l1 l2).
    reflexivity. apply IH.
    rewrite H2, H4. reflexivity.
Qed.

Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros. generalize dependent l1.
  generalize dependent l2. induction l.
  - intros. destruct l1,l2.
    reflexivity. discriminate H.
    discriminate H. simpl in H0.
    discriminate H0.
  - intros. destruct a, l1 ,l2.
    * discriminate H0.
    * discriminate H0.
    * discriminate H0.
    * simpl in H0. simpl in H.
      injection H as H. apply IHl in H.
      injection H0 as H1 H2 H3.
      + simpl. rewrite H.
      rewrite H1, H2. reflexivity.
      + injection H0 as H1 H2 H3. apply H3.
Qed.
