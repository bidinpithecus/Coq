(* Vinícios Bidin Santos *)

Require Export Coq.Lists.List.
Import ListNotations.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
  Proof.
  intros X P H1 H2.
  destruct H2 as [x H3].
  apply H3.
  apply H1.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - intros H.
    destruct H as [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros H.
    destruct H as [HP | HQ].
    + destruct HP as [x HP].
      exists x. left. apply HP.
    + destruct HQ as [x HQ].
      exists x. right. apply HQ.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros X P Q H.
  destruct H as [x [HP HQ]].
  split.
    - exists x. apply HP.
    - exists x. apply HQ.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x Hin.
  induction l as [|x' l' IHl].
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin_tail].
    + left. rewrite Heq. reflexivity.
    + right. apply IHl. apply Hin_tail.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. split.
  induction l as [|h t].
  - simpl. intros [].
  - simpl. intros [H | H].
    + exists h. split. apply H. left. reflexivity.
    + apply IHt in H. destruct H as [w [F I]].
      exists w. split. apply F. right. apply I.
  - intros [w [F I]].
    rewrite <- F. apply In_map. apply I.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - induction l as [|h t].
    + simpl. intro. right. apply H.
    + simpl. intros [H | H].
      * left. left. apply H.
      * apply IHt in H. destruct H.
        { left. right. apply H. }
        { right. apply H. }
  - induction l as [|h t].
    + intros [H | H].
      * inversion H.
      * simpl. apply H.
    + intros [H | H].
      * simpl. inversion H.
        { left. apply H0. }
        { right. apply IHt. left. apply H0. }
      * simpl. right. apply IHt. right. apply H.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P H.
  apply H. right. intro H'. apply H. left. apply H'.
Qed.

Theorem disj_impl : forall (P Q: Prop),
 (~P \/ Q) -> P -> Q.
Proof.
  intros P Q HnotP_or_Q HP.
  destruct HnotP_or_Q as [HnotP | HQ].
  - contradiction.
  - apply HQ.
Qed.

Theorem Peirce_double_negation: forall (P:Prop), (forall P Q: Prop,
  (((P->Q)->P)->P)) -> (~~ P -> P).
Proof.
  intros P H HNNP.
  unfold not in HNNP.
  apply H with (Q := False).
  intros HPQ.
  apply HNNP in HPQ.
  contradiction.
Qed.

Theorem double_negation_excluded_middle : forall (P:Prop),
  (forall (P:Prop), (~~ P -> P)) -> (P \/ ~P). 
Proof.
  intros.
  apply H.
  intros H2.
  unfold not in H2.
  apply H2.
  right.
  intros p.
  exfalso.
  apply H2.
  left.
  apply p.
Qed.
