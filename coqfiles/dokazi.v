

Theorem or_comm : forall p q, p \/ q -> q \/ p.
Proof.
  intros.
  case H.
  - intros proof_p.
    refine (or_intror proof_p).
  - intros proof_q.
    refine (or_introl proof_q).
Qed.

Theorem modus_ponens : forall p q : Prop, (p -> q) /\ p -> q.
Proof.
  intros.
  destruct H as [implic proof_p].
  apply implic.
  exact proof_p.
Qed.

Theorem and_comm : forall p q : Prop, p /\ q -> q /\ p.
Proof.
  intros.
  destruct H as [andl andr].
  split.
  - exact andr.
  - exact andl.
Qed.

Theorem distribute_and : forall p q r : Prop, (p \/ q) /\ r -> (p /\ r) \/ (q /\ r).
Proof.
  intros.
  destruct H as [or_comb proof_r].
  case or_comb.
  - intros.
    left.
    split.
    * exact H.
    * exact proof_r.
  - intros.
    right.
    exact (conj H proof_r).
Qed.

Theorem distribute_or : forall p q r : Prop, (p /\ q) \/ r -> (p \/ r) /\ (q \/ r).
Proof.
  intros.
  destruct H.
  - destruct H as [proof_p proof_q].
    split.
    {
      left.
      exact proof_p.
    }
    {
      left.
      exact proof_q.
    }
  - split.
    exact (or_intror H).
    exact (or_intror H).
Qed.

Theorem and_or_impl : forall p q r : Prop, ((p -> r) /\ (q -> r)) <-> (p \/ q -> r).
Proof.
  intros.
  unfold iff.
  split.
  {
    intros.
    destruct H as [leva desna].
    case H0.
    - intros.
      apply leva.
      exact H.
    - intros.
      apply desna.
      exact H.
  }
  {
    intros.
    split.
    - intros.
      apply H.
      exact (or_introl H0).
    - intros.
      apply H.
      exact (or_intror H0).
  }
Qed.

Theorem and_or_impl' : forall p q r : Prop, ((p -> r) /\ (q -> r)) <-> (p \/ q -> r).
Proof.
  firstorder.
Qed.


