Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Notation "'0'" := (O).

Inductive nat_list : Set :=
| Nil : nat_list
| Cons : nat -> nat_list -> nat_list.

Notation "'[]'" := (Nil).
Notation "x '::' xs" := (Cons x xs).

Inductive nat_list_of_len : nat -> Set :=
| Nill : nat_list_of_len 0
| Conss : forall n, nat -> nat_list_of_len n -> nat_list_of_len (S n).

Inductive muf_ali (A B : Prop) : Prop :=
| muf_ali_inl : A -> muf_ali A B
| muf_ali_inr : B -> muf_ali A B.

Arguments muf_ali_inl {_}.
Arguments muf_ali_inl {_} {_}.
Arguments muf_ali_inr {_}.
Arguments muf_ali_inr {_} {_}.

Theorem muf_ali_comm : forall p q, (muf_ali p q) -> (muf_ali q p).
Proof.
  intros A B.
  intros H.
  case H.
  - intros proof_of_A.
    refine (muf_ali_inr proof_of_A).
  - intros proof_of_B.
    refine (muf_ali_inl proof_of_B).
Qed.

Inductive muf_in (A B:Prop) : Prop :=
muf_in_conj : A -> B -> muf_in A B.

Arguments muf_in_conj {_}.
Arguments muf_in_conj {_} {_}.

Theorem muf_in_comm : forall A B, muf_in A B -> muf_in B A.
Proof.
  destruct 1.
  apply muf_in_conj.
  exact H0.
  exact H.
Qed.

(* (P => Q) /\ P => Q *)
Theorem modus_ponens : forall P Q : Prop, muf_in (P -> Q) P -> Q.
Proof.
  destruct 1 as [H HP].
  apply H.
  assumption.
Qed.

(* (P \/ Q) /\ R => (P /\ R) \/ (Q /\ R) *)
Theorem t3 : forall p q r, muf_in (muf_ali p q) r -> muf_ali (muf_in p r) (muf_in q r).
Proof.
  intros P Q R.
  destruct 1 as [H HR].
  case H.
  - intros HP.
    left.
    apply muf_in_conj; assumption.
  - intros HQ.
    right.
    apply muf_in_conj; assumption.
Qed.

(* (P /\ Q) \/ R => (P \/ R) /\ (Q \/ R) *)
Theorem dist' : forall P Q R, muf_ali ( muf_in P Q) R -> muf_in (muf_ali P R) (muf_ali Q R).
Proof.
  destruct 1.
  - destruct H as [HP HQ].
    apply muf_in_conj.
    apply muf_ali_inl.
    assumption.
    apply muf_ali_inl.
    assumption.
  - apply muf_in_conj.
    apply muf_ali_inr.
    assumption.
    apply muf_ali_inr.
    assumption.
Qed.


(* (P => R) /\ (Q => R) <=> ((P \/ Q) => R) *)
Theorem t4 : forall P Q R: Prop, muf_in (P -> R) (Q -> R) <-> ((muf_ali P Q) -> R).
Proof.
  split.
  - intros.
    destruct H.
    destruct H0.
    + apply H.
      assumption.
    + apply H1.
      assumption.
  - split.
    + intros HP.
      apply H.
      exact (muf_ali_inl HP).
    + intros HQ.
      apply H.
      exact (muf_ali_inr HQ).
Qed.


Theorem sad : forall P Q: Prop, muf_in P Q -> muf_ali P Q.
Proof.
  intros.
  right.
  apply H.
Qed.
