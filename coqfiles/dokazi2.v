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
