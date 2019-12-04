Inductive naravno : Type :=
| nic : naravno
| nasl : naravno -> naravno.

Theorem niso_vsa_naravna_nic : not (forall n: naravno, n = nic).
Proof.
  intro.
  specialize (H (nasl(nic))).
  discriminate H.
Qed.

Fixpoint plus (n m : naravno) : naravno :=
  match n with
  | nic => m
  | nasl(x) => plus x (nasl m)
  end.

Theorem plus_assoc : forall n m k: naravno, plus (plus n m) k = plus n (plus m k).
Proof.
  intros.
  induction n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
