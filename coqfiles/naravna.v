Module nar.
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
  | nasl(x) => nasl(plus x m)
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
     rewrite IHn.
     reflexivity.
  }
Qed.


Lemma plus_succ : forall n m, nasl (plus n m) = plus n (nasl m).
Proof.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  f_equal.
  exact IHn.
Qed.

  
Theorem plus_comm : forall m n, plus m n = plus n m.
Proof.
  intros.
  induction m.
  {
    simpl.
    induction n.    
    auto.
    simpl.
    f_equal.
    exact IHn.
  }
  {
    simpl.
    induction n.
    - simpl.
      f_equal.
      rewrite IHm.
      simpl.
      tauto.
    - simpl.
      f_equal.
      rewrite IHm.
      simpl.  
      apply plus_succ.
  }
Qed.

        
Inductive je_sodo : naravno -> Prop :=
| Enic : je_sodo nic
| Enasl_nasl n : je_sodo n -> je_sodo (nasl (nasl n)).

Check (Enasl_nasl (nasl (nasl  nic))).

Lemma stiri_je_sodo : je_sodo (nasl (nasl (nasl (nasl nic)))).
Proof.
  apply Enasl_nasl.
  apply Enasl_nasl.
  apply Enic.
Qed.

Theorem sodo_plus_sodo : forall m n, je_sodo m -> je_sodo n -> je_sodo (plus m n).
Proof.
  intros.
  induction H.
  {
    simpl.
    trivial.
  }
  {
    simpl.
    apply Enasl_nasl.
    trivial.
  }
Qed.
End nar.

Module ineq.
Inductive manj_enako : nar.naravno -> nar.naravno -> Prop :=
| nic : forall m, manj_enako nar.nic m
| nasl : forall m n,  manj_enako m n -> manj_enako (nar.nasl m) (nar.nasl n).

Inductive manj_enako' : nar.naravno -> nar.naravno -> Prop :=
| refl' : forall m, manj_enako' m m
| nasl' : forall m n, manj_enako' m n -> manj_enako' m (nar.nasl n).

Lemma leq_do_nasl : forall m, manj_enako m (nar.nasl m).
Proof.
  intros.  
  induction m.
  - apply nic.
  - apply nasl.
    tauto.
Qed.

Lemma leq_do_nasl' : forall m, manj_enako' m (nar.nasl m).
Proof.
  intros.
  induction m.
  {
    apply nasl'.
    apply refl'.
  }
  {
    apply nasl'.
    apply refl'.
  }
Qed.

Lemma nic_nima_prednika : not (exists m, manj_enako (nar.nasl m) nar.nic).
Proof.
  intro.
  destruct H.
  induction x.
  inversion H.
  inversion H.
Qed.

  
Theorem manj_enako_refl : forall m, manj_enako m m.
Proof.
  intros.
  induction m.
  {
    apply nic.
  }
  {
    apply nasl.
    exact IHm.
  }
Qed.

Theorem manj_enako_trans : forall q p r, manj_enako q p -> manj_enako p r -> manj_enako q r.
Proof.
  intros.
  induction p.
  {
    induction q.
    exact H0.
    case H.
    - intros.
      apply nic.
    - intros.
      inversion H.
  }
  admit.
Admitted.

Theorem manj_enako_trans' : forall p q r, (manj_enako' p q /\ manj_enako' q r) -> manj_enako' q r.
Proof.
  intros.
  destruct H as [leva desna].
  induction leva.
  exact desna.
  exact desna.
Qed.
