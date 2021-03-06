(*
prej smo uporabljali le tip Prop, propositions
lahko pa ustvarimo svoje tipe!
V tej datoteki ustvarimo tip naravnih števil in nekaj osnovnih operacij na njih

Module nar. samo pove, da tukaj definiramo naravna števila, ni pomembno
*)

Module nar.
(*
naravna števila so tipičen primer induktivnega tipa
imajo prvi element (nič)
in imajo funkcijo naslednjika
tako definiramo naravna števila v coqu
*)
Inductive naravno : Type :=
| nic : naravno
| nasl : naravno -> naravno.
(* tukaj -> predstavlja funkcijo *)

Theorem niso_vsa_naravna_nic : not (forall n: naravno, n = nic).
Proof.
  intro.
  specialize (H (nasl(nic))).
  discriminate H.
Qed.

(* fixpoint pomeni funkcija (razlog je da se funkcije formalno definira kot fiksna točka
neke drugačne funkcije, ni pomembno) *)
Fixpoint plus (n m : naravno) : naravno :=
  match n with
  | nic => m (* 0 + m = m *)
  | nasl(x) => nasl(plus x m) (* (1+x) + n = 1+ (x+n) *)
  end.

(* dokažemo, da je + asociativen *)
Theorem plus_assoc : forall n m k: naravno, plus (plus n m) k = plus n (plus m k).
Proof.
  intros.
  (* dokažemo s indukcijo na n*)
  induction n.
  {
    (* lahko bi napisali -, tako kot v prejšnji datoteki. Najprej primer n=0 *)
    (* Coq pove
        m, k : naravno
        ============================
        plus (plus nic m) k = plus nic (plus m k)
     *)
    simpl.
    (* simpl lahko uporbi definicijo + da najde 0+a = a *)
    (* Coq pove
       m, k : naravno
       ============================
       plus m k = plus m k
     *)
    reflexivity.
  }
  {
     simpl.
     rewrite IHn.
     reflexivity.
  }
Qed.

(* dokaz 1 + (n + m) = n + (1 + m) *)
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

(* definiramo tip sodih števil. Število je sodo če je nič, ali pa če je 2+sodo*)        
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

(* dokaz, da je vsota sodih soda *)
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
(* note: povsod sem pisal (plus n m) ampak če ne bi bil len bi lahko definiral nov operator
potem bi lahko pisal (n + m) kot v normalni matematiki (ampak takrat še nisem znal tega v Coq) *)
(* zdaj smo končali modul naravnih števil, če želimo uporabljati karkoli iz tam, pišemo nar.izrek *)

Module ineq.
(*
dve definiciji operatorja <=

1)
0 <= vse
n<=m če n+1 <= m+1

2)
m <= m
m <= n če m <= n+1

Kdaj je lažje uporabljati kakšno definicijo, kdaj drugo! To je zelo pomembno pri formalizaciji
kdaj si olajšamo dokaz 300% samo da izberemo drugo definicijo
*)
  
Inductive manj_enako : nar.naravno -> nar.naravno -> Prop :=
| nic : forall m, manj_enako nar.nic m
| nasl : forall m n,  manj_enako m n -> manj_enako (nar.nasl m) (nar.nasl n).

Inductive manj_enako' : nar.naravno -> nar.naravno -> Prop :=
| refl' : forall m, manj_enako' m m
| nasl' : forall m n, manj_enako' m n -> manj_enako' m (nar.nasl n).

(* Toy dokaz da m <= m+1 *)
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

(* negacija ~p je definirana kot p -> false *)
Lemma nic_nima_prednika' : forall m, not (manj_enako' (nar.nasl m) nar.nic).
Proof.
  intro.
  unfold not.
  intros.
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
  (* če ne znamo dokaza, napišemo admit. Pomeni, da se predamo. Potem Coq dovoli, da to trditev
   uporabimo v ostalih dokazih (ampak zmeraj naredi opozorilo da uporabljaš nedokazane trditve)
   je tudi uporabno za strukturirano pisanje dokazov. razdeliš na veliko malih delov in dolker niso dokončani
napišeš admit v njih (lahko jih pa uporabiš v večjem) *)
  admit.
Admitted.


Lemma manj'_ohranja_predhodnike : forall m n, manj_enako' m n -> manj_enako' (nar.nasl m) (nar.nasl n).
Proof.
  intros.
  induction m.
  apply nasl' in H.
  admit.
Admitted.

Lemma nic_najmanjsa : forall n, manj_enako' nar.nic n.
Proof.
  induction n.
  apply refl'.
  apply nasl'.
  exact IHn.
Qed.
  
Lemma manj'_ohranja_naslednjike : forall m n, manj_enako' (nar.nasl m) (nar.nasl n) -> manj_enako' m n.
Proof.
  intros.
  induction n.
  destruct m.
  apply refl'.
  admit.
Admitted.


Theorem manj_enako_trans' : forall p q r, (manj_enako' p q /\ manj_enako' q r) -> manj_enako' p r.
Proof.
  intros.
  destruct H as [leva desna].
  induction leva.
  exact desna.
  apply IHleva.
  induction r.
  inversion desna.
  apply nasl'.
  apply manj'_ohranja_naslednjike.
  assumption.
Qed.
End ineq.

(* tukaj sem se predal s tistimi definicijami <= in uporabil neko, ki mi je davorin predlagal lol
potem so dokazi zelo lažji *)
Module davorin.

(* neinduktivna definicija <= 

a <= b če lahko a prištejemo neko naravno število in dobimo b 
 *)

Definition leq (m n : nar.naravno) := exists x : nar.naravno, nar.plus m x = n.

Theorem leq_refl : forall m, leq m m.
Proof.
  intros.
  unfold leq.
  apply ex_intro with nar.nic.
  apply nar.plus_comm.
Qed.

Theorem leq_trans : forall q p r, (leq q p /\ leq p r) -> leq q r.
Proof.
  intros.
  destruct H as [left right].
  unfold leq.
  unfold leq in left, right.
  elim left.
  intros.
  elim right.
  intros.
  apply ex_intro with (nar.plus x x0).
  symmetry in H0.
  rewrite H0.
  symmetry in H.
  rewrite H.
  symmetry.
  apply nar.plus_assoc.
Qed.

Lemma zero_is_neutral : forall n, n = nar.plus n nar.nic.
Proof.
  intros.
  rewrite nar.plus_comm.
  simpl.
  tauto.
Qed.

Lemma add_both_sides : forall n m p, n = m -> nar.plus p n = nar.plus p m.
Proof.
  intros.
  f_equal.
  assumption.
Qed.


(* še nedokončan od zadnjič, ignore *)
Theorem leq_antisym : forall p q, leq p q /\ leq q p -> p = q.
Proof.
  intros.
  destruct H as [lefty righty].
  unfold leq in lefty, righty.
  elim lefty.
  elim righty.
  repeat intros.
  symmetry in H,  H0.
  rewrite H, H0.
  rewrite H0 in H.
  assert (sum_is_zero : nar.nic = nar.plus x0 x).
  {
    rewrite nar.plus_assoc in H.
    pattern p at 1 in H.
    rewrite zero_is_neutral in H.
    induction p.
    

    
  assert (newx : x0= nar.plus x0 nar.nic).
  {
    rewrite nar.plus_comm.
    simpl.
    tauto.
  }
  admit.
Admitted.
End davorin.
