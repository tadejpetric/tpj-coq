
(* to so komentarji *)

(* -> predstavlja implikacijo *)
(* izrek komutativnost or *)
Theorem or_comm : forall p q, p \/ q -> q \/ p.
Proof.
  (* dokazujemo implikacijo H => G
   torej predpostavimo H*)
  intros.
  (* V predpostavkah drži (p ali q). Torej ali drži p, ali q 
   cases loči na te primere*)
  case H.
  (* alineje strukturirano povejo v katirem delu koraka smo. Namesto njih so 
     tudi * ali pa {} *)
  (* V tej točki nam Coq pove:
     p,q : Prop (torej p in q sta predikata)
     H : p \/ q (to je v predpostavkah)
     ============================ (te črte vedno ločujejo predpostavke od cilja)
     p -> q \/ p (to moremo dokazati za prvi primer)
     
     subgoal 2 (ID 8) is:
     q -> q \/ p (ko bomo dokazali tisto zgoraj bomo morali še ta primer dokazati)
   *)
  - intros proof_p.
    (* 
       spet smo dobili dokaz implikacije torej predpostavimo levo stran
       Lahko ji damo tudi eksplicitno ime, proof_p.
       Tukaj Coq pravi
       p, q : Prop
       H : p \/ q
       proof_p : p
       ============================
       q \/ p
     *)
    refine (or_intror proof_p).
    (* refine pove, da uporabimo neko "funkcijo" na izrazu
       tukaj uporabimo funkcijo or_intror. Ta pravi, da če p drži, tudi q ali p
       To je pa ravno to kar je bilo potrebno dokazati!
       drugi primer naredimo podobno
     *)
  - intros proof_q.
    refine (or_introl proof_q).
Qed.

(*
logične izjave imajo ponavadi introduction rule in elimination rule
to so pravila s katerimi vpeljemo operacijo in s katerim jo izničimo
primer za or:
introduction je da če p, potem tudi q \/ p in p \/ q
elimination je da če p \/ q potem preverimo primer p in primer q

naslednja trditev ina konjunkcijo, tukaj sta pravili taki
introduction: če p drži in q drži potem p /\ q
elimination: če p /\ q drži potem p drži in q drži
ta elimination pravilo za /\ pokličemo z destruct
*)

Theorem modus_ponens : forall p q : Prop, (p -> q) /\ p -> q.
Proof.
  intros.
  (* spet implikacija 
     tukaj je  H : (p -> q) /\ p *)
  destruct H as [implic proof_p].
  (* po temu pravilu je
     implic : p -> q
     proof_p : p
     ============================
     q
   *)
  apply implic.
  (* s taktiko apply lahko implikacijo uporabimo na cilju
   če moramo dokazati q in vemo da p -> q, lahko dokažemo samo p
   apply naredi točno to
   *)
  (*
    p, q : Prop
    implic : p -> q
    proof_p : p
    ============================
    p
   *)
  exact proof_p.
  (* morali smo dokazati p, ampak dokaz p je že proof_p*)
Qed.

Theorem and_comm : forall p q : Prop, p /\ q -> q /\ p.
Proof.
  intros.
  destruct H as [andl andr].
  (*
    split je elimination rule za konjunkcijo
    prej smo dokazovali q /\ p, zdaj ločeno dokazujemo najprej p, potem q
   *)
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
    (* če moramo dokazati a \/ b ampak vemo da a drži ni potrebno ločiti na dva primera
     lahko samo dokažemo šibkejšo trditev, da drži a
     to naredimo z left (povemo da bomo dokazali da leva stran pač vedno drži)*)
    left.
    split.
    * exact H.
    * exact proof_r.
  - intros.
    (* tukaj pa desna stran vedno drži *)
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
  (* 
     coq dovoli tudi bolj zahtevne operatorje. Na primer, natanko takrat, <-> je
     definiran kakor obe implikaciji (a <-> b) pomeni (a->b) /\ (b->a)
     unfold unfolds the definition, jo razpiše
   *)
  (*
    v tej točki Coq pravi 
    p, q, r : Prop
    ============================
    (p -> r) /\ (q -> r) <-> (p \/ q -> r)
   *)
  unfold iff.
  (*
    tukaj pa
    p, q, r : Prop
    ============================
    ((p -> r) /\ (q -> r) -> p \/ q -> r) /\ ((p \/ q -> r) -> (p -> r) /\ (q -> r))
   *)
  split. (* split dela podobno kot destruct, loči konjunkcijo na primere *)
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

(* Coq ima tudi bolj napredne taktike, ki bi vse zgoraj rešile v eni vrstici
tukaj je primer ene take taktike

taktike, ki bi dokazala vse izreke iz matematike ni (in se da dokazati da ne more obstajati)
ampak če dovolj zožaš obseg matematike je pa možno (glej presburger arithmetic. So naravna števila s 
samo seštevanjem, brez množenja. obstaja taktika, ki ti tukaj lahko dokaže vse izreke v eni vrstici!)
*)
Theorem and_or_impl' : forall p q r : Prop, ((p -> r) /\ (q -> r)) <-> (p \/ q -> r).
Proof.
  firstorder.
Qed.


