inductive naravno : Type
| nic : naravno
| nasl : naravno -> naravno

inductive seznam_naravnih_stevil : Type
| prazen : seznam_naravnih_stevil
| sestavljen : naravno -> seznam_naravnih_stevil -> seznam_naravnih_stevil

inductive seznam_dolzine : naravno -> Type
| prazen : seznam_dolzine naravno.nic
| sestavljen : ∀ n, naravno -> seznam_dolzine n -> seznam_dolzine (naravno.nasl n)

inductive ali : Prop -> Prop -> Prop
| inl : ∀ p q, p -> ali p q
| inr : ∀ p q, q -> ali p q

#check ali.rec
#check or.rec
#check or.inl

-- P \/ Q => Q \/ P
def or_comm' : ∀ p q, p ∨ q -> q ∨ p :=
  λ p q h_p_q, or.rec or.inr or.inl h_p_q

theorem or_comm'' : ∀ p q, p ∨ q -> q ∨ p := begin
  intro p, intro q, intro h, cases h,
  case or.inl {
    apply or.inr,
    exact h,
  },
  case or.inr {
    left,
    assumption,
  }
end

#print or_comm''

theorem or_comm'' : forall p q, p ∨ q -> q ∨ p := begin
  intros,
  cases a,
  case or.inl { apply or.inr, exact a },
  case or.inr { apply (or.inl a) }
end

-- (P => Q) /\ P => Q

-- P /\ Q => Q /\ P

-- (P \/ Q) /\ R => (P /\ R) \/ (Q /\ R)

-- (P /\ Q) \/ R => (P \/ R) /\ (Q \/ R)

-- (P => R) => (Q => R) <=> ((P \/ Q) => R)

-- P \/ Q => P /\ Q
