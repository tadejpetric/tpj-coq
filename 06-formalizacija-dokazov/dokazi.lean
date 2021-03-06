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

theorem or_comm''' : forall p q, p ∨ q -> q ∨ p := begin
  intros,
  cases a,
  case or.inl { apply or.inr, exact a },
  case or.inr { apply (or.inl a) }
end

-- (P => Q) /\ P => Q

-- P /\ Q => Q /\ P
theorem t2: forall p q, p ∧ q -> q ∧ p :=
begin
  intros,
  cases a,
  show  q ∧ p, from and.intro a_right a_left,
  --and.intro (and.right a_left) (and.left a_right),
end

theorem orintroleft : forall p q: Prop, p -> (p ∨ q) :=
begin
  intros,
  show p ∨ q, from or.intro_left q a,
end
theorem orintroright : forall p q: Prop, p -> (q ∨ p) :=
begin
  intros,
  show q ∨ p, from or.intro_right q a,
end

-- (P \/ Q) /\ R => (P /\ R) \/ (Q /\ R)
theorem t3 : forall p q r, (p ∨ q) ∧ r -> (p ∧ r) ∨ (q ∧ r) := 
begin
  intros,
  cases a,
  cases a_left,
  case or.inl {
    apply orintroleft,
    show p ∧ r, from and.intro a_left a_right,
  },
  case or.inr {
    apply orintroright,
    exact and.intro a_left a_right,
  }
end
-- (P /\ Q) \/ R => (P \/ R) /\ (Q \/ R)

-- (P => R) => (Q => R) <=> ((P \/ Q) => R)
-- r = ⊥    p = ⊤   q = ⊤ 
-- a : ⊥ → (q → r),
-- a_1 : p

theorem t5 : forall p q r : Prop, (p -> r) -> ((q -> r) ↔ ((p ∨ q) -> r)) := 
begin
  intros,
  apply iff.intro,
  {
    intros,
    cases a_2,
    case or.inl {
      apply a,
      assumption,
    },
    case or.inr {
      apply a_1,
      assumption,
    },
  },
  {
    intros,
    apply a_1,
    apply orintroright,
    assumption,
  }
end

-- P \/ Q => P /\ Q
