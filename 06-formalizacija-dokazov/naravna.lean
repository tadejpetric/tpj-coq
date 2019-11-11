inductive naravno : Type    -- type naravno = 
| nic : naravno             -- | Nic
| nasl : naravno -> naravno -- | Nasl of naravno

def plus : naravno -> naravno -> naravno
| naravno.nic      m := m
| (naravno.nasl m) n := naravno.nasl (plus m n)

theorem plus_assoc : forall m n p, plus (plus m n) p = plus m (plus n p) :=
  begin
    intros,
    induction m,
    case naravno.nic {
      unfold plus,
    },
    case naravno.nasl {
      unfold plus,
      rewrite m_ih,
    }
  end

-- P /\ Q  ... p * q
-- je_sodo 4 ... izjava
-- je_sodo  ... funkcija iz naravnih števil v izjave

inductive je_sodo : naravno -> Prop
| nic : je_sodo naravno.nic
| nasl_nasl {n} : je_sodo n -> je_sodo (naravno.nasl (naravno.nasl n))

#check je_sodo.nasl_nasl je_sodo.nic

lemma stiri_je_sodo : je_sodo (naravno.nasl (naravno.nasl (naravno.nasl (naravno.nasl naravno.nic)))) := begin
  apply je_sodo.nasl_nasl,
  apply je_sodo.nasl_nasl,
  apply je_sodo.nic,
end

theorem sodo_plus_sodo : forall m n, je_sodo m -> je_sodo n -> je_sodo (plus m n) :=
begin
  intros m n h_m h_n,
  induction h_m,
  case je_sodo.nic {
    unfold plus,
    assumption,
  },
  case je_sodo.nasl_nasl {
    rename h_m_n m',
    unfold plus,
    apply je_sodo.nasl_nasl,
    assumption,
  }
end

inductive manj_enako : naravno -> naravno -> Prop
| nic : forall m, manj_enako naravno.nic m
| nasl {m n} : manj_enako m n -> manj_enako (naravno.nasl m) (naravno.nasl n)

inductive manj_enako' : naravno -> naravno -> Prop
| refl : forall m, manj_enako' m m
| nasl : forall m n, manj_enako' m n -> manj_enako' m (naravno.nasl n)

theorem manj_enako_refl : forall m, manj_enako m m :=
begin
  intros,
  induction m,
  case naravno.nic {exact (manj_enako.nic naravno.nic)},
  case naravno.nasl {exact (manj_enako.nasl m_ih)},
end


theorem manj_enako_trans : forall m n, manj_enako m n -> forall p, manj_enako n p -> manj_enako m p :=
begin
  intros m n p h_m_manjse_n h_n_manjse_p,
  induction h_m_manjse_n,
  case manj_enako.nic {exact (manj_enako.nic p)},
  case manj_enako.nasl {
    rename h_m_manjse_n_m m',
    rename h_m_manjse_n_n n',
    cases h_n_manjse_p,
    rename h_n_manjse_p_n p',


  }
end

theorem manj_enako_refl' : forall m, manj_enako' m m :=
begin
  exact manj_enako'.refl
end
