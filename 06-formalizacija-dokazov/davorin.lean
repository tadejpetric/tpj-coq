inductive natu : Type
| Zer : natu
| Suc : natu -> natu 

#check natu.rec 

theorem t1 : ∀ p q r : Prop, (p->(q->r)) ↔ (p ∧ q) -> r :=
begin
    intros,
    apply iff.intro,
    {
        intros,
        apply a,
        cases a_1,
        assumption,
        cases a_1,
        assumption,
    },
    {
        intros,
        apply a,
        show p ∧ q, from and.intro a_1 a_2,
    }
end

theorem t2 : ∀ p, ¬ ¬ ¬ p ↔ ¬ p :=
begin
intros,
apply iff.intro,
{
    intros,
    apply not.intro,
    intros,
    apply a,
    apply not.intro,
    intros,
    apply a_2,
    assumption,
},
{
    intros,
    apply not.intro,
    intros,
    apply a_1,
    assumption,
}
end

theorem demorgan_l : ∀ p q, ¬ p ∧ ¬ q ↔ ¬ (p ∨ q) :=
begin
intros,
apply iff.intro,
{
    intros,
    cases a,
    apply not.intro,
    intros,
    cases a,
    {
        apply a_left,
        assumption,
    },
    {
        apply a_right,
        assumption,
    }
},
{
    intros,
    apply and.intro,
    {
        apply not.intro,
        intros,
        apply a,
        apply or.intro_left,
        assumption,
    },
    {
        apply not.intro,
        intros,
        apply a,
        apply or.intro_right,
        assumption,
    }
}
end

theorem demorgan_2 : ∀ p q, ¬ p ∨ ¬ q → ¬ (p ∧ q) :=
begin
intros,
apply not.intro,
intros,
cases a_1,
{
    cases a,
    {
        apply a,
        assumption,
    },
    {
        apply a,
        assumption,
    }
}
end

theorem t3 : ∀ p q, ¬¬ (p ∧ q) ↔ ¬¬ p ∧ ¬¬ q :=
begin
intros,
apply iff.intro,
{
    intros,
    apply and.intro,
    {
        apply not.intro,
        intros,
        apply a,
        apply not.intro,
        intros,
        cases a_2,
        apply a_1,
        assumption,
    },
    {
        apply not.intro,
        intros,
        apply a,
        apply not.intro,
        intros,
        cases a_2,
        apply a_1,
        exact a_2_right,
    }
},
{
    intros,
    apply not.intro,
    intros,
    cases a,
    apply a_1,
    have both : ¬¬ p ∨ ¬¬ q,
    {
        apply or.intro_left,
        assumption,
    },
    have dmo : ¬ (¬p ∧ ¬ q),
    {
        apply demorgan_2,
        assumption,
    },
    exfalso,
    apply dmo,
    apply and.intro,
    {
        apply not.intro,
        intros,
        have a_1_impl : (p ∧ q) -> false,
        {
            apply a_1,
        },
        have qtf : q → false,
        {
            intros,
            apply a_1_impl,
            exact and.intro a a_2,
        },
        have dumb : (q -> false) -> false,
        {
            apply a_right,
        },
        apply dumb,
        apply qtf,
    },
    {
        apply not.intro,
        intros,
        have a_1_impl : (p ∧ q) -> false,
        {
            apply a_1,
        },
        have qtf : p → false,
        {
            intros,
            apply a_1_impl,
            exact and.intro a_2 a,
        },
        have dumb : (p -> false) -> false,
        {
            apply a_left,
        },
        apply dumb,
        apply qtf,
    }
}
end