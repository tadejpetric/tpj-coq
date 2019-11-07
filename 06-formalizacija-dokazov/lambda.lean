inductive ty : Type
| unit : ty
| bool : ty
| arrow : ty -> ty -> ty

def nm := string

inductive tm : Type
| var : nm -> tm
| unit : tm
| true : tm
| false : tm
| app : tm -> tm -> tm
| lam : nm -> tm -> tm
| if_then_else : tm -> tm -> tm -> tm

inductive value : tm -> Prop
| unit : value tm.unit
| true : value tm.true
| false : value tm.false
| lam {x : nm} {N : tm} : value (tm.lam x N)

def subst (x : nm) (M : tm) : tm -> tm
| (tm.var y) := if x = y then M else tm.var y
| tm.unit := tm.unit
| tm.true := tm.true
| tm.false := tm.false
| (tm.app N1 N2) := tm.app (subst N1) (subst N2)
| (tm.lam y N) := if x = y then tm.lam y N else tm.lam y (subst N)
| (tm.if_then_else N N1 N2) := tm.if_then_else (subst N) (subst N1) (subst N2)

inductive step : tm -> tm -> Prop
| step1 {M M' N : tm} : step M M' -> step (tm.app M N) (tm.app M' N)
| step2 {V N N' : tm} : value V -> step N N' -> step (tm.app V N) (tm.app V N')
| beta {x} {M V : tm} : value V -> step (tm.app (tm.lam x M) V) (subst x V M)
| test {M M' N1 N2 : tm} : step M M' -> step (tm.if_then_else M N1 N2) (tm.if_then_else M' N1 N2)
| true {N1 N2 : tm} : step (tm.if_then_else tm.true N1 N2) N1
| false {N1 N2 : tm} : step (tm.if_then_else tm.false N1 N2) N2

inductive ctx : Type
| nil : ctx
| cons : nm -> ty -> ctx -> ctx

inductive lookup : nm -> ctx -> ty -> Prop
| here {x A Γ} : lookup x (ctx.cons x A Γ) A
| there {x y : nm} {A B : ty} {Γ : ctx} : x ≠ y -> lookup x Γ A -> lookup x (ctx.cons y B Γ) A

inductive of : ctx -> tm -> ty -> Prop
| var {x Γ A}: lookup x Γ A -> of Γ (tm.var x) A
| unit {Γ}: of Γ tm.unit ty.unit
| true {Γ}: of Γ tm.true ty.bool
| false {Γ}: of Γ tm.false ty.bool
| app {Γ M N A B} : of Γ M (ty.arrow A B) -> of Γ N A -> of Γ (tm.app M N) B
| lam {Γ x M A B} : of (ctx.cons x A Γ) M B -> of Γ (tm.lam x M) (ty.arrow A B)
| if_then_else {Γ M N1 N2 A} : of Γ M ty.bool -> of Γ N1 A -> of Γ N2 A -> of Γ (tm.if_then_else M N1 N2) A

theorem substitution (Γ x A M M' A') : of Γ M A -> of (ctx.cons x A Γ) M' A' -> of Γ (subst x M M') A' := sorry

theorem preservation (Γ M M') : step M M' -> forall A, of Γ M A -> of Γ M' A :=
begin
    intros Hstep,
    induction Hstep,
    repeat {intros A Hof},
    case step.beta
        {cases Hof, cases Hof_a, apply substitution _ _ _ _ _ _ Hof_a_1 Hof_a_a },
    case step.step1
        {cases Hof, apply of.app,
            apply Hstep_ih _ Hof_a, apply Hof_a_1},
    case step.step2
        {cases Hof, apply of.app, apply Hof_a, apply Hstep_ih _ Hof_a_1},
    case step.test {
        cases Hof,
        apply of.if_then_else,
        apply Hstep_ih _ Hof_a,
        apply Hof_a_1,
        apply Hof_a_2
    },
    case step.true {
        cases Hof,
        apply Hof_a_1
    },
    case step.false {
        cases Hof,
        apply Hof_a_2
    }
end

theorem progress (M A) : of ctx.nil M A -> (value M) ∨ (exists M', step M M') :=
begin
    generalize empty : ctx.nil = Γ,
    intros H,
    induction H,
    case of.var
        {rewrite ←empty at H_a, cases H_a},
    case of.unit
        {left, exact value.unit},
    case of.app
        {
            cases H_ih_a empty,
                case or.inl {
                    cases H_a,
                        case of.var
                            {rw ←empty at H_a_a, cases H_a_a},
                        case of.app
                            {cases h},
                        case of.lam {
                            cases H_ih_a_1 empty,
                            right,
                            existsi (subst H_a_x H_N H_a_M),
                            apply step.beta,
                            assumption,
                            right,
                            cases h_1,
                            existsi (tm.app (tm.lam H_a_x H_a_M) h_1_w),
                            eapply step.step2,
                            exact value.lam,
                            assumption
                        },
                        case of.if_then_else {
                            cases h
                        }
                },
                case or.inr {
                    cases h with M H_step,
                    right,
                    existsi (tm.app M H_N),
                    apply step.step1,
                    assumption
                }
        },
    case of.lam
        {left, exact value.lam},
    case of.true
        {left, exact value.true},
    case of.false
        {left, exact value.false},
    case of.if_then_else {
        cases H_ih_a empty,
        case or.inl {
            cases H_a,
            case of.var
                {rw ←empty at H_a_a, cases H_a_a},
            case of.true {
                right, existsi H_N1, exact step.true
            },
            case of.false {
                right, existsi H_N2, exact step.false
            },
            cases h,
            cases h
        },
        case or.inr {
            cases h,
            right,
            existsi (tm.if_then_else h_w H_N1 H_N2),
            exact (step.test h_h),
        }
    }
end

