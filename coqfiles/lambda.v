From Coq Require Import Strings.String.

Module types.
  Inductive ty : Type :=
  | unit_t : ty
  | bool_t : ty
  | arrow_t : ty -> ty -> ty.
End types.

Module terms.
  Inductive tm : Type :=
  | var : string -> tm
  | unit : tm
  | true : tm
  | false : tm
  | app : tm -> tm -> tm
  | lam : string -> tm -> tm
  | if_then_else : tm -> tm -> tm -> tm.
  
  Fixpoint substitute (x : string) (e v : tm) : tm :=
    match v with
    | var y => if (string_dec x y) then e else var y
    | unit => unit
    | true => true
    | false => false
    | app f value => app (substitute x e f) (substitute x e value)
    | lam variable body => if string_dec x variable
                          then lam variable body
                          else lam variable (substitute x e body)
    | if_then_else cond passed failed =>
      if_then_else (substitute x e cond) (substitute x e passed) (substitute x e failed)
    end.
End terms.

Module val.
Inductive value : terms.tm -> Prop :=
| unit : value terms.unit
| true : value terms.true
| false : value terms.false
| lam x e : value (terms.lam x e).
End val.

Module int.
  Inductive step : terms.tm -> terms.tm -> Prop :=
    | app1 
