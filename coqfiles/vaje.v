Module list_ex.
  Inductive list (A : Type) : Type :=
  | Nil : list A
  | Cons : A -> list A -> list A.
  
  Arguments Nil {A}.
  Arguments Cons {A} a l.
  Variable X : Type.
  
  Infix "::" := Cons (at level 60, right associativity).
  
  Fixpoint join (A B: list X) : list X:=
    match A with
    | Nil => B
    | Cons x y => x :: (join y B)
    end.
  
  Notation "[ ]" := Nil.
  Notation "[ x ; y ; .. ; z ]" := (Cons x (Cons y .. (Cons z Nil) ..)).
  Infix "++" := join.
  
  Theorem join_nil (xs: list X) : xs ++ [] = xs.
  Proof.
    induction xs.
    simpl.
    tauto.
    simpl.
    rewrite IHxs.
    tauto.
  Qed.
End list_ex.

