namespace hidden
universe u

-------------------------------------------------------------------------------
inductive list (A:Type) : Type
| Nil {} : list -- Brez {} moramo konstruktorju Nil vedno podati tip A
| Cons : A -> list -> list -- Cons tip A ugotovi iz tipa prvega elementa

namespace list
-- Dopolnite definicije in dokažitve trditve za sezname iz vaj 3. Uporabljate -- lahko notacijo x :: xs, [] in ++ (namesto @), vendar bodite pozorni na
-- oklepaje.

notation x `::` xs := Cons x xs
notation `[]` := Nil

def join {A} : list A -> list A -> list A
| [] ys := ys
| (x :: xs) ys := x :: (join xs ys)

notation xs `++` ys := join xs ys

theorem join_nil {A} (xs: list A) :
  xs ++ [] = xs 
:=
begin
  induction xs,
  { unfold join, },
  unfold join, rewrite xs_ih,
end

def reverse {A} : list A -> list A
| [] := []
| (x::xs) := (reverse xs) ++ (x::[])


theorem join_assoc {A} (xs ys zs : list A) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
:=
begin
  induction xs,
  unfold join,
  unfold join, rewrite xs_ih,
end


theorem reverse_join {A} (xs ys : list A):
  reverse (xs ++ ys) = (reverse ys) ++ (reverse xs)
:=
begin
  induction xs,
  { unfold join, unfold reverse, rewrite join_nil, },
  unfold join, unfold reverse, rewrite xs_ih,
  rewrite join_assoc,
end





end list
-------------------------------------------------------------------------------

-- Podobno kot za sezname, napišite tip za drevesa in dokažite trditve iz 
-- vaj 3. Če po definiciji tipa `tree` odprete `namespace tree` lahko
-- uporabljate konstruktorje brez predpone, torej `Empty` namesto
-- `tree.Empty`.

inductive tree (A:Type) : Type
| Empty {} : tree 
| Node : tree -> A -> tree -> tree 

namespace tree

def mirror {A} : tree A -> tree A
| Empty := Empty
| (Node lt x rt) := Node (mirror rt) x (mirror lt)   
theorem mirror_mirror {A} (t : tree A) :
  mirror (mirror t) = t
:=
begin
induction t,
{ unfold mirror, },
unfold mirror, rewrite [t_ih_a, t_ih_a_1],
end

def tree_map {A B : Type} (f : A -> B) : tree A -> tree B
| Empty := Empty
| (Node lt x rt) := Node (tree_map lt) (f x) (tree_map rt)

theorem mirror_map_comm {A B} (t : tree A) (f : A -> B) :
  tree_map f (mirror t) = mirror (tree_map f t) 
:=
begin
  induction t,
  { unfold mirror, unfold tree_map, unfold mirror, },
  unfold mirror, unfold tree_map,
  rewrite [t_ih_a, t_ih_a_1],
  unfold mirror,
end

end tree

end hidden