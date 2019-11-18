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

def join {A} : list A -> list A -> list A := sorry

notation xs `++` ys := join xs ys

theorem join_nil {A} (xs: list A) :
  xs ++ [] = xs 
:=
begin
  sorry
end

end list
-------------------------------------------------------------------------------

-- Podobno kot za sezname, napišite tip za drevesa in dokažite trditve iz 
-- vaj 3. Če po definiciji tipa `tree` odprete `namespace tree` lahko
-- uporabljate konstruktorje brez predpone, torej `Empty` namesto
-- `tree.Empty`.

end hidden