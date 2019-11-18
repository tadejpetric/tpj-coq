-- ==================== Syntax ====================

def loc := string


inductive aexp : Type
| Lookup : loc -> aexp
| Int : int -> aexp
| Plus : aexp -> aexp -> aexp
| Minus : aexp -> aexp -> aexp
| Times : aexp -> aexp -> aexp


inductive bexp : Type
| Bool : bool -> bexp
| Equal : aexp -> aexp -> bexp
| Less : aexp -> aexp -> bexp


inductive cmd : Type
| Assign : loc -> aexp -> cmd
| IfThenElse : bexp -> cmd -> cmd -> cmd 
| Seq : cmd -> cmd -> cmd 
| Skip : cmd 
| WhileDo : bexp -> cmd -> cmd 

-- ================== Example 'fact.imp' in LEAN notation. ==================

def fact : cmd :=
  cmd.Seq
    (cmd.Seq
      (cmd.Assign "n" (aexp.Int 10))
      (cmd.Assign "fact" (aexp.Int 1)) )
    (cmd.WhileDo
      (bexp.Less (aexp.Int 0) (aexp.Lookup "n"))
      (cmd.Seq
        (cmd.Assign "fact" 
          (aexp.Times (aexp.Lookup "fact") (aexp.Lookup "n")) )
        (cmd.Assign "n"
          (aexp.Minus (aexp.Lookup "n") (aexp.Int 1)) ) ) )

-- ==================== Environment ====================

inductive env : Type
| Nil : env
| Cons : loc -> int -> env -> env


inductive lookup : loc -> env -> int -> Prop
| Find {loc i E} : 
    lookup loc (env.Cons loc i E) i 
| Search {loc loc' i' E' i} : 
    loc≠loc' -> lookup loc E' i -> 
    lookup loc (env.Cons loc' i' E') i

-- ==================== Operational Semantics ====================

inductive aeval : env -> aexp -> int -> Prop
| Lookup {E loc i} :
    lookup loc E i -> 
    aeval E (aexp.Lookup loc) i
| Int {E i}:
    aeval E (aexp.Int i) i
| Plus {E a1 i1 a2 i2}:
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Plus a1 a2) (i1 + i2)
| Minus {E a1 i1 a2 i2}:
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Minus a1 a2) (i1 - i2)
| Times {E a1 i1 a2 i2}:
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Times a1 a2) (i1 * i2)


-- Lean works best with '<' and '≤' so we use them instead of '>' and '≥'.
inductive beval : env -> bexp -> bool -> Prop
| Bool {E b} :
    beval E (bexp.Bool b) b
| Equal_t {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 = i2 ->
    beval E (bexp.Equal a1 a2) true
| Equal_f {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 ≠ i2 ->
    beval E (bexp.Equal a1 a2) false
| Less_t {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 < i2 ->
    beval E (bexp.Less a1 a2) true
| Less_f {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> ¬ i1 < i2 ->
    beval E (bexp.Less a1 a2) false


inductive ceval : env -> cmd -> env -> Prop
| Assign {E a i l}:
    aeval E a i ->
    ceval E (cmd.Assign l a) (env.Cons l i E)
| IfThenElse_t {E b c1 c2 E'} :
    beval E b true -> ceval E c1 E' ->
    ceval E (cmd.IfThenElse b c1 c2) E'
| IfThenElse_f {E b c1 c2 E'} :
    beval E b false ->ceval E c2 E' ->
    ceval E (cmd.IfThenElse b c1 c2) E'
| Seq {c1 c2 E E' E''}:
    ceval E c1 E' -> ceval E' c2 E'' ->
    ceval E (cmd.Seq c1 c2) E''
| Skip {E} :
    ceval E cmd.Skip E
| WhileDo_t {E b c E' E''}:
    beval E b true -> ceval E c E' ->
    ceval E' (cmd.WhileDo b c) E'' ->
    ceval E (cmd.WhileDo b c) E''
| WhileDo_f {E b c}:
    beval E b false ->
    ceval E (cmd.WhileDo b c) E

-- ==================== Safety ====================

-- Contains all the names of already assigned locations.
inductive locs : Type
| Nil : locs
| Cons : loc -> locs -> locs


inductive loc_safe : loc -> locs -> Prop
| Find {loc L} : 
    loc_safe loc (locs.Cons loc L) 
| Search {loc loc' L} : 
    loc'≠loc -> loc_safe loc L -> 
    loc_safe loc (locs.Cons loc' L)


inductive asafe : locs -> aexp -> Prop
-- | Lookup 
-- | Int
| Plus {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Plus a1 a2)
| Minus {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Minus a1 a2)
| Times {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Times a1 a2)


inductive bsafe : locs -> bexp -> Prop
-- | Bool
-- | Equal
-- | Less

inductive csafe : locs -> cmd -> locs -> Prop
-- | Assign {L loc a} :

-- | IfThenElse SKIP THIS CONSTRUCT
-- Note: This part requires a definition of locs intersection.

-- | Seq
-- | Skip
-- | WhileDo

-- ==================== Auxiliary safety for lookup ====================

-- Ensures that the given environment maps all the required locations.
inductive env_maps : env -> locs -> Prop
| Nil {E} :
    env_maps E locs.Nil
| Cons {loc E L} :
    env_maps E L -> (∃i, lookup loc E i) ->
    env_maps E (locs.Cons loc L)


-- Increasing the environment does not break its safety.
theorem env_maps_weaken {E L loc i}:
  env_maps E L -> env_maps (env.Cons loc i E) L
:=
begin
  intro es, induction es with E' loc' E' L' maps finds ih,
  case env_maps.Nil
    { sorry },
  case env_maps.Cons
    { apply env_maps.Cons, assumption,
      -- we compare the the strings to know which lookup result is correct
      cases string.has_decidable_eq loc' loc with neq eq,
      { cases finds with i', existsi i',
        -- lookup must search deeper 
        sorry },
      existsi i, 
      -- loc' and loc are equal, 'subst eq' will rewrite them to the same name.
      sorry,
end


-- If the location is safe in the same specification as the environment
-- then we are guaranteed to look up a value
theorem safe_lookup {L E loc}:
  loc_safe loc L -> env_maps E L -> ∃ (i:int), lookup loc E i
:=
begin
  -- if we have an impossible hypothesis 'h' (such as a safety check in
  -- an empty locs list) we can complete the proof with 'cases h'
  sorry
end

-- ==================== Safety theorems ====================

theorem asafety {L E a}:
  asafe L a -> env_maps E L -> ∃ (i:int), aeval E a i
:=
begin
  intros s es,
  induction s,
  case asafe.Lookup
    { cases safe_lookup s_a es with i, 
    -- cases safe_lookup ... applies the theorem and eliminates the ∃ 
      existsi i, apply aeval.Lookup, assumption, },
  case asafe.Int
    { sorry },
  case asafe.Plus
    { cases s_ih_a es with i1,
      cases s_ih_a_1 es with i2,
      sorry },
  case asafe.Minus
    { sorry },
  case asafe.Times
    { sorry },
end


theorem bsafety {L E b}:
  bsafe L b -> env_maps E L -> ∃ (v:bool), beval E b v
:=
begin
  intros s es,
  induction s,
  case bsafe.Bool
    { existsi s_b, apply beval.Bool, },
  case bsafe.Equal
    { cases asafety s_a es with i1,
      cases asafety s_a_1 es with i2,
      cases int.decidable_eq i1 i2 with neq eq,
      -- we cannot just do a case analysis on logical formulas because
      -- we are not using classical logic. Luckily integer equality is
      -- decidable, so we can specify to do a case analysis on that
      -- i1 ≠ i2
      { sorry },
      -- i1 = i2
      { sorry }, },
  case bsafe.Less
    { sorry,
      cases int.decidable_lt i1 i2 with neq eq,
      -- i1 ≰ i2
      { sorry },
      -- i1 < i2
      { sorry }, },
end


theorem csafety {L L' E c }:
  csafe L c L' -> env_maps E L -> ∃ (E':env), ceval E c E' ∧ env_maps E' L'
:=
begin
  -- constructor splits ∧ into two subgoals
  intros s, revert E, -- we revert to obtain a stronger induction
  induction s; intros E es,
  case csafe.Assign
    { cases asafety s_a_1 es with i,
      existsi (env.Cons s_loc i E),
      constructor, -- constructor splits ∧ into two subgoals
      { sorry },
      sorry },
  case csafe.Seq
    { sorry },
  case csafe.Skip
    { sorry },
  case csafe.WhileDo
    { -- this part can't really be done in big step semantics
      sorry },
end