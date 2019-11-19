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
| Greater : aexp -> aexp -> bexp


inductive cmd : Type
| Assign : loc -> aexp -> cmd
| IfThenElse  : bexp -> cmd -> cmd -> cmd
| Seq : cmd -> cmd -> cmd
| Skip : cmd
| WhileDo : bexp -> cmd -> cmd

-- ================== Example 'fact.imp' in LEAN notation. ==================

def fact : cmd :=
  cmd.Seq
    (cmd.Seq
      (cmd.Assign "n" (aexp.Int 10))
      (cmd.Assign "fact" (aexp.Int 10)) )
    (cmd.WhileDo
      (bexp.Greater
        (aexp.Lookup "n")
        (aexp.Int 0) )
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
| Int {E i} :
    aeval E (aexp.Int i) i
| Plus {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Plus a1 a2) (i1 + i2)
| Minus {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Minus a1 a2) (i1 - i2)
| Times {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Times a1 a2) (i1 * i2)


-- Lean works best with '<' and '≤' so we use them to encode '>' and '≥'.
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
| Greater_t {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> ¬ i1 ≤ i2 ->
    beval E (bexp.Greater a1 a2) true
| Greater_f {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 ≤ i2 ->
    beval E (bexp.Greater a1 a2) false


inductive ceval : env -> cmd -> env -> Prop
| Assign {loc a i E} :
    aeval E a i ->
    ceval E (cmd.Assign loc a) (env.Cons loc i E)
| IfThenElse_t {E b c1 c2 M'} :
    beval E b true -> ceval E c1 M' ->
    ceval E (cmd.IfThenElse b c1 c2) M'
| IfThenElse_f {E b c1 c2 E'} :
    beval E b false -> ceval E c2 E' ->
    ceval E (cmd.IfThenElse b c1 c2) E'
| Seq {E c1 E' c2 E''} :
    ceval E c1 E' -> ceval E' c2 E'' ->
    ceval E (cmd.Seq c1 c2) E''
| Skip {E} :
    ceval E cmd.Skip E
| WhileDo_t {E b c E' E''} :
    beval E b true -> ceval E c E' ->
    ceval E' (cmd.WhileDo b c) E'' ->
    ceval E (cmd.WhileDo b c) E''
| WhileDo_f {E b c} :
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
| Lookup {L loc}:
    loc_safe loc L -> asafe L (aexp.Lookup loc)
| Int {L i}:
    asafe L (aexp.Int i)
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
| Bool {L b} :
    bsafe L (bexp.Bool b)
| Equal {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Equal a1 a2)
| Less {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Less a1 a2)
| Greater {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Greater a1 a2)


inductive csafe : locs -> cmd -> locs -> Prop
| Assign {L loc a} :
    asafe L a ->
    csafe L (cmd.Assign loc a) (locs.Cons loc L)
-- | IfThenElse {L b c1 c2} :
--     bsafe L b -> csafe L c1 L' -> csafe L c2 L'' ->
-- Note: This part requires a definition of locs intersection. 
| Seq {L c1 L' c2 L''} :
    csafe L c1 L' -> csafe L' c2 L'' ->
    csafe L (cmd.Seq c1 c2) L''
| Skip {L} :
    csafe L cmd.Skip L
| WhileDo {L b c L'} :
    bsafe L b -> csafe L c L' ->
    csafe L (cmd.WhileDo b c) L'

-- ==================== Auxiliary safety for lookup ====================

-- Proves that the given environment maps all the required locations.
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
  apply env_maps.Nil,
  apply env_maps.Cons, assumption,
  -- we compare the the strings to know which lookup result is correct
  cases string.has_decidable_eq loc' loc with neq eq,
  { cases finds with i', existsi i',
    apply lookup.Search, assumption, assumption, },
  existsi i, subst eq, apply lookup.Find,
end


-- If the location is safe in the same specification as the environment
-- then we are guaranteed to look up a value
theorem safe_lookup {L E loc}:
  loc_safe loc L -> env_maps E L -> ∃ (i:int), lookup loc E i
:=
begin
  intros sloc es, 
  induction es with E' loc' E' L' maps finds ih,
  { cases sloc, },
  cases sloc, assumption, apply ih, assumption,
end

-- ==================== Safety theorems ====================

theorem asafety {L E a}:
  asafe L a -> env_maps E L -> ∃ (i:int), aeval E a i
:=
begin
  intros s es,
  induction s,
  case asafe.Lookup
    { cases safe_lookup s_a es,
      existsi w, apply aeval.Lookup, assumption, },
  case asafe.Int
    { existsi s_i, apply aeval.Int, },
  case asafe.Plus
    { cases s_ih_a es with i1,
      cases s_ih_a_1 es with i2,
      existsi (i1+i2), apply aeval.Plus, 
      assumption, assumption },
  case asafe.Minus
    { cases s_ih_a es with i1,
      cases s_ih_a_1 es with i2,
      existsi (i1-i2), apply aeval.Minus, 
      assumption, assumption },
  case asafe.Times
    { cases s_ih_a es with i1,
      cases s_ih_a_1 es with i2,
      existsi (i1*i2), apply aeval.Times, 
      assumption, assumption },
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
      -- i1 ≠ i2
      { existsi (false:bool), apply beval.Equal_f,
        assumption, assumption, assumption,},
      -- i1 = i2
      { existsi (true:bool), apply beval.Equal_t,
        assumption, assumption, assumption,}, },
  case bsafe.Less
    { cases asafety s_a es with i1,
      cases asafety s_a_1 es with i2,
      cases int.decidable_lt i1 i2 with neq eq,
      -- i1 ≰ i2
      { existsi (false:bool), apply beval.Less_f,
        assumption, assumption, assumption,},
      -- i1 < i2
      { existsi (true:bool), apply beval.Less_t,
        assumption, assumption, assumption,}, },
  case bsafe.Greater
    { cases asafety s_a es with i1,
      cases asafety s_a_1 es with i2,
      cases int.decidable_le i1 i2 with neq eq,
      -- i > i2
      { existsi (true:bool), apply beval.Greater_t,
        assumption, assumption, assumption,},
      -- i ≱ i2
      { existsi (false:bool), apply beval.Greater_f,
        assumption, assumption, assumption,}, },
end


theorem csafety {L L' E c }:
  csafe L c L' -> env_maps E L -> ∃ (E':env), ceval E c E' ∧ env_maps E' L'
:=
begin
  intros s, revert E,
  induction s; intros E es,
  case csafe.Assign
    { cases asafety s_a_1 es with i,
      existsi (env.Cons s_loc i E),
      constructor,
      { apply ceval.Assign, assumption, },
      apply env_maps.Cons,
      { apply env_maps_weaken, assumption, },
      existsi i, apply lookup.Find, },
  case csafe.Seq
    { cases (s_ih_a es) with E',
      destruct h, intros c1s es',
      cases (s_ih_a_1 es') with E'',
      destruct h_1, intros c2s es'',
      existsi E'', constructor,
      { apply ceval.Seq, assumption, assumption, },
      assumption, },
  case csafe.Skip
    { existsi E, constructor, apply ceval.Skip, assumption, },
  case csafe.WhileDo
    { 
      -- this part can't really be done in big step semantics
      cases (s_ih es) with E',
      destruct h, intros csafe es',
      cases bsafety s_a es,
      cases w,
      { existsi E, constructor,
        apply ceval.WhileDo_f,
        assumption, sorry, },
      { existsi E', constructor,
        apply ceval.WhileDo_t,
        assumption, assumption, 
        sorry, sorry, } 
      },
end