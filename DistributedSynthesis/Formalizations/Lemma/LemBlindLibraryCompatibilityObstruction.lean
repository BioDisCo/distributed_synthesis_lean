/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlindLibraryParitySynthesis

/-!
# Blind compatibility can have infinite index

For Boolean streams committed as blind continuations, the safety objective
requiring equal outputs admits a joint prescription tree exactly when the
streams are equal. Thus finite independent contextual profiles cannot preserve
all accepting-tree tests. This is not an obstruction to replacing both streams
jointly by a finite winner.
-/

namespace DistributedSynthesis.BlindLibraryCompatibilityObstruction

open BlindControllerLibrary

abbrev Env := EnvironmentRound Unit Unit
abbrev Word := Nat → Bool

def equalityObjective : DetParityAutomaton (RoundRecord Unit Unit Graph Bool Bool) where
  State := Bool
  stateFinite := inferInstance
  initial := true
  step := fun q r ↦ q && decide (r.outputOne = r.outputTwo)
  priority := fun q ↦ if q then 0 else 1

def event (g : Graph) : Env := ⟨(), (), g⟩

variable (L : BlindControllerLibrary Unit Unit Bool Bool)

def blindOne (b : L.OneControl) : Nat → Bool
  | 0 => (L.noRecvOne b ()).2
  | n + 1 => blindOne (L.noRecvOne b ()).1 n

def blindTwo (b : L.TwoControl) : Nat → Bool
  | 0 => (L.noRecvTwo b ()).2
  | n + 1 => blindTwo (L.noRecvTwo b ()).1 n

/-- The three children give a triangle of equalities. In particular, receive
resets do not remove the constraint on the two current blind continuations. -/
theorem blind_equal_of_safe
    (tree : LabeledTree Env L.Move) (run : List Env → L.State equalityObjective)
    (hstep : ∀ node e, run (node ++ [e]) = L.next equalityObjective (run node) (tree node) e)
    (hsafe : ∀ node e, (L.record equalityObjective (run node) (tree node) e).outputOne =
      (L.record equalityObjective (run node) (tree node) e).outputTwo) :
    ∀ n node, blindOne L (run node).1.1 n = blindTwo L (run node).1.2 n := by
  intro n
  induction n with
  | zero =>
    intro node
    have hl := hsafe node (event .left)
    have hr := hsafe node (event .right)
    have hb := hsafe node (event .both)
    simp only [record, responses, event] at hl hr hb
    exact hr.trans (hb.symm.trans hl)
  | succ n ih =>
    intro node
    have hl := ih (node ++ [event .left])
    have hr := ih (node ++ [event .right])
    have hb := ih (node ++ [event .both])
    rw [hstep] at hl hr hb
    simp only [next, responses, event] at hl hr hb
    exact hr.trans (hb.symm.trans hl)

private def extend (node : List Env) : Nat → Env :=
  fun n ↦ node.getD n (event .both)

private theorem extend_prefix (node : List Env) : ∀ n, n ≤ node.length →
    branchNode (extend node) n = node.take n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [show branchNode (extend node) (n + 1) =
      branchNode (extend node) n ++ [node.getD n (event .both)] from rfl,
      ih (by omega), List.getD_eq_getElem node (event .both) (by omega),
      List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl

theorem safe_of_accepting_run
    (tree : LabeledTree Env L.Move) (run : List Env → L.State equalityObjective)
    (hstep : ∀ node e, run (node ++ [e]) = L.next equalityObjective (run node) (tree node) e)
    (hparity : ∀ env, NatSeqMinEvenParity
      (fun n ↦ equalityObjective.priority (run (branchNode env n)).2)) :
    ∀ node e, (L.record equalityObjective (run node) (tree node) e).outputOne =
      (L.record equalityObjective (run node) (tree node) e).outputTwo := by
  have htrue : ∀ node, (run node).2 = true := by
    intro node
    by_contra hn
    have hf : (run node).2 = false := Bool.eq_false_iff.mpr hn
    have hprefix : branchNode (extend node) node.length = node := by
      rw [extend_prefix node _ (Nat.le_refl _), List.take_length]
    have hpersist : ∀ k, (run (branchNode (extend node) (node.length + k))).2 = false := by
      intro k
      induction k with
      | zero => simpa only [Nat.add_zero, hprefix] using hf
      | succ k ih =>
        change (run (branchNode (extend node) (node.length + k) ++
          [extend node (node.length + k)])).2 = false
        rw [hstep]
        change ((run (branchNode (extend node) (node.length + k))).2 && _) = false
        rw [ih]
        rfl
    apply not_natSeqMinEvenParity_of_eventually_one _ node.length _ (hparity (extend node))
    intro n hn
    have hp := hpersist (n - node.length)
    rw [Nat.add_sub_of_le hn] at hp
    simp [equalityObjective, hp]
  intro node e
  have ht := htrue (node ++ [e])
  rw [hstep] at ht
  change ((run node).2 && decide (_ = _)) = true at ht
  rw [htrue node, Bool.true_and] at ht
  exact of_decide_eq_true ht

theorem initial_blind_equal (h : L.HasAcceptingTree equalityObjective) :
    ∀ n, blindOne L L.initialOne n = blindTwo L L.initialTwo n := by
  obtain ⟨tree, run, ⟨hinit, hstep⟩, hparity⟩ := h
  intro n
  have heq := blind_equal_of_safe L tree run hstep
    (safe_of_accepting_run L tree run hstep hparity) n []
  simpa only [hinit, initial] using heq

def shift (f : Word) (k : Nat) : Word := fun n ↦ f (k + n)

def wordLibrary (f g : Word) : BlindControllerLibrary Unit Unit Bool Bool where
  OneControl := Word
  TwoControl := Word
  initialOne := f
  initialTwo := g
  noRecvOne := fun w _ ↦ (shift w 1, w 0)
  noRecvTwo := fun w _ ↦ (shift w 1, w 0)

private theorem blindOne_word (f g w : Word) (n : Nat) :
    blindOne (wordLibrary f g) w n = w n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    change blindOne (wordLibrary f g) (shift w 1) n = w (n + 1)
    rw [ih]
    simp [shift, Nat.add_comm]

private theorem blindTwo_word (f g w : Word) (n : Nat) :
    blindTwo (wordLibrary f g) w n = w n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    change blindTwo (wordLibrary f g) (shift w 1) n = w (n + 1)
    rw [ih]
    simp [shift, Nat.add_comm]

theorem same_word_accepting (f : Word) :
    (wordLibrary f f).HasAcceptingTree equalityObjective := by
  let tree : LabeledTree Env (wordLibrary f f).Move := fun node _ _ ↦
    ((shift f (node.length + 1), f node.length),
      (shift f (node.length + 1), f node.length))
  let run : List Env → (wordLibrary f f).State equalityObjective :=
    fun node ↦ ((shift f node.length, shift f node.length), true)
  refine ⟨tree, run, ⟨?_, ?_⟩, ?_⟩
  · change ((shift f 0, shift f 0), true) = ((f, f), true)
    have hz : shift f 0 = f := by
      funext n
      exact congrArg f (Nat.zero_add n)
    rw [hz]
  · intro node e
    have hshift : shift (shift f node.length) 1 = shift f (node.length + 1) := by
      funext n
      simp [shift, Nat.add_assoc]
    cases hg : e.graph <;>
      simp [run, tree, next, record, responses, hg, wordLibrary,
        equalityObjective, hshift, shift]
  · intro env
    refine ⟨0, ⟨0, rfl⟩, ?_, fun q _ ↦ Nat.zero_le q⟩
    intro n
    exact ⟨n, Nat.le_refl n, rfl⟩

/-- Exact compatibility already has infinitely many distinct sections for a
two-state safety objective and singleton input alphabets. -/
theorem accepting_iff_eq (f g : Word) :
    (wordLibrary f g).HasAcceptingTree equalityObjective ↔ f = g := by
  constructor
  · intro h
    funext n
    have hn := initial_blind_equal (wordLibrary f g) h n
    change blindOne (wordLibrary f g) f n = blindTwo (wordLibrary f g) g n at hn
    simpa only [blindOne_word, blindTwo_word] using hn
  · rintro rfl
    exact same_word_accepting f

def pulse (k : Nat) : Word := fun n ↦ decide (n = k)

/-- Even allowing different profiles on the two sides cannot give a finite
exact contextual quotient. Only the first profile's codomain is assumed finite. -/
theorem no_finite_independent_profiles (T₁ T₂ : Type*) [Finite T₁]
    (one : Word → T₁) (two : Word → T₂) (compatible : T₁ → T₂ → Prop) :
    ¬ (∀ f g, (wordLibrary f g).HasAcceptingTree equalityObjective ↔
      compatible (one f) (two g)) := by
  intro hexact
  obtain ⟨k, l, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k ↦ one (pulse k))
  have hself := (hexact (pulse l) (pulse l)).mp (same_word_accepting (pulse l))
  rw [← heq] at hself
  have hequal := (accepting_iff_eq (pulse k) (pulse l)).mp
    ((hexact (pulse k) (pulse l)).mpr hself)
  have hvalue := congrFun hequal k
  simp [pulse, hne] at hvalue

end DistributedSynthesis.BlindLibraryCompatibilityObstruction
