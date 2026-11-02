/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Representatives
import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryLabelTransport
import Mathlib.Data.Set.Finite.List

/-! Finite block rules and exact replay of objective states. Equal block
types preserve every priority in the block, not just its final state. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

abbrev BlockPrefix (E : Type*) (D : Nat) := {u : List E // 0 < u.length ∧ u.length ≤ D}
abbrev BlockWord (E : Type*) (D : Nat) := {u : List E // u.length = D}

instance {E : Type*} [Finite E] (D : Nat) : Finite (BlockPrefix E D) :=
  ((List.finite_length_le E D).subset (fun _ h => h.2)).to_subtype

instance {E : Type*} [Finite E] (D : Nat) : Finite (BlockWord E D) :=
  (List.finite_length_eq E D).to_subtype

/-- Enumerate the nonempty words of length at most `D` from the given
alphabet enumeration. This instance does not use classical choice. -/
instance blockPrefix_fintype {E : Type*} [Fintype E] [DecidableEq E] (D : Nat) :
    Fintype (BlockPrefix E D) := by
  let f : (Σ n : Fin D, List.Vector E (n.val+1)) → BlockPrefix E D :=
    fun x => ⟨x.2.val, by rw [x.2.property]; omega, by rw [x.2.property]; omega⟩
  apply Fintype.ofSurjective f
  intro u
  let n : Fin D := ⟨u.val.length-1, by have := u.property; omega⟩
  exact ⟨⟨n, ⟨u.val, by have := u.property; dsimp [n]; omega⟩⟩, rfl⟩

instance blockWord_fintype {E : Type*} [Fintype E] (D : Nat) : Fintype (BlockWord E D) :=
  inferInstanceAs (Fintype (List.Vector E D))

instance envRecord_finite {I₁ I₂ : Type*} [Finite I₁] [Finite I₂] :
    Finite (RoundRecord I₁ I₂ Graph Unit Unit) := by
  let code : RoundRecord I₁ I₂ Graph Unit Unit → I₁ × I₂ × Graph :=
    fun r => (r.inputOne, r.inputTwo, r.graph)
  apply Finite.of_injective code
  intro a b eq
  cases a; cases b
  simpa [code] using eq

def envRecordEquiv (I₁ I₂ : Type*) :
    I₁ × I₂ × Graph ≃ RoundRecord I₁ I₂ Graph Unit Unit where
  toFun := fun e => ⟨e.1, e.2.1, e.2.2, (), ()⟩
  invFun := fun e => (e.inputOne, e.inputTwo, e.graph)
  left_inv := fun _ => rfl
  right_inv := by
    intro e
    cases e with
    | mk x y g a b => cases a; cases b; rfl

instance envRecord_fintype {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂] :
    Fintype (RoundRecord I₁ I₂ Graph Unit Unit) :=
  Fintype.ofEquiv _ (envRecordEquiv I₁ I₂)

instance envRecord_decidableEq {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂] :
    DecidableEq (RoundRecord I₁ I₂ Graph Unit Unit) := by
  intro a b
  apply decidable_of_iff
    ((a.inputOne, a.inputTwo, a.graph) = (b.inputOne, b.inputTwo, b.graph))
  exact (envRecordEquiv I₁ I₂).symm.injective.eq_iff

/-- Equal initial states and equal outputs at all nonempty prefixes give
equal monitor states at all prefixes, including the empty prefix. -/
theorem block_replay {E O Q : Type*} (state : List E → Q) (out : List E → O)
    (step : Q → E → O → Q)
    (update : ∀ h e, state (h++[e]) = step (state h) e (out (h++[e])))
    (D : Nat) (h k : List E) (initial : state h = state k)
    (rules : ∀ u : BlockPrefix E D, out (h++u.val) = out (k++u.val))
    (u : List E) (bound : u.length ≤ D) : state (h++u) = state (k++u) := by
  induction u using List.reverseRecOn with
  | nil => simpa using initial
  | append_singleton u e ih =>
    have oldBound : u.length ≤ D := by simp only [List.length_append, List.length_singleton] at bound; omega
    have outputs := rules ⟨u++[e], by simp, bound⟩
    simp only [← List.append_assoc] at outputs ⊢
    rw [update, update, ih oldBound, outputs]

/-- Concrete rule used by a distributed strategy on one root. -/
def strategyBlockRule {I₁ I₂ O₁ O₂ : Type} (σ : StrategyPair I₁ I₂ O₁ O₂)
    (D : Nat) (h : EnvHistory I₁ I₂) :
    BlockPrefix (RoundRecord I₁ I₂ Graph Unit Unit) D → O₁ × O₂ := fun u =>
  (σ.one (currentView .one (h++u.val)), σ.two (currentView .two (h++u.val)))

/-- For the existing strategy-monitor semantics, equality of finite block
rules really preserves the objective state reached after each prefix. -/
theorem strategy_block_replay {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (D : Nat) (h k : EnvHistory I₁ I₂)
    (initial : strategyHistoryLabel σ step q₀ h = strategyHistoryLabel σ step q₀ k)
    (rules : strategyBlockRule σ D h = strategyBlockRule σ D k)
    (u : EnvHistory I₁ I₂) (bound : List.length u ≤ D) :
    strategyHistoryLabel σ step q₀ (h++u) = strategyHistoryLabel σ step q₀ (k++u) :=
  block_replay (strategyHistoryLabel σ step q₀)
    (fun h => (σ.one (currentView .one h), σ.two (currentView .two h)))
    (fun q e y => step q (e.inputOne, e.inputTwo, e.graph) y)
    (strategyHistoryLabel_append σ step q₀) D h k initial (congrFun rules) u bound

/-- The finite block type records exactly the data used for replacement. -/
def strategyBlockType {I₁ I₂ O₁ O₂ Q G R : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) (root : R → EnvHistory I₁ I₂)
    (graphState : R → G) (objectiveState : R → Q)
    (member : R → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Bool) (i : R) :
    BlockType G Q (BlockPrefix (RoundRecord I₁ I₂ Graph Unit Unit) D) (O₁ × O₂)
      (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) :=
  ⟨graphState i, objectiveState i, strategyBlockRule σ D (root i), member i⟩

/-- Equal graph-recognizer states remain equal after the same suffix. This
holds beyond the current block as well. -/
theorem graph_recognizer_replay {I₁ I₂ G : Type*} (M : Recognizer Graph G)
    (h k u : EnvHistory I₁ I₂)
    (same : M.eval (History.graphSequence h) = M.eval (History.graphSequence k)) :
    M.eval (History.graphSequence (h++u)) = M.eval (History.graphSequence (k++u)) := by
  simpa only [History.graphSequence, List.map_append, Recognizer.eval,
    Recognizer.evalFrom, List.foldl_append] using
    congrArg (fun q => List.foldl M.step q (History.graphSequence u)) same

/-- The fold cannot change whether any future extension is live when the
type records the state of a recognizer for the live graph-prefix language. -/
theorem graph_recognizer_live_iff {I₁ I₂ G : Type*} (M : Recognizer Graph G)
    (P : List Graph → Prop) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (h k u : EnvHistory I₁ I₂)
    (same : M.eval (History.graphSequence h) = M.eval (History.graphSequence k)) :
    P (History.graphSequence (h++u)) ↔ P (History.graphSequence (k++u)) := by
  rw [recognizes, recognizes, graph_recognizer_replay M h k u same]

end Characterisation.PeriodicBlocks
