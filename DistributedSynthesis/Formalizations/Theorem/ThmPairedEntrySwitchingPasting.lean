/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryWinningRun
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Pasting infinitely switching paired-entry branches

This file states the concrete witness produced by flattening an alternating
paired-entry branch and proves that such witnesses discharge the remaining
tree-run parity condition.  It deliberately contains no new automata
assumption: acceptance is that of a genuine continuation of the original
winning strategy, and the only equality requested is the usual equality
between the stored minimum state and the minimum on its finite block.

Branches that choose the wrong orientation enter the even sink and are proved
accepting separately.  Thus the model construction only has to flatten the
genuinely alternating branches.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

namespace PairedStrategyMemory

variable {A}
variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

/-- An invalid direction eventually leaves the operational tree in its even
sink forever. -/
def EventuallySink
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n ->
    atNode (A := A) initial (branchNode branch n) = .sink

/-- A direction has the orientation required by the current live paired
node. -/
def DirectionCompatible
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) : Prop :=
  match memory, direction with
  | .processOne _ _, .fromOne _ _ _ => True
  | .processTwo _ _, .fromTwo _ _ _ => True
  | _, _ => False

/-- The genuinely switching branches are precisely those whose orientation
matches at every live node. -/
def Alternates
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∀ n : Nat,
    DirectionCompatible
      (atNode (A := A) initial (branchNode branch n)) (branch n)

theorem step_eq_sink_of_not_directionCompatible
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hinvalid : ¬ DirectionCompatible memory direction) :
    memory.step (A := A) direction = .sink := by
  cases memory <;> cases direction <;>
    simp_all [DirectionCompatible, step]

/-- Every branch either alternates forever or reaches the accepting sink.
This removes invalid directions from the model-specific pasting obligation. -/
theorem eventuallySink_or_alternates
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    EventuallySink (A := A) initial branch ∨
      Alternates (A := A) initial branch := by
  classical
  by_cases halternates : Alternates (A := A) initial branch
  · exact Or.inr halternates
  · left
    simp only [Alternates] at halternates
    push Not at halternates
    rcases halternates with ⟨n, hn⟩
    have hsink :
        atNode (A := A) initial (branchNode branch (n + 1)) = .sink := by
      rw [branchNode, atNode_append]
      exact step_eq_sink_of_not_directionCompatible _ _ hn
    refine ⟨n + 1, ?_⟩
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    clear hm
    induction k with
    | zero => simpa using hsink
    | succ k ih =>
        rw [Nat.add_succ, branchNode, atNode_append, ih]
        rfl

/-- Data obtained by flattening one genuinely alternating compressed branch
to a real continuation word.  Cut `k` begins at the selected fresh entry
state, and its block ends immediately before the next fresh entry state. -/
structure SwitchingPastingWitness
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) where
  start : A.State
  word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  cuts : Nat -> Nat
  cutsStrictMono : StrictMono cuts
  cutsZero : cuts 0 = 0
  accepts : A.AcceptsFrom start word
  priority_eq_blockMin : ∀ k : Nat,
    pairedEntryPriority A
        (run (A := A) initial (branchNode branch (k + 1))) =
      cutBlockMin
        (fun n => A.priority (A.runFrom start word n)) cuts k

/-- A branch that is eventually in the even sink satisfies parity. -/
theorem switchingParity_of_eventuallySink
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hsink : EventuallySink (A := A) initial branch) :
    NatSeqMinEvenParity (fun n =>
      pairedEntryPriority A
        (run (A := A) initial (branchNode branch n))) := by
  rcases hsink with ⟨N, hN⟩
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨max n N, Nat.le_max_left _ _, ?_⟩
    simp only [run, hN _ (Nat.le_max_right _ _), toTreeState,
      pairedEntryPriority]
  · intro q hq
    exact Nat.zero_le q

/-- Parity pasting turns a genuine flattening witness into acceptance of the
compressed branch.  The root priority is harmless; after shifting it away,
the sequence is exactly the sequence of finite block minima. -/
theorem switchingParity_of_pastingWitness
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (branch : Nat -> PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (witness : SwitchingPastingWitness (A := A) initial branch) :
    NatSeqMinEvenParity (fun n =>
      pairedEntryPriority A
        (run (A := A) initial (branchNode branch n))) := by
  let realPriorities : Nat -> Nat :=
    fun n => A.priority (A.runFrom witness.start witness.word n)
  have hreal : NatSeqMinEvenParity realPriorities := by
    exact witness.accepts
  have hblocks :
      NatSeqMinEvenParity (cutBlockMin realPriorities witness.cuts) :=
    (natSeqMinEvenParity_cutBlockMin realPriorities
      witness.cutsStrictMono witness.cutsZero).mpr hreal
  let compressed : Nat -> Nat := fun n =>
    pairedEntryPriority A
      (run (A := A) initial (branchNode branch n))
  have hshift :
      (fun n => compressed (1 + n)) =
        cutBlockMin realPriorities witness.cuts := by
    funext n
    simpa [compressed, realPriorities, Nat.add_comm] using
      witness.priority_eq_blockMin n
  have hcompressedShift :
      NatSeqMinEvenParity (fun n => compressed (1 + n)) := by
    rw [hshift]
    exact hblocks
  exact (natSeqMinEvenParity_shift compressed 1).mp hcompressedShift

/-- It is enough to flatten every non-sink branch.  This is the precise
remaining branch-construction target for the unconditional reduction. -/
theorem switchingAccepts_of_sink_or_pasting
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (hbranch : ∀ branch,
      EventuallySink (A := A) initial branch ∨
        Nonempty (SwitchingPastingWitness (A := A) initial branch)) :
    initial.SwitchingAccepts (A := A) := by
  intro branch
  rcases hbranch branch with hsink | hwitness
  · exact switchingParity_of_eventuallySink initial branch hsink
  · rcases hwitness with ⟨witness⟩
    exact switchingParity_of_pastingWitness initial branch witness

/-- Equivalent consumer form: the concrete flattener is required only on
branches whose orientations alternate correctly. -/
theorem switchingAccepts_of_alternating_pasting
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (hflatten : ∀ branch,
      Alternates (A := A) initial branch ->
        Nonempty (SwitchingPastingWitness (A := A) initial branch)) :
    initial.SwitchingAccepts (A := A) := by
  apply switchingAccepts_of_sink_or_pasting initial
  intro branch
  rcases eventuallySink_or_alternates initial branch with hsink | halternates
  · exact Or.inl hsink
  · exact Or.inr (hflatten branch halternates)

/-- Complete Bérard handoff once the concrete branch flattener is supplied.
The local infinite-block case has already been derived from `hwin`. -/
theorem hasRationalRun_of_winning_and_pasting
    [Inhabited In₁] [Inhabited In₂]
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy)
    (basis :
      (pairedEntryRunAutomaton A initial.toTreeState).RationalRunBasis)
    (hbranch : ∀ branch,
      EventuallySink (A := A) initial branch ∨
        Nonempty (SwitchingPastingWitness (A := A) initial branch)) :
    (pairedEntryRunAutomaton A initial.toTreeState).HasRationalRun :=
  initial.hasRationalRun_of_winning (A := A) hwin basis
    (switchingAccepts_of_sink_or_pasting initial hbranch)

/-- Final form used by the concrete construction: flatten every correctly
alternating branch, and all other directions are handled automatically. -/
theorem hasRationalRun_of_winning_and_alternating_pasting
    [Inhabited In₁] [Inhabited In₂]
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy)
    (basis :
      (pairedEntryRunAutomaton A initial.toTreeState).RationalRunBasis)
    (hflatten : ∀ branch,
      Alternates (A := A) initial branch ->
        Nonempty (SwitchingPastingWitness (A := A) initial branch)) :
    (pairedEntryRunAutomaton A initial.toTreeState).HasRationalRun :=
  initial.hasRationalRun_of_winning (A := A) hwin basis
    (switchingAccepts_of_alternating_pasting initial hflatten)

end PairedStrategyMemory

end DetParityAutomaton

end DistributedSynthesis
