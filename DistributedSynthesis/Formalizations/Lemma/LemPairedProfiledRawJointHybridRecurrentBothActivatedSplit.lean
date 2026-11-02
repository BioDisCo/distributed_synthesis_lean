/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRecurrentEnvironmentRecut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridForeverCommonAcceptance

/-!
# Recurrent-both split for the activated hybrid route

Recurrent synchronization has two genuinely different positive treatments.
Either the environment is eventually all-`.both`, in which case the existing
forever-common hybrid physical word is accepted, or strict groups start
arbitrarily late, providing the productive cut stream for the activated
one-sided construction.

This file packages that split together with the exact input stream of the
all-`.both` suffix.  It makes no executable side test: the disjunction,
tail start, and strict-group witnesses are all proof-side.  To apply the
first branch to a new physical controller one still proves the ordinary
rerooted-trace equality with the displayed forever-common word.
-/

namespace DistributedSynthesis

universe u v x y s

/-- Input pairs of an environment suffix, with the graph component erased. -/
def environmentTailInputPairs
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₁ × In₂ :=
  fun n ↦ ((env (start + n)).inputOne, (env (start + n)).inputTwo)

/-- An eventually all-`.both` tail is literally the all-`.both` environment
built from its own suffix input pairs. -/
theorem EventuallyAllBoth.drop_eq_inputPairs_allBoth
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hall : EventuallyAllBoth (fun n ↦ (env n).graph)) :
    ∃ start : Nat,
      OmegaWord.drop env start = (fun n ↦
        { inputOne := (environmentTailInputPairs env start n).1
          inputTwo := (environmentTailInputPairs env start n).2
          graph := .both } : EnvironmentSequence In₁ In₂) := by
  rcases hall with ⟨start, hstart⟩
  refine ⟨start, ?_⟩
  funext n
  cases hround : env (start + n) with
  | mk inputOne inputTwo graph =>
      have hgraph : graph = .both := by
        simpa [hround] using hstart (start + n) (Nat.le_add_right start n)
      subst graph
      simp [OmegaWord.drop, environmentTailInputPairs, hround]

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reusable activated-route split.  The left branch gives both the exact
all-`.both` suffix and the already verified accepted hybrid physical word on
its input stream.  The right branch gives recurrent strict gaps and their
strict-group starts. -/
theorem graphBothRecurrent_hybridForeverCommon_or_strictGaps
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    (∃ start : Nat,
      (OmegaWord.drop env start = (fun n ↦
          { inputOne := (environmentTailInputPairs env start n).1
            inputTwo := (environmentTailInputPairs env start n).2
            graph := .both } : EnvironmentSequence In₁ In₂)) ∧
      A.Accepts
        (profiledRawJointHybridForeverCommonPhysicalWord A strategy hwin
          (environmentTailInputPairs env start))) ∨
      (GraphStrictRecurrent (fun n ↦ (env n).graph) ∧
        StrictGroupStartsRecurrent (fun n ↦ (env n).graph)) := by
  rcases graphBothRecurrent_split (fun n ↦ (env n).graph) hboth with
      hall | hstrict
  · left
    obtain ⟨start, hdrop⟩ := hall.drop_eq_inputPairs_allBoth env
    refine ⟨start, hdrop, ?_⟩
    exact profiledRawJointHybridForeverCommonPhysicalWord_accepts A strategy
      hwin (environmentTailInputPairs env start)
  · exact Or.inr hstrict

end

end DetParityAutomaton

end DistributedSynthesis
