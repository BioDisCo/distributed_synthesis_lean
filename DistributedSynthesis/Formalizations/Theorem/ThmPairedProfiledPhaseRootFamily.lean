/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootFamilyAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOverlapInvariant

/-!
# Reifying real profiled phases as restarted family roots

This is the adapter from the semantic phase invariant to the concrete outer
family automaton.  The receiver-side phase control contains the exact monitor
state reached at the current prefix.  We retain that state in the proof-side
root descriptor; the local process receives neither the descriptor nor the
hidden Boolean family index.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- Exact restarted right root carried by a right-oriented semantic phase. -/
def profiledRightRestartRootOfPhase
    (phase : ProfiledMatchedPhase A firstBank) (hright : phase.IsRight) :
    ProfiledRightRestartRoot A := by
  cases phase with
  | firstRight owner receiver sameKey =>
      exact ⟨.inl receiver.1, receiver.2.2.1⟩
  | firstLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.IsRight] at hright
  | bankRight owner receiver sameKey =>
      exact ⟨.inr receiver.1, receiver.2.2.1⟩
  | bankLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.IsRight] at hright

/-- Exact restarted left root carried by a left-oriented semantic phase. -/
def profiledLeftRestartRootOfPhase
    (phase : ProfiledMatchedPhase A firstBank) (hleft : phase.IsLeft) :
    ProfiledLeftRestartRoot A := by
  cases phase with
  | firstRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.IsLeft] at hleft
  | firstLeft receiver owner sameKey =>
      exact ⟨.inl receiver.1, receiver.2.2.1⟩
  | bankRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.IsLeft] at hleft
  | bankLeft receiver owner sameKey =>
      exact ⟨.inr receiver.1, receiver.2.2.1⟩

/-- The proof-side Boolean enumerates the two candidates.  It is never an
input to either local process. -/
def profiledBothCandidatePhase (candidates : ProfiledBothCandidates A firstBank) :
    Bool → ProfiledMatchedPhase A firstBank
  | false => candidates.right
  | true => candidates.left

/-- Reify a same-orientation right candidate pair as the exact finite source
family consumed by one simultaneous move. -/
def profiledRightRestartRootsOfCandidates
    (candidates : ProfiledBothCandidates A firstBank)
    (hright : ∀ anchor,
      (profiledBothCandidatePhase A firstBank candidates anchor).IsRight) :
    Bool → ProfiledRightRestartRoot A :=
  fun anchor => profiledRightRestartRootOfPhase A firstBank
    (profiledBothCandidatePhase A firstBank candidates anchor) (hright anchor)

/-- Left mirror. -/
def profiledLeftRestartRootsOfCandidates
    (candidates : ProfiledBothCandidates A firstBank)
    (hleft : ∀ anchor,
      (profiledBothCandidatePhase A firstBank candidates anchor).IsLeft) :
    Bool → ProfiledLeftRestartRoot A :=
  fun anchor => profiledLeftRestartRootOfPhase A firstBank
    (profiledBothCandidatePhase A firstBank candidates anchor) (hleft anchor)

end

end


end DetParityAutomaton

end DistributedSynthesis
