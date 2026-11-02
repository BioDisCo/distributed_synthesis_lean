/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentKeys

/-!
# The shared tail table below an exact guarded hybrid root

The simultaneous and strict interpretations of the first ambiguous round are
different sibling states.  They must not be identified.  What they share is
the transition table of the one root-pinned policy: after the root bit has
been consumed, every later transition calls the same false-state successor
function.

This file packages that function without constructing a fresh
`ordinaryBelow` policy for either sibling.  It also proves that the fresh bit
stays false at every successor of a reachable false state.  Thus the guarded
phase is consumed exactly once and cannot recursively accumulate.
-/

namespace DistributedSynthesis

universe u v x y s

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

/-! ## One table below every guarded child -/

/-- The common tail transition table of the selected root-pinned policy.
The argument is the underlying ordinary state; the one-shot root bit is
inserted as `false` before consulting the guarded table and discarded again
afterwards. -/
noncomputable def profiledRawJointHybridInitialRootPinnedTailSuccessor
    (first : In₁ × In₂)
    (state :
      (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy
        first).State)
    (childCode : ProfiledRawJointHybridCode A) :
    (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy
      first).State :=
  ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
    ).policy.successor (false, state) childCode).2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every successor of a reachable false-bit state still has its fresh bit
cleared.  The proof uses reachability in the single guarded run; no semantic
identification of sibling children is required. -/
theorem profiledRawJointHybridInitialRootPinned_successor_fresh_false
    (first : In₁ × In₂)
    (state : ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy
      first)
    (hreachable :
      ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin first
        state)
    (hfresh : state.1 = false)
    (childCode : ProfiledRawJointHybridCode A) :
    ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor state childCode).1 = false := by
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  rcases hreachable with ⟨node, hnode⟩
  cases node with
  | nil =>
      have hroot : package.policy.run [] =
          (true,
            (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy
              first).initial) :=
        package.policy.accepts.1.1
      have htrue : state.1 = true := by
        rw [← hnode, hroot]
      rw [htrue] at hfresh
      contradiction
  | cons head tail =>
      have hchild := package.policy.successor_at (head :: tail) childCode
      have hbelow :=
        InputFreeRunParityTreeAutomaton.rootGuardedPolicy_fresh_false
        (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy first)
        (sourceFreeBeliefCodeParityRootAllowed
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
          (ProfiledRawJointHybridProvenanceValid A strategy)
          (profiledRawJointHybridFiniteCodeNext A)
          (profiledRawJointHybridInitialExactRootPredicate A strategy first))
        package.policy head (tail ++ [childCode])
      rw [hnode] at hchild
      rw [hchild]
      simpa [List.append_assoc] using hbelow

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At every reachable false-bit state, the complete guarded successor is
the false tag paired with the one shared tail-table result. -/
theorem profiledRawJointHybridInitialRootPinned_successor_eq_tail
    (first : In₁ × In₂)
    (state : ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy
      first)
    (hreachable :
      ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin first
        state)
    (hfresh : state.1 = false)
    (childCode : ProfiledRawJointHybridCode A) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor state childCode =
      (false,
        profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin
          first state.2 childCode) := by
  have hstate : state = (false, state.2) := by
    apply Prod.ext
    · exact hfresh
    · rfl
  apply Prod.ext
  · exact profiledRawJointHybridInitialRootPinned_successor_fresh_false
      A strategy hwin first state hreachable hfresh childCode
  · rw [hstate]
    rfl

/-! ## Both sibling kinds use that same table -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem
    ProfiledRawJointHybridInitialRootPinnedFalseCommonKey.successor_eq_tail
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first)
    (childCode : ProfiledRawJointHybridCode A) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state childCode =
      (false,
        profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin
          first key.state.2 childCode) :=
  profiledRawJointHybridInitialRootPinned_successor_eq_tail A strategy hwin
    first key.state key.reachable key.fresh_false childCode

theorem
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey.successor_eq_tail
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first)
    (childCode : ProfiledRawJointHybridCode A) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state childCode =
      (false,
        profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin
          first key.state.2 childCode) :=
  profiledRawJointHybridInitialRootPinned_successor_eq_tail A strategy hwin
    first key.state key.reachable key.fresh_false childCode

/-- The exact simultaneous and strict siblings are different states but both
advance through the same named tail function, and both remain below the
guard. -/
theorem profiledRawJointHybridInitialRootPinned_siblings_share_tail
    (first current : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (childCode : ProfiledRawJointHybridCode A) :
    let common := profiledRawJointHybridInitialRootPinnedSimultaneousKey A
      strategy hwin first current
    let strict := profiledRawJointHybridInitialRootPinnedStrictKey A strategy
      hwin first actual
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.successor common.state childCode =
      (false,
        profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin
          first common.state.2 childCode) ∧
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.successor strict.state childCode =
      (false,
        profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin
          first strict.state.2 childCode) := by
  dsimp only
  constructor
  · exact
      ProfiledRawJointHybridInitialRootPinnedFalseCommonKey.successor_eq_tail
        (A := A) (strategy := strategy) (hwin := hwin) (first := first)
        (key := profiledRawJointHybridInitialRootPinnedSimultaneousKey A
          strategy hwin first current) childCode
  · exact
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey.successor_eq_tail
        (A := A) (strategy := strategy) (hwin := hwin) (first := first)
        (key := profiledRawJointHybridInitialRootPinnedStrictKey A strategy
          hwin first actual) childCode

end

end

end DetParityAutomaton

end DistributedSynthesis
