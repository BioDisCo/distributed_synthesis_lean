/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialRootPinnedPolicy

/-!
# Persistent keys in the exact root-guarded hybrid policy

At the first locally ambiguous hybrid round, the simultaneous and strict
interpretations must be sibling successors of one policy table.  Selecting a
fresh policy after either child is too late and may create the familiar
accepted-run mosaic.

This file packages both exact root children as reachable false-bit keys of the
same root-pinned policy.  The Boolean is an internal one-shot policy state,
not a graph or leader observation.  Below either child it is permanently
false.
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

/-! ## Exact guarded run automaton and reachable keys -/

noncomputable abbrev ProfiledRawJointHybridInitialRootPinnedRunAutomaton
    (first : In₁ × In₂) :=
  sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointHybridCodeParityDPA A
      (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
    (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridFiniteCodeNext A)

noncomputable abbrev ProfiledRawJointHybridInitialRootPinnedGuardedAutomaton
    (first : In₁ × In₂) :=
  (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy first
    ).rootGuarded
      (sourceFreeBeliefCodeParityRootAllowed
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (profiledRawJointHybridFiniteCodeNext A)
        (profiledRawJointHybridInitialExactRootPredicate A strategy first))

abbrev ProfiledRawJointHybridInitialRootPinnedGuardedState
    (first : In₁ × In₂) :=
  (ProfiledRawJointHybridInitialRootPinnedGuardedAutomaton A strategy
    first).State

abbrev ProfiledRawJointHybridInitialRootPinnedReachable
    (first : In₁ × In₂)
    (state : ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy
      first) : Prop :=
  ∃ node : TreeNode (ProfiledRawJointHybridCode A),
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.run node = state

/-- A reachable post-root state whose underlying tag is common. -/
structure ProfiledRawJointHybridInitialRootPinnedFalseCommonKey
    (first : In₁ × In₂) where
  incidenceCode : ProfiledRawJointIncidenceCode A (I := Unit)
  state : ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first
  reachable : ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin
    first state
  fresh_false : state.1 = false
  state_code : state.2.1 = .common incidenceCode

/-- A reachable post-root state whose underlying tag is one-sided. -/
structure ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey
    (first : In₁ × In₂) where
  incidenceCode : ProfiledRawJointIncidenceCode A (I := Unit)
  state : ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first
  reachable : ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin
    first state
  fresh_false : state.1 = false
  state_code : state.2.1 = .oneSided incidenceCode

noncomputable instance
    profiledRawJointHybridInitialRootPinnedFalseCommonKeyFintype
    (first : In₁ × In₂) :
    Fintype (ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first) := by
  classical
  let encode := fun key :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy hwin
        first ↦ (key.incidenceCode, key.state)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨lc, ls, lr, lf, lcode⟩
    rcases right with ⟨rc, rs, rr, rf, rcode⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

noncomputable instance
    profiledRawJointHybridInitialRootPinnedFalseOneSidedKeyFintype
    (first : In₁ × In₂) :
    Fintype (ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) := by
  classical
  let encode := fun key :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
        first ↦ (key.incidenceCode, key.state)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨lc, ls, lr, lf, lcode⟩
    rcases right with ⟨rc, rs, rr, rf, rcode⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-! ## The two sibling children of the exact guarded root -/

/-- The literal simultaneous child as a false/common key of the guarded
policy. -/
noncomputable def profiledRawJointHybridInitialRootPinnedSimultaneousKey
    (first current : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy hwin
      first := by
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  let childCode := profiledRawJointHybridInitialSimultaneousChildCode A
    strategy first current
  let childState :=
    (false,
      (childCode,
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
            (profiledRawJointHybridCodeParityDPA A
              (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
              ).initial childCode))
  have htable : package.policy.successor (package.policy.run []) childCode =
      childState := by
    rw [package.policy.accepts.1.1]
    exact profiledRawJointHybridInitialRootPinnedPolicy_successor_simultaneous
      A strategy hwin first current
  have hrun : package.policy.run [childCode] = childState := by
    calc
      package.policy.run [childCode] =
          package.policy.successor (package.policy.run []) childCode := by
        simpa using (package.policy.successor_at [] childCode).symm
      _ = childState := htable
  refine {
    incidenceCode :=
      profiledRawJointIncidenceNext A
        ((profiledRawJointCommonWorldFamily A
          (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
          ).incidenceCode A).family
        (ProfiledRawJointHybridInitialLiteralRawMove A strategy first)
        (profiledRawJointBothRestartDirection current)
    state := childState
    reachable := ⟨[childCode], hrun⟩
    fresh_false := rfl
    state_code := ?_ }
  rfl

/-- The literal strict alternative is a false/one-sided sibling in that same
guarded policy. -/
noncomputable def profiledRawJointHybridInitialRootPinnedStrictKey
    (first : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      first := by
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  let childCode := profiledRawJointHybridInitialStrictChildCode A strategy
    first actual
  let childState :=
    (false,
      (childCode,
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
            (profiledRawJointHybridCodeParityDPA A
              (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
              ).initial childCode))
  have htable : package.policy.successor (package.policy.run []) childCode =
      childState := by
    rw [package.policy.accepts.1.1]
    exact profiledRawJointHybridInitialRootPinnedPolicy_successor_strict
      A strategy hwin first actual
  have hrun : package.policy.run [childCode] = childState := by
    calc
      package.policy.run [childCode] =
          package.policy.successor (package.policy.run []) childCode := by
        simpa using (package.policy.successor_at [] childCode).symm
      _ = childState := htable
  refine {
    incidenceCode := profiledRawJointOneSidedNext A
      ((profiledRawJointCommonWorldFamily A
        (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)
        ).incidenceCode A)
      (ProfiledRawJointHybridInitialLiteralRawMove A strategy first)
      (profiledRawJointCommonActualDirection actual)
    state := childState
    reachable := ⟨[childCode], hrun⟩
    fresh_false := rfl
    state_code := ?_ }
  exact profiledRawJointHybridInitialStrictChildCode_eq_oneSidedNext A strategy
    first actual

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Both alternative keys use literally the same guarded policy object.  The
different child tags occur only in their finite states. -/
theorem profiledRawJointHybridInitialRootPinnedSiblingPolicy
    (first current : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    let common := profiledRawJointHybridInitialRootPinnedSimultaneousKey A
      strategy hwin first current
    let strict := profiledRawJointHybridInitialRootPinnedStrictKey A strategy
      hwin first actual
    common.state.1 = false ∧ strict.state.1 = false := by
  exact ⟨rfl, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
