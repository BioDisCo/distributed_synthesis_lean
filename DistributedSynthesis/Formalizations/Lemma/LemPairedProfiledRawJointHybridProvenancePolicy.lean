/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonHybridSemanticParity
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodeDirection

/-!
# Finite provenance policy for the common/one-sided raw joint tree

The hybrid semantic tree has an infinite proof-side direction alphabet, but
its public child code is finite.  We therefore rationalize only after replacing
raw directions by finite child-code tags.  The resulting executable policy has
no arbitrary-direction rational-basis hypothesis.

Reachable policy states retain both the tagged hybrid code and the state of
the parity monitor.  The latter is deliberately kept in the one-sided key:
the public code does not determine the monitor state, and the rational
successor table is indexed by the complete product state.

This file only installs the hybrid policy and exposes semantic provenance.  It
does not identify a reachable one-sided suffix with the older independently
rationalized one-sided policy.
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

/-! ## Finite child-code rational policy -/

/-- Replace each raw hybrid direction by the finite tag equal to its requested
child code. -/
noncomputable def profiledRawJointHybridFiniteCodeNext
    (code : ProfiledRawJointHybridCode A)
    (move : ProfiledRawJointHybridMove A)
    (childCode : ProfiledRawJointHybridCode A) :
    ProfiledRawJointHybridCode A :=
  sourceFreeBeliefFiniteCodeNext
    (Direction := ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (profiledRawJointHybridNext A) code move childCode

/-- Provenance-strengthened hybrid policy over the finite child-code
direction alphabet. -/
noncomputable abbrev ProfiledRawJointHybridProvenanceRationalPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridFiniteCodeNext A)

/-- Complete finite state: the current hybrid code together with the code-DPA
state. -/
noncomputable abbrev ProfiledRawJointHybridProvenancePolicyState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridFiniteCodeNext A)).State

/-- Reachability in the one selected hybrid rational run. -/
abbrev ProfiledRawJointHybridProvenancePolicyReachable
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridFiniteCodeNext A)
    policy state

/-- One installed move realizes every finite child-code successor at this
complete policy state. -/
def ProfiledRawJointHybridProvenanceMoveRealizesAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointHybridMove A) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.MoveRealizesAt
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridFiniteCodeNext A)
    policy state move

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The winning hybrid semantic tree yields an executable finite-direction
rational policy without an arbitrary-direction rational-basis assumption. -/
theorem nonempty_profiledRawJointHybridProvenanceRationalPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty (ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
        A))) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let certificate :=
    profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial
  exact certificate.nonempty_finiteCodeDirectionRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    raw

/-! ## Reachability and installed semantic source -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The root of the selected hybrid policy is reachable. -/
theorem profiledRawJointHybridProvenancePolicy_initial_reachable
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) :
    ProfiledRawJointHybridProvenancePolicyReachable A strategy initialCode
      policy (policy.run []) :=
  ⟨[], rfl⟩

/-- Every finite child-code successor of a reachable state remains in the
same selected rational run. -/
theorem profiledRawJointHybridProvenancePolicy_successor_reachable
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (hreachable : ProfiledRawJointHybridProvenancePolicyReachable A strategy
      initialCode policy state)
    (childCode : ProfiledRawJointHybridCode A) :
    ProfiledRawJointHybridProvenancePolicyReachable A strategy initialCode
      policy (policy.successor state childCode) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [childCode], ?_⟩
  rw [← policy.successor_at node childCode, hnode]

/-- Every reachable state has one installed hybrid move realizing its entire
finite successor table. -/
theorem exists_profiledRawJointHybridProvenanceInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (hreachable : ProfiledRawJointHybridProvenancePolicyReachable A strategy
      initialCode policy state) :
    ∃ move : ProfiledRawJointHybridMove A,
      ProfiledRawJointHybridProvenanceMoveRealizesAt A strategy initialCode
        policy state move := by
  exact SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridFiniteCodeNext A)
    policy state hreachable

/-- Invert the provenance component of an installed move into one literal
hybrid semantic source with exactly the policy code and installed move. -/
theorem ProfiledRawJointHybridProvenanceMoveRealizesAt.exists_semanticSource
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointHybridMove A)
    (hmove : ProfiledRawJointHybridProvenanceMoveRealizesAt A strategy
      initialCode policy state move) :
    ∃ source : ProfiledRawJointHybridSemanticState A strategy,
      source.code A = state.1 ∧ source.move A = move := by
  exact hmove.1

/-- Combined installation form used by later local controller adapters. -/
theorem exists_profiledRawJointHybridProvenanceInstalledSemanticSource
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode)
    (hreachable : ProfiledRawJointHybridProvenancePolicyReachable A strategy
      initialCode policy state) :
    ∃ move : ProfiledRawJointHybridMove A,
      ∃ source : ProfiledRawJointHybridSemanticState A strategy,
        ProfiledRawJointHybridProvenanceMoveRealizesAt A strategy initialCode
            policy state move ∧
          source.code A = state.1 ∧ source.move A = move := by
  rcases exists_profiledRawJointHybridProvenanceInstalledMove A strategy
      initialCode policy state hreachable with ⟨move, hmove⟩
  rcases hmove.exists_semanticSource A strategy initialCode policy state move
      with ⟨source, hcode, hsourceMove⟩
  exact ⟨move, source, hmove, hcode, hsourceMove⟩

end

/-! ## Finite reachable one-sided keys -/

/-- A reachable complete hybrid policy state whose tagged public code is
literally one-sided.  The incidence code is stored explicitly, avoiding later
dependent equality inversion.  The complete state, including its code-DPA
coordinate, is retained. -/
structure ProfiledRawJointHybridOneSidedPolicyKey
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) where
  incidenceCode : ProfiledRawJointIncidenceCode A (I := Unit)
  state : ProfiledRawJointHybridProvenancePolicyState A strategy initialCode
  reachable : ProfiledRawJointHybridProvenancePolicyReachable A strategy
    initialCode policy state
  state_code : state.1 = .oneSided incidenceCode

/-- The reachable one-sided policy keys form a finite controller alphabet. -/
noncomputable instance profiledRawJointHybridOneSidedPolicyKeyFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) :
    Fintype (ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
      policy) := by
  classical
  let encode := fun key : ProfiledRawJointHybridOneSidedPolicyKey A strategy
      initialCode policy ↦ (key.incidenceCode, key.state)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftCode, leftState, leftReachable, leftStateCode⟩
    rcases right with
      ⟨rightCode, rightState, rightReachable, rightStateCode⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

end

end DetParityAutomaton

end DistributedSynthesis
