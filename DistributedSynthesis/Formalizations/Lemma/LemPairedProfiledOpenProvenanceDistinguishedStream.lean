/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedRawState

/-!
# Iterating the finite provenance distinguished state

This file is the query-generic runtime bridge for the delayed physical recut.
It iterates the finite distinguished recurrence along an arbitrary stream of
completed-direction queries.  No physical-boundary convention is built into
the iterator: a later adapter only has to produce the query stream.

At every index the public coordinate follows the literal finite table, the
proof-side actual coordinate follows one policy-retagged exact edge, and its
code-policy state and move remain coherent.  The complete range lies in one
finite state type; cursor nodes and query histories occur only inside erased
representation proofs inherited from the one-step construction.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable
  (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev StreamState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev StreamQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

/-! ## Arbitrary-source iteration -/

/-- Iterate the finite transition from any already represented distinguished
state. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedStateAtFrom
    (start : StreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : Nat → StreamQuery A initialCode) : Nat →
      StreamState A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package
  | 0 => start
  | n + 1 =>
      profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedStateAtFrom start query n)
        (query n)

@[simp] theorem profiledOpenProvenancePolicyDistinguishedStateAtFrom_zero
    (start : StreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : Nat → StreamQuery A initialCode) :
    profiledOpenProvenancePolicyDistinguishedStateAtFrom A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start query
        0 = start :=
  rfl

theorem profiledOpenProvenancePolicyDistinguishedStateAtFrom_succ
    (start : StreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    profiledOpenProvenancePolicyDistinguishedStateAtFrom A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start query
          (n + 1) =
      profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedStateAtFrom A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          start query n) (query n) :=
  rfl

/-! ## Initial-table iteration -/

/-- Canonical stream run starting at the provenance table root. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedStateAt
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    StreamState A strategy hwin basis initialCode codePolicy fixedPolicy point
      initialRoot package :=
  profiledOpenProvenancePolicyDistinguishedStateAtFrom A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package
    (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package) query n

@[simp] theorem profiledOpenProvenancePolicyDistinguishedStateAt_zero
    (query : Nat → StreamQuery A initialCode) :
    profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query 0 =
      profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package :=
  rfl

theorem profiledOpenProvenancePolicyDistinguishedStateAt_succ
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query
          (n + 1) =
      profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package query n)
        (query n) :=
  rfl

/-! ## Pointwise coupling laws -/

/-- The public table coordinate follows the existing finite recurrence at
every query index. -/
theorem profiledOpenProvenancePolicyDistinguishedStateAt_public_succ
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package query
          (n + 1)) =
      profiledOpenProvenancePolicyRetaggedBranchStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            query n))
        (query n) := by
  rw [profiledOpenProvenancePolicyDistinguishedStateAt_succ]
  exact profiledOpenProvenancePolicyDistinguishedStep_public A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package _ _

/-- Consecutive actual candidates form one literal retagged exact edge. -/
theorem profiledOpenProvenancePolicyDistinguishedStateAt_exact
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    let current := profiledOpenProvenancePolicyDistinguishedStateAt A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query n
    let next := profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
      (n + 1)
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy
      ((profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current
        ).2.1)
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current)
      (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package current)
      (query n)
      (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next).1
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package next) := by
  rw [profiledOpenProvenancePolicyDistinguishedStateAt_succ]
  exact profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package _ _

/-- The policy-state projection follows the code policy at every index. -/
theorem profiledOpenProvenancePolicyDistinguishedStateAt_policySuccessor
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query
        (n + 1))).1 =
      codePolicy.successor
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            query n)).1
        (query n).1.2 := by
  rw [profiledOpenProvenancePolicyDistinguishedStateAt_succ]
  exact profiledOpenProvenancePolicyDistinguishedStep_policySuccessor A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
    package _ _

/-- Both endpoint move identities of every stream edge realize the same
selected code policy at their respective states. -/
theorem profiledOpenProvenancePolicyDistinguishedStateAt_moveRealizes
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    let current := profiledOpenProvenancePolicyDistinguishedStateAt A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query n
    let next := profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
      (n + 1)
    ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin basis
        initialCode codePolicy
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          current).moveIdentity ∧
      ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
        basis initialCode codePolicy
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          next).1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          next).moveIdentity := by
  rw [profiledOpenProvenancePolicyDistinguishedStateAt_succ]
  exact profiledOpenProvenancePolicyDistinguishedStep_moveRealizes A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package _ _

/-- Membership, liveness, and current-bank validity hold at every stream
position. -/
theorem profiledOpenProvenancePolicyDistinguishedStateAt_mem_live_valid
    (query : Nat → StreamQuery A initialCode) (n : Nat) :
    let current := profiledOpenProvenancePolicyDistinguishedStateAt A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query n
    let actual := profiledOpenProvenancePolicyDistinguishedActual A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      current
    actual ∈
        (profiledOpenProvenancePolicyDistinguishedPublic A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package
          current).2 ∧
      ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis initialCode
        codePolicy actual.2 actual.1 ∧
      ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
        initialCode actual.2 actual.1
          (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package
            current) :=
  profiledOpenProvenancePolicyDistinguished_mem_live_valid A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package _

/-! ## Explicit finite-memory boundary -/

/-- The state space used by the stream iterator is finite (and already carries
the explicit `Fintype` instance constructed by the one-step module). -/
theorem profiledOpenProvenancePolicyDistinguishedStreamState_finite :
    Finite (StreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package) := by
  infer_instance

/-- Every query stream is carried by one fixed finite memory set.  This is the
finite-memory statement consumed by the global recut adapter; it does not
bound or store the query history. -/
theorem profiledOpenProvenancePolicyDistinguishedStateAt_finiteMemory
    (query : Nat → StreamQuery A initialCode) :
    ∃ memory : Finset (StreamState A strategy hwin basis initialCode
        codePolicy fixedPolicy point initialRoot package),
      ∀ n,
        profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package query n ∈
          memory := by
  exact ⟨Finset.univ, fun _ ↦ Finset.mem_univ _⟩

end

end DetParityAutomaton

end DistributedSynthesis
