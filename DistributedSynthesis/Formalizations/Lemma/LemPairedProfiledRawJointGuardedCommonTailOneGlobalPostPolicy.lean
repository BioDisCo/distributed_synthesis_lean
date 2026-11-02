/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCrossAnchorJointMove

/-!
# One outer post-policy across both cross-anchor orientations

The separate right- and left-cross-anchor adapters in
`LemPairedProfiledRawJointGuardedCommonTailCrossAnchorJointMove` are useful
local projections, but their types also permit two unrelated rational
policies.  That is too weak for a run which switches strict orientation.

Here both semantic tables are selected as the two projections of one move of
one `CodedObservablePostPolicy.Package`.  The runtime still sees only its
finite local bank.  The exact observation and the outer policy state remain
proof-side data; in particular, no process tests the graph or identifies a
strict leader.

The final two theorems isolate the deliberately weaker handoff interface.
A physical handoff need not reproduce an independently prescribed raw move.
It only has to reindex the next finite anchor to the successor selected by
the one outer policy.  This immediately gives an `AllowedTarget` edge, and a
whole reindexed path is accepting by `accepts_of_allowedTarget_path`.
-/

namespace DistributedSynthesis

universe a b c d e k u v x y s

namespace CodedObservablePostPolicy

variable {Observation : Type a} {Move : Type b} {Code : Type c}
variable [Fintype Code]
variable
  (S : FiniteThreadSystem.{max a b, d, e} (Move × Observation))
  (initialObservation : Observation) (code : Observation → Code)
  (Valid : Code → Move → Prop)

/-- Every exact-observation response of a move bank extracted from one
package is an edge of that same package's rational policy. -/
theorem Package.moveBank_allowedTarget
    {Key : Type k}
    (package : Package S initialObservation code Valid)
    (stateAt : Key → CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      Reachable S initialObservation code Valid package.policy (stateAt key))
    (key : Key) (observation : Observation) :
    AllowedTarget S initialObservation code Valid package.policy (stateAt key)
      (code observation,
        S.universalRunDPA.step (stateAt key).2
          (package.moveBank S initialObservation code Valid stateAt reachableAt
            key, observation)) := by
  exact ⟨observation,
    package.moveBank_successor_eq S initialObservation code Valid stateAt
      reachableAt key observation⟩

/-- Reindexing a concrete successor to the state selected by the one package
is sufficient for an allowed edge.  This asks for equality of finite policy
states, not equality with a separately chosen semantic move family. -/
theorem Package.allowedTarget_of_moveBank_reindex
    {Key : Type k}
    (package : Package S initialObservation code Valid)
    (stateAt : Key → CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      Reachable S initialObservation code Valid package.policy (stateAt key))
    (key nextKey : Key) (observation : Observation)
    (hreindex :
      stateAt nextKey =
        (code observation,
          S.universalRunDPA.step (stateAt key).2
            (package.moveBank S initialObservation code Valid stateAt
              reachableAt key, observation))) :
    AllowedTarget S initialObservation code Valid package.policy (stateAt key)
      (stateAt nextKey) := by
  rw [hreindex]
  exact package.moveBank_allowedTarget S initialObservation code Valid stateAt
    reachableAt key observation

/-- A sequence of physical anchors reindexed to successors of the one global
package is parity accepting, even when the anchor orientation changes at
every step. -/
theorem Package.accepts_of_moveBank_reindexed_path
    {Key : Type k}
    (package : Package S initialObservation code Valid)
    (stateAt : Key → CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      Reachable S initialObservation code Valid package.policy (stateAt key))
    (keys : Nat → Key) (observations : Nat → Observation)
    (hzero : stateAt (keys 0) = package.policy.run [])
    (hreindex : ∀ n,
      stateAt (keys (n + 1)) =
        (code (observations n),
          S.universalRunDPA.step (stateAt (keys n)).2
            (package.moveBank S initialObservation code Valid stateAt
              reachableAt (keys n), observations n))) :
    NatSeqMinEvenParity (fun n ↦
      (Automaton S initialObservation code Valid).priority
        (stateAt (keys n))) := by
  apply accepts_of_allowedTarget_path S initialObservation code Valid
    package.policy (fun n ↦ stateAt (keys n)) hzero
  intro n
  exact package.allowedTarget_of_moveBank_reindex S initialObservation code
    Valid stateAt reachableAt (keys n) (keys (n + 1)) (observations n)
      (hreindex n)

end CodedObservablePostPolicy

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-- A single finite key space covers both possible strict orientations.  The
sum tag is proof-side phase data, not a leader bit read by either process. -/
abbrev ProfiledRawJointGuardedCrossAnchorKey :=
  ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin ⊕
    ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin

/-- One outer move chooses the right and left response tables together. -/
abbrev ProfiledRawJointGuardedCrossAnchorJointMove :=
  CodedObservablePostPolicy.JointMove
    (ProfiledRawJointGuardedRightCrossAnchorJointMove A strategy hwin
      initialBank)
    (ProfiledRawJointGuardedLeftCrossAnchorJointMove A strategy hwin
      initialBank)

/-- The two local executable banks projected from one outer move bank. -/
abbrev ProfiledRawJointGuardedCrossAnchorBanks :=
  ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin initialBank ×
    ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin initialBank

/-- Install both orientation-specific executable banks from one package and
one state assignment on the sum of anchor keys. -/
noncomputable def
    profiledRawJointGuardedCrossAnchorBanksOfJointPostPolicy
    {Observation : Type a} {Code : Type c} [Fintype Code]
    (S : FiniteThreadSystem.{max a (max u v x y s), d, e}
      (ProfiledRawJointGuardedCrossAnchorJointMove A strategy hwin
          initialBank × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code →
      ProfiledRawJointGuardedCrossAnchorJointMove A strategy hwin initialBank →
        Prop)
    (package : CodedObservablePostPolicy.Package S initialObservation code
      Valid)
    (stateAt : ProfiledRawJointGuardedCrossAnchorKey A strategy hwin →
      CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      CodedObservablePostPolicy.Reachable S initialObservation code Valid
        package.policy (stateAt key)) :
    ProfiledRawJointGuardedCrossAnchorBanks A strategy hwin initialBank :=
  let bank := package.moveBank S initialObservation code Valid stateAt
    reachableAt
  (fun key ↦ (bank (.inl key)).1, fun key ↦ (bank (.inr key)).2)

/-- The right table is literally the first projection of the move selected by
the one global package at the corresponding sum key. -/
theorem profiledRawJointGuardedCrossAnchorBanksOfJointPostPolicy_right_apply
    {Observation : Type a} {Code : Type c} [Fintype Code]
    (S : FiniteThreadSystem.{max a (max u v x y s), d, e}
      (ProfiledRawJointGuardedCrossAnchorJointMove A strategy hwin
          initialBank × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code →
      ProfiledRawJointGuardedCrossAnchorJointMove A strategy hwin initialBank →
        Prop)
    (package : CodedObservablePostPolicy.Package S initialObservation code
      Valid)
    (stateAt : ProfiledRawJointGuardedCrossAnchorKey A strategy hwin →
      CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      CodedObservablePostPolicy.Reachable S initialObservation code Valid
        package.policy (stateAt key))
    (key : ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin) :
    (profiledRawJointGuardedCrossAnchorBanksOfJointPostPolicy A strategy hwin
      initialBank S initialObservation code Valid package stateAt reachableAt).1
        key =
      (package.moveBank S initialObservation code Valid stateAt reachableAt
        (.inl key)).1 := by
  rfl

/-- Left-orientation mirror of the projection equation. -/
theorem profiledRawJointGuardedCrossAnchorBanksOfJointPostPolicy_left_apply
    {Observation : Type a} {Code : Type c} [Fintype Code]
    (S : FiniteThreadSystem.{max a (max u v x y s), d, e}
      (ProfiledRawJointGuardedCrossAnchorJointMove A strategy hwin
          initialBank × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code →
      ProfiledRawJointGuardedCrossAnchorJointMove A strategy hwin initialBank →
        Prop)
    (package : CodedObservablePostPolicy.Package S initialObservation code
      Valid)
    (stateAt : ProfiledRawJointGuardedCrossAnchorKey A strategy hwin →
      CodedObservableInputFreeState (Code := Code) S)
    (reachableAt : ∀ key,
      CodedObservablePostPolicy.Reachable S initialObservation code Valid
        package.policy (stateAt key))
    (key : ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin) :
    (profiledRawJointGuardedCrossAnchorBanksOfJointPostPolicy A strategy hwin
      initialBank S initialObservation code Valid package stateAt reachableAt).2
        key =
      (package.moveBank S initialObservation code Valid stateAt reachableAt
        (.inr key)).2 := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
