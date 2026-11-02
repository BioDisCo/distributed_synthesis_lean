/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedPackage

/-!
# The exact entry key below a root-pinned literal-cross policy

The guarded root is consumed by the simultaneous input at an honest entry.
This file packages the resulting child as a reachable false-bit state of the
same rational policy.  It then exposes the common false-state successor table
and proves that every later transition stays below the one-shot guard.

No policy is re-rationalized at the child.  In particular, the entry key
retains both the exact child code and the objective-DPA state reached from the
literal predecessor.
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
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev CrossExtra :=
  ProfiledRawJointGuardedCommonLiteralCrossExtra A

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

private abbrev DecoratedMove :=
  ProfiledRawJointGuardedCommonPair A strategy hwin × CrossExtra A

private noncomputable abbrev RootPolicy
    (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
    initial

private noncomputable abbrev RunAutomaton
    (initial : CommonPoint A strategy) :=
  sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      (CrossValid A strategy hwin))
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)

/-- Finite state space of the one-shot guarded literal-cross policy. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedState
    (initial : CommonPoint A strategy) :=
  Bool × (RunAutomaton A strategy hwin initial).State

/-- Reachability is always taken in the one selected guarded policy. -/
def ProfiledRawJointGuardedCommonLiteralCrossRootPinnedReachable
    (initial : CommonPoint A strategy)
    (state :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedState A strategy hwin
        initial) : Prop :=
  ∃ node : TreeNode (In₁ × In₂),
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial).policy.run node = state

/-- A finite key below the guarded root.  The proof fields certify that the
state belongs to the selected policy and that the one-shot root bit has
already been consumed. -/
structure ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey
    (initial : CommonPoint A strategy) where
  state :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedState A strategy hwin
      initial
  reachable :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedReachable A strategy
      hwin initial state
  fresh_false : state.1 = false

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKeyFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) := by
  classical
  let encode := fun key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial ↦ key.state
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    simp only [encode] at heq
    cases heq
    rfl)

/-- The exact simultaneous child of the literal predecessor, retained as a
false-bit key of the same guarded rational policy. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
      hwin initial := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial
  let childCode :=
    (initial.move A strategy hwin).bothNextCode A strategy hwin input
  let D := profiledRawJointGuardedCommonCodeParityDPA A
    (initial.code A strategy)
  let childState :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedState A strategy hwin
        initial :=
    (false, (childCode, D.step D.initial childCode))
  have htable : package.policy.successor (package.policy.run []) input =
      childState := by
    rw [package.policy.accepts.1.1]
    exact
      profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_successor A
        strategy hwin initial input
  have hrun : package.policy.run [input] = childState := by
    calc
      package.policy.run [input] =
          package.policy.successor (package.policy.run []) input := by
        simpa using (package.policy.successor_at [] input).symm
      _ = childState := htable
  exact {
    state := childState
    reachable := ⟨[input], hrun⟩
    fresh_false := rfl }

/-- The concrete key is exactly the singleton-input state of the selected
guarded policy.  This equation prevents a later controller layer from
silently replacing it by an independently selected child policy. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey_state
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey A strategy
      hwin initial input).state =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy
        hwin initial).policy.run [input] := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial
  let childCode :=
    (initial.move A strategy hwin).bothNextCode A strategy hwin input
  let D := profiledRawJointGuardedCommonCodeParityDPA A
    (initial.code A strategy)
  let childState :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedState A strategy hwin
        initial :=
    (false, (childCode, D.step D.initial childCode))
  have htable : package.policy.successor (package.policy.run []) input =
      childState := by
    rw [package.policy.accepts.1.1]
    exact
      profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_successor A
        strategy hwin initial input
  change childState = package.policy.run [input]
  symm
  calc
    package.policy.run [input] =
        package.policy.successor (package.policy.run []) input := by
      simpa using (package.policy.successor_at [] input).symm
    _ = childState := htable

/-- The public code stored by the entry key is exactly the literal child's
code, not merely the code of a reselected representative. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey_code
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey A strategy
      hwin initial input).state.2.1 =
      (initial.step A strategy input).code A strategy := by
  change (initial.move A strategy hwin).bothNextCode A strategy hwin input = _
  exact (ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
    initial input).symm

/-- The entry key contains the exact objective-DPA successor reached by
reading its literal child code. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey_control
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey A strategy
      hwin initial input).state.2.2 =
      let D := profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy)
      let childCode :=
        (initial.move A strategy hwin).bothNextCode A strategy hwin input
      D.step D.initial childCode := by
  rfl

/-! ## The shared table below the one-shot root -/

/-- Every false-bit state uses the same tail successor table of the guarded
policy.  The Boolean is inserted only to query that table and is discarded
from the result. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedTailSuccessor
    (initial : CommonPoint A strategy)
    (state : (RunAutomaton A strategy hwin initial).State)
    (input : In₁ × In₂) :
    (RunAutomaton A strategy hwin initial).State :=
  ((profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial).policy.successor (false, state) input).2

/-- A successor of a reachable false-bit state cannot re-enter the unique
guarded root. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinned_successor_fresh_false
    (initial : CommonPoint A strategy)
    (state :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedState A strategy hwin
        initial)
    (hreachable :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedReachable A strategy
        hwin initial state)
    (hfresh : state.1 = false) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial).policy.successor state input).1 = false := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial
  rcases hreachable with ⟨node, hnode⟩
  cases node with
  | nil =>
      have hroot : package.policy.run [] =
          (true, (RunAutomaton A strategy hwin initial).initial) :=
        package.policy.accepts.1.1
      have htrue : state.1 = true := by
        rw [← hnode, hroot]
      rw [htrue] at hfresh
      contradiction
  | cons head tail =>
      have hchild := package.policy.successor_at (head :: tail) input
      have hbelow :=
        InputFreeRunParityTreeAutomaton.rootGuardedPolicy_fresh_false
          (RunAutomaton A strategy hwin initial)
          (sourceFreeBeliefCodeParityRootAllowed
            (profiledRawJointGuardedCommonCodeParityDPA A
              (initial.code A strategy))
            (initial.code A strategy)
            (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
              (CrossValid A strategy hwin))
            (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
            (profiledRawJointGuardedCommonLiteralCrossRootPred A strategy hwin
              initial))
          package.policy head (tail ++ [input])
      rw [hnode] at hchild
      rw [hchild]
      simpa [List.append_assoc] using hbelow

/-- The complete guarded successor of a reachable false key is the false tag
paired with the shared tail-table result. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey.successor_eq_tail
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
        initial).policy.successor key.state input =
      (false,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedTailSuccessor A
          strategy hwin initial key.state.2 input) := by
  have hstate : key.state = (false, key.state.2) := by
    apply Prod.ext
    · exact key.fresh_false
    · rfl
  apply Prod.ext
  · exact
      profiledRawJointGuardedCommonLiteralCrossRootPinned_successor_fresh_false
        A strategy hwin initial key.state key.reachable key.fresh_false input
  · rw [hstate]
    rfl

/-! ## Literal decorated moves installed by the shared tail -/

/-- A decorated move realizes the complete successor table at one underlying
false-state coordinate. -/
def ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveRealizesAt
    (initial : CommonPoint A strategy)
    (state : (RunAutomaton A strategy hwin initial).State)
    (move : DecoratedMove A strategy hwin) : Prop :=
  ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      (CrossValid A strategy hwin) state.1 move ∧
    ∀ input : In₁ × In₂,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedTailSuccessor A
          strategy hwin initial state input =
        (move.1.bothNextCode A strategy hwin input,
          (profiledRawJointGuardedCommonCodeParityDPA A
            (initial.code A strategy)).step state.2
              (move.1.bothNextCode A strategy hwin input))

/-- Legality of the single guarded policy exposes one decorated move at every
reachable false key.  Thus subsequent bootstrap steps retain both a guarded
pair and the preselected literal-cross table IDs without a new choice. -/
theorem
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMove
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) :
    ∃ move : DecoratedMove A strategy hwin,
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveRealizesAt A
        strategy hwin initial key.state.2 move := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial
  rcases key.reachable with ⟨node, hnode⟩
  have hlegal := package.policy.legal_at node
  rw [hnode] at hlegal
  have hstate : key.state = (false, key.state.2) := by
    apply Prod.ext
    · exact key.fresh_false
    · rfl
  rw [hstate] at hlegal
  change ∃ next : (In₁ × In₂) →
      (RunAutomaton A strategy hwin initial).State,
    (∃ move : DecoratedMove A strategy hwin,
      ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
          (CrossValid A strategy hwin) key.state.2.1 move ∧
        ∀ input : In₁ × In₂,
          next input =
            (move.1.bothNextCode A strategy hwin input,
              (profiledRawJointGuardedCommonCodeParityDPA A
                (initial.code A strategy)).step key.state.2.2
                  (move.1.bothNextCode A strategy hwin input))) ∧
      package.policy.successor (false, key.state.2) =
        fun input ↦ (false, next input) at hlegal
  rcases hlegal with ⟨next, ⟨move, hvalid, hnext⟩, htable⟩
  refine ⟨move, hvalid, ?_⟩
  intro input
  change (package.policy.successor (false, key.state.2) input).2 = _
  rw [htable]
  exact hnext input

/-- Total finite lookup of the decorated move installed at a false key.  The
choice is made once as part of the finite controller table; no semantic
occurrence is an argument of a runtime transition. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) : DecoratedMove A strategy hwin :=
  Classical.choose
    (exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMove A
      strategy hwin initial key)

/-- The total lookup realizes the selected guarded policy's complete
successor table. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt_realizes
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveRealizesAt A
      strategy hwin initial key.state.2
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt A
        strategy hwin initial key) :=
  Classical.choose_spec
    (exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMove A
      strategy hwin initial key)

/-- Proof-side literal occurrence represented by a false key's total finite
move table.  This witness is extracted from the pre-rationalized cross-table
validity proof and is not stored in an endpoint control. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) : CommonPoint A strategy :=
  Classical.choose
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt_realizes A
      strategy hwin initial key).1.2

/-- The proof-side occurrence has the exact public code stored by the key. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt_code
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt A strategy
      hwin initial key).code A strategy = key.state.2.1 :=
  (Classical.choose_spec
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt_realizes A
      strategy hwin initial key).1.2).1

/-- Its guarded pair is exactly the pair stored in the finite move table. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt_move
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt A strategy
      hwin initial key).move A strategy hwin =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt A
        strategy hwin initial key).1 :=
  (Classical.choose_spec
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt_realizes A
      strategy hwin initial key).1.2).2.1

/-- Its two literal-cross table IDs are exactly the annotation stored in the
same finite move table. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt_extra
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial) :
    profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt A
          strategy hwin initial key) =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt A
        strategy hwin initial key).2 :=
  (Classical.choose_spec
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt_realizes A
      strategy hwin initial key).1.2).2.2

/-- Executable successor of a false key inside the same guarded policy. -/
noncomputable def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey.successor
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
      hwin initial := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial
  let next := package.policy.successor key.state input
  have hreachable :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedReachable A strategy
        hwin initial next := by
    rcases key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [input], ?_⟩
    rw [← package.policy.successor_at node input, hnode]
  exact {
    state := next
    reachable := hreachable
    fresh_false :=
      profiledRawJointGuardedCommonLiteralCrossRootPinned_successor_fresh_false
        A strategy hwin initial key.state key.reachable key.fresh_false input }

/-- Field equation for the executable false-key transition. -/
@[simp] theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey.successor_state
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial)
    (input : In₁ × In₂) :
    (key.successor A strategy hwin initial input).state =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy
        hwin initial).policy.successor key.state input := by
  rfl

/-- Concrete transition equation: the finite move stored at the current key
determines both the exact child code and the objective-DPA successor. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey.successor_eq
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial)
    (input : In₁ × In₂) :
    (key.successor A strategy hwin initial input).state =
      let move :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt A
          strategy hwin initial key
      (false,
        (move.1.bothNextCode A strategy hwin input,
          (profiledRawJointGuardedCommonCodeParityDPA A
            (initial.code A strategy)).step key.state.2.2
              (move.1.bothNextCode A strategy hwin input))) := by
  dsimp only
  rw [key.successor_state A strategy hwin initial input]
  rw [key.successor_eq_tail A strategy hwin initial input]
  rw [(profiledRawJointGuardedCommonLiteralCrossRootPinnedFalseMoveAt_realizes
    A strategy hwin initial key).2 input]
  rfl

/-- Occurrence-sensitive form of the successor equation: the next key names
the literal simultaneous child of the occurrence extracted at the current
key. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey.successor_code
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy
        hwin initial)
    (input : In₁ × In₂) :
    (key.successor A strategy hwin initial input).state.2.1 =
      ((profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt A
        strategy hwin initial key).step A strategy input).code A strategy := by
  rw [key.successor_eq A strategy hwin initial input]
  dsimp only
  rw [←
    profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt_move A
      strategy hwin initial key]
  exact
    (ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedFalsePointAt A
        strategy hwin initial key) input).symm

end

end DetParityAutomaton

end DistributedSynthesis
