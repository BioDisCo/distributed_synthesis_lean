/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy

/-!
# Reachable tail keys for the parent-linked entry policy

The root-pinned parent-linked policy already gives the exact finite state
after the entry input.  This file turns its false-bit tail into a finite
recurrent key.  A key retains reachability in that one selected accepting
policy, exposes its current guarded pair and literal-cross annotation, and
advances using the same policy successor table.

Unlike the older root-only false key, the public code here contains the
annotation installed by the parent.  Hence the pair and cross tables at every
successor are literally the two projections of one selected child annotation.
No semantic occurrence is an argument of an executable transition.
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

private abbrev ParentState (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedState A
    strategy hwin initial

private abbrev ParentRunState (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedRunState A
    strategy hwin initial

private abbrev ParentMove :=
  ProfiledRawJointGuardedCommonLiteralCrossParentLinkedMove A strategy hwin

private abbrev ParentValid :=
  ProfiledRawJointGuardedCommonLiteralCrossParentLinkedValid A strategy hwin

private noncomputable abbrev ParentNext :=
  profiledRawJointGuardedCommonLiteralCrossParentLinkedNext A strategy hwin

private noncomputable abbrev ParentDPA (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossParentLinkedDPA A strategy hwin
    initial

/-! ## Reachable finite keys -/

/-- Reachability is measured in the one selected root-pinned parent-linked
policy. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedReachable
    (initial : CommonPoint A strategy) (state : ParentState A strategy hwin
      initial) : Prop :=
  ∃ node : TreeNode (In₁ × In₂),
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial).policy.run node = state

/-- A reachable state below the unique fresh root. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey
    (initial : CommonPoint A strategy) where
  state : ParentState A strategy hwin initial
  reachable :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedReachable A
      strategy hwin initial state
  fresh_false : state.1 = false

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKeyFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey
        A strategy hwin initial) := by
  classical
  let encode := fun key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey
        A strategy hwin initial ↦ key.state
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    simp only [encode] at heq
    cases heq
    rfl)

/-- Exact key obtained by consuming the actual entry input. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
      strategy hwin initial := by
  let state :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState A
      strategy hwin initial entry
  refine ⟨state, ⟨[entry], rfl⟩, ?_⟩
  have hstate := congrArg Prod.fst
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_eq
      A strategy hwin initial entry)
  simpa [state] using hstate

/-- Current guarded pair carried in the public parent-linked annotation. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.pair
    {initial : CommonPoint A strategy}
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial) :
    ProfiledRawJointGuardedCommonPair A strategy hwin :=
  key.state.2.1.2.1

/-- Current literal-cross table pair carried beside the guarded pair. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.extra
    {initial : CommonPoint A strategy}
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial) :
    ProfiledRawJointGuardedCommonLiteralCrossExtra A :=
  key.state.2.1.2.2

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey_pair
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey A
      strategy hwin initial entry).pair A strategy hwin =
      (initial.step A strategy entry).move A strategy hwin := by
  exact
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_pair
      A strategy hwin initial entry

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey_extra
    (initial : CommonPoint A strategy) (entry : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey A
      strategy hwin initial entry).extra A strategy hwin =
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
        (initial.step A strategy entry) := by
  exact
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_extra
      A strategy hwin initial entry

/-! ## Successors stay below the root guard -/

/-- A successor of a reachable false state cannot return to the unique fresh
root. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinked_successor_fresh_false
    (initial : CommonPoint A strategy)
    (state : ParentState A strategy hwin initial)
    (hreachable :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedReachable
        A strategy hwin initial state)
    (hfresh : state.1 = false) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial).policy.successor state input).1 = false := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial
  rcases hreachable with ⟨node, hnode⟩
  cases node with
  | nil =>
      have hroot : (package.policy.run []).1 = true :=
        congrArg Prod.fst package.policy.accepts.1.1
      have htrue : state.1 = true := by
        rw [← hnode, hroot]
      rw [htrue] at hfresh
      contradiction
  | cons head tail =>
      have hchild := package.policy.successor_at (head :: tail) input
      have hbelow :=
        InputFreeRunParityTreeAutomaton.rootGuardedPolicy_fresh_false _ _
          package.policy head (tail ++ [input])
      rw [hnode] at hchild
      rw [hchild]
      simpa [List.append_assoc] using hbelow

/-- Executable successor inside the same selected parent-linked policy. -/
noncomputable def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.successor
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
      strategy hwin initial := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial
  let next := package.policy.successor key.state input
  have hreachable :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedReachable
        A strategy hwin initial next := by
    rcases key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [input], ?_⟩
    rw [← package.policy.successor_at node input, hnode]
  exact {
    state := next
    reachable := hreachable
    fresh_false :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinked_successor_fresh_false
        A strategy hwin initial key.state key.reachable key.fresh_false input }

@[simp] theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.successor_state
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial)
    (input : In₁ × In₂) :
    (key.successor A strategy hwin initial input).state =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
        strategy hwin initial).policy.successor key.state input :=
  rfl

/-! ## The one selected annotated move at a key -/

/-- A parent-linked move realizes the complete guarded-policy successor table
at one reachable false key. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveRealizesAt
    (initial : CommonPoint A strategy)
    (state : ParentState A strategy hwin initial)
    (move : ParentMove A strategy hwin) : Prop :=
  ParentValid A strategy hwin state.2.1 move ∧
    ∀ input : In₁ × In₂,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
        strategy hwin initial).policy.successor state input =
        let childCode := ParentNext A strategy hwin state.2.1 move input
        (false,
          (childCode,
            (ParentDPA A strategy hwin initial).step state.2.2 childCode))

/-- Legality exposes one annotated move at every reachable false key. -/
theorem
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMove
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial) :
    ∃ move : ParentMove A strategy hwin,
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveRealizesAt
        A strategy hwin initial key.state move := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial
  rcases key.reachable with ⟨node, hnode⟩
  have hlegal := package.policy.legal_at node
  rw [hnode] at hlegal
  have hstate : key.state = (false, key.state.2) := by
    apply Prod.ext
    · exact key.fresh_false
    · rfl
  rw [hstate] at hlegal
  change ∃ next : (In₁ × In₂) → ParentRunState A strategy hwin initial,
    (∃ move : ParentMove A strategy hwin,
      ParentValid A strategy hwin key.state.2.1 move ∧
        ∀ input : In₁ × In₂,
          let childCode :=
            ParentNext A strategy hwin key.state.2.1 move input
          next input =
            (childCode,
              (ParentDPA A strategy hwin initial).step key.state.2.2
                childCode)) ∧
      package.policy.successor (false, key.state.2) =
        fun input ↦ (false, next input) at hlegal
  rcases hlegal with ⟨next, ⟨move, hvalid, hnext⟩, htable⟩
  refine ⟨move, hvalid, ?_⟩
  intro input
  rw [hstate]
  rw [htable]
  exact congrArg (fun state ↦ (false, state)) (hnext input)

/-- Total finite move-table lookup at a reachable key. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial) : ParentMove A strategy hwin :=
  Classical.choose
    (exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMove
      A strategy hwin initial key)

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt_realizes
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveRealizesAt
      A strategy hwin initial key.state
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt
          A strategy hwin initial key) :=
  Classical.choose_spec
    (exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMove
      A strategy hwin initial key)

/-- The current component of the selected move is the pair carried by the
same key annotation. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt_current
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
      strategy hwin initial key).1 = key.pair A strategy hwin := by
  let move :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
      strategy hwin initial key
  have hvalid :=
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt_realizes
      A strategy hwin initial key).1
  rcases hvalid.2 with
    ⟨point, _hcode, hannotation, hpointMove, _hchildren⟩
  have hpair := congrArg Prod.fst hannotation
  calc
    move.1 = point.move A strategy hwin := hpointMove.symm
    _ = key.pair A strategy hwin := by
      simpa [move,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.pair,
        profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf] using hpair

/-- The successor key carries exactly the pair and cross-table projections of
the child annotation selected by the current move. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.successor_annotation
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial)
    (input : In₁ × In₂) :
    ((key.successor A strategy hwin initial input).pair A strategy hwin,
      (key.successor A strategy hwin initial input).extra A strategy hwin) =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
        strategy hwin initial key).2 input := by
  let move :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
      strategy hwin initial key
  have hnext :=
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt_realizes
      A strategy hwin initial key).2 input
  unfold
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.pair
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.extra
  rw [key.successor_state A strategy hwin initial input]
  rw [hnext]
  rfl

theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.successor_pair
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial)
    (input : In₁ × In₂) :
    (key.successor A strategy hwin initial input).pair A strategy hwin =
      ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
        strategy hwin initial key).2 input).1 := by
  exact congrArg Prod.fst
    (key.successor_annotation A strategy hwin initial input)

theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey.successor_extra
    (initial : CommonPoint A strategy)
    (key :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
        strategy hwin initial)
    (input : In₁ × In₂) :
    (key.successor A strategy hwin initial input).extra A strategy hwin =
      ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedMoveAt A
        strategy hwin initial key).2 input).2 := by
  exact congrArg Prod.snd
    (key.successor_annotation A strategy hwin initial input)

end

end DetParityAutomaton

end DistributedSynthesis
