/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalCarrier

/-!
# The post-initial operational transition kernel

This module turns the proof-level matched phase invariant into total finite
local operations.  Matching is checked only at a receive, when each process
has the partner's finite summary.  No local state stores the current graph,
the current strict orientation, or the identity of a strict leader.
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

/-! ## Decoding a received pair of finite controls -/

/-- Recover a right-oriented proof phase from its two finite projections.
The dependent equality is decided only after the projections have met at a
receive. -/
noncomputable def profiledMatchedRightOfControls
    (one : ProfiledPhaseOneControl A firstBank)
    (two : ProfiledPhaseTwoControl A firstBank) :
    Option (ProfiledMatchedPhase A firstBank) := by
  classical
  exact match one, two with
    | .inl owner, .inl receiver =>
        if h : owner.1 = receiver.1 then
          some (.firstRight owner receiver h)
        else none
    | .inr (.inr (.inl owner)), .inr (.inr (.inl receiver)) =>
        if h : owner.1 = receiver.1 then
          some (.bankRight owner receiver h)
        else none
    | _, _ => none

/-- Left-oriented mirror. -/
noncomputable def profiledMatchedLeftOfControls
    (one : ProfiledPhaseOneControl A firstBank)
    (two : ProfiledPhaseTwoControl A firstBank) :
    Option (ProfiledMatchedPhase A firstBank) := by
  classical
  exact match one, two with
    | .inr (.inl receiver), .inr (.inl owner) =>
        if h : receiver.1 = owner.1 then
          some (.firstLeft receiver owner h)
        else none
    | .inr (.inr (.inr receiver)), .inr (.inr (.inr owner)) =>
        if h : receiver.1 = owner.1 then
          some (.bankLeft receiver owner h)
        else none
    | _, _ => none

@[simp] theorem profiledMatchedRightOfControls_firstRight
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (h : owner.1 = receiver.1) :
    profiledMatchedRightOfControls A firstBank (.inl owner) (.inl receiver) =
      some (.firstRight owner receiver h) := by
  classical
  simp [profiledMatchedRightOfControls, h]

@[simp] theorem profiledMatchedRightOfControls_bankRight
    (owner : ProfiledBankRightOwnerControl A)
    (receiver : ProfiledBankRightReceiverControl A)
    (h : owner.1 = receiver.1) :
    profiledMatchedRightOfControls A firstBank
        (.inr (.inr (.inl owner))) (.inr (.inr (.inl receiver))) =
      some (.bankRight owner receiver h) := by
  classical
  simp [profiledMatchedRightOfControls, h]

@[simp] theorem profiledMatchedLeftOfControls_firstLeft
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (h : receiver.1 = owner.1) :
    profiledMatchedLeftOfControls A firstBank
        (.inr (.inl receiver)) (.inr (.inl owner)) =
      some (.firstLeft receiver owner h) := by
  classical
  simp [profiledMatchedLeftOfControls, h]

@[simp] theorem profiledMatchedLeftOfControls_bankLeft
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A)
    (h : receiver.1 = owner.1) :
    profiledMatchedLeftOfControls A firstBank
        (.inr (.inr (.inr receiver))) (.inr (.inr (.inr owner))) =
      some (.bankLeft receiver owner h) := by
  classical
  simp [profiledMatchedLeftOfControls, h]

/-! ## Strict no-receive steps -/

/-- Process one's no-receive operation.  In the two-process graph model this
means that process one is the right owner.  A left receiver therefore uses
its staged close to enter the right bank. -/
noncomputable def profiledPostNoRecvOne
    (one : ProfiledPhaseOneControl A firstBank) (input : In₁) :
    Out₁ × Option (ProfiledPhaseOneControl A firstBank) :=
  match one with
  | .inl owner =>
      let next := stepProfiledGuardedFirstRightOwner A firstBank owner input
      (next.1, some (.inl next.2))
  | .inr (.inl receiver) =>
      let next := switchProfiledFirstLeftReceiverToBankRightOwner A receiver
        input
      (next.1, next.2.map fun owner => .inr (.inr (.inl owner)))
  | .inr (.inr (.inl owner)) =>
      let next := stepProfiledBankRightOwner A owner input
      (next.1, some (.inr (.inr (.inl next.2))))
  | .inr (.inr (.inr receiver)) =>
      let next := switchProfiledBankLeftReceiverToBankRightOwner A receiver
        input
      (next.1, next.2.map fun owner => .inr (.inr (.inl owner)))

/-- Process-two mirror. -/
noncomputable def profiledPostNoRecvTwo
    (two : ProfiledPhaseTwoControl A firstBank) (input : In₂) :
    Out₂ × Option (ProfiledPhaseTwoControl A firstBank) :=
  match two with
  | .inl receiver =>
      let next := switchProfiledFirstRightReceiverToBankLeftOwner A receiver
        input
      (next.1, next.2.map fun owner => .inr (.inr (.inr owner)))
  | .inr (.inl owner) =>
      let next := stepProfiledGuardedFirstLeftOwner A firstBank owner input
      (next.1, some (.inr (.inl next.2)))
  | .inr (.inr (.inl receiver)) =>
      let next := switchProfiledBankRightReceiverToBankLeftOwner A receiver
        input
      (next.1, next.2.map fun owner => .inr (.inr (.inr owner)))
  | .inr (.inr (.inr owner)) =>
      let next := stepProfiledBankLeftOwner A owner input
      (next.1, some (.inr (.inr (.inr next.2))))

/-! ## Receive-entry into the two-candidate carrier -/

/-- A received matched right pair enters the overlap carrier.  The returned
Boolean is the retained right anchor, not the current graph. -/
noncomputable def profiledPostRecvFromRight
    (one : ProfiledPhaseOneControl A firstBank)
    (two : ProfiledPhaseTwoControl A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalOverlapOne A firstBank ×
        ProfiledOperationalOverlapTwo A firstBank) :=
  match profiledMatchedRightOfControls A firstBank one two with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.enterBothFromRight A firstBank move
      (next.1, next.2.map fun candidates =>
        ((false, candidates.oneControl A firstBank),
          (false, candidates.twoControl A firstBank)))

/-- Left-oriented mirror. -/
noncomputable def profiledPostRecvFromLeft
    (one : ProfiledPhaseOneControl A firstBank)
    (two : ProfiledPhaseTwoControl A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalOverlapOne A firstBank ×
        ProfiledOperationalOverlapTwo A firstBank) :=
  match profiledMatchedLeftOfControls A firstBank one two with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.enterBothFromLeft A firstBank move
      (next.1, next.2.map fun candidates =>
        ((true, candidates.oneControl A firstBank),
          (true, candidates.twoControl A firstBank)))

/-! ## The closed recurrent operational step -/

/-- Recurrent local carrier for process one: either a resolved strict shadow
or the two projections retained after a receive. -/
abbrev ProfiledOperationalPostOne :=
  ProfiledPhaseOneControl A firstBank ⊕
    ProfiledOperationalOverlapOne A firstBank

/-- Process-two mirror. -/
abbrev ProfiledOperationalPostTwo :=
  ProfiledPhaseTwoControl A firstBank ⊕
    ProfiledOperationalOverlapTwo A firstBank

/-- Reassemble the proof-only candidate pair after the two finite overlap
summaries meet at a receive. -/
noncomputable def profiledBothOfOverlapControls
    (one : ProfiledOperationalOverlapOne A firstBank)
    (two : ProfiledOperationalOverlapTwo A firstBank) :
    Option (ProfiledBothCandidates A firstBank) := by
  classical
  exact if hanchor : one.1 = two.1 then
    match profiledMatchedRightOfControls A firstBank one.2.1 two.2.1,
        profiledMatchedLeftOfControls A firstBank one.2.2 two.2.2 with
    | some right, some left =>
        if hright : right.IsRight then
          if hleft : left.IsLeft then
            some ⟨right, left, hright, hleft⟩
          else none
        else none
    | _, _ => none
  else none

/-- Package an overlap result as the recurrent operational carrier. -/
def profiledOperationalPostOfCandidates
    (anchor : Bool) (candidates : ProfiledBothCandidates A firstBank) :
    ProfiledOperationalPostOne A firstBank ×
      ProfiledOperationalPostTwo A firstBank :=
  (.inr (anchor, candidates.oneControl A firstBank),
    .inr (anchor, candidates.twoControl A firstBank))

/-- Enter from a right matched pair and package the result. -/
noncomputable def profiledOperationalPostRecvRight
    (one : ProfiledPhaseOneControl A firstBank)
    (two : ProfiledPhaseTwoControl A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalPostOne A firstBank ×
        ProfiledOperationalPostTwo A firstBank) :=
  let next := profiledPostRecvFromRight A firstBank one two move
  (next.1, next.2.map fun pair => (.inr pair.1, .inr pair.2))

/-- Left matched mirror. -/
noncomputable def profiledOperationalPostRecvLeft
    (one : ProfiledPhaseOneControl A firstBank)
    (two : ProfiledPhaseTwoControl A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalPostOne A firstBank ×
        ProfiledOperationalPostTwo A firstBank) :=
  let next := profiledPostRecvFromLeft A firstBank one two move
  (next.1, next.2.map fun pair => (.inr pair.1, .inr pair.2))

/-- Repeat a synchronizing round from two overlap summaries.  The common
past anchor chooses which old shadow is continued and which one is refreshed.
The anchor is history, not an observation of the current graph. -/
noncomputable def profiledOperationalPostRecvOverlap
    (one : ProfiledOperationalOverlapOne A firstBank)
    (two : ProfiledOperationalOverlapTwo A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalPostOne A firstBank ×
        ProfiledOperationalPostTwo A firstBank) :=
  match profiledBothOfOverlapControls A firstBank one two with
  | none => ((default, default), none)
  | some candidates =>
      let next := if one.1 then
        candidates.repeatBothFromLeft A firstBank move
      else
        candidates.repeatBothFromRight A firstBank move
      (next.1, next.2.map fun c =>
        profiledOperationalPostOfCandidates A firstBank one.1 c)

/-- The complete recurrent receive operation.  Its four cases are exactly
the reachable local shapes: two resolved shadows, right-resolved/overlap,
overlap/left-resolved, and two overlaps. -/
noncomputable def profiledOperationalPostRecv
    (one : ProfiledOperationalPostOne A firstBank)
    (two : ProfiledOperationalPostTwo A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalPostOne A firstBank ×
        ProfiledOperationalPostTwo A firstBank) :=
  match one, two with
  | .inl one, .inl two =>
      match profiledMatchedRightOfControls A firstBank one two with
      | some _ => profiledOperationalPostRecvRight A firstBank one two move
      | none => profiledOperationalPostRecvLeft A firstBank one two move
  | .inl one, .inr two =>
      profiledOperationalPostRecvRight A firstBank one two.2.1 move
  | .inr one, .inl two =>
      profiledOperationalPostRecvLeft A firstBank one.2.2 two move
  | .inr one, .inr two =>
      profiledOperationalPostRecvOverlap A firstBank one two move

/-- Process one's complete recurrent no-receive operation.  In an overlap,
the retained past anchor selects the projection that is semantically current;
the process does not learn a current graph or leader bit. -/
noncomputable def profiledOperationalPostNoRecvOne
    (one : ProfiledOperationalPostOne A firstBank) (input : In₁) :
    Out₁ × Option (ProfiledOperationalPostOne A firstBank) :=
  let next := match one with
    | .inl one => profiledPostNoRecvOne A firstBank one input
    | .inr one => profiledPostNoRecvOne A firstBank
        (if one.1 then one.2.2 else one.2.1) input
  (next.1, next.2.map Sum.inl)

/-- Process-two mirror. -/
noncomputable def profiledOperationalPostNoRecvTwo
    (two : ProfiledOperationalPostTwo A firstBank) (input : In₂) :
    Out₂ × Option (ProfiledOperationalPostTwo A firstBank) :=
  let next := match two with
    | .inl two => profiledPostNoRecvTwo A firstBank two input
    | .inr two => profiledPostNoRecvTwo A firstBank
        (if two.1 then two.2.2 else two.2.1) input
  (next.1, next.2.map Sum.inl)

end

end

end DetParityAutomaton

end DistributedSynthesis
