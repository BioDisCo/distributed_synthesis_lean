/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalAutomaton

/-!
# Reconstruction of the distributed profiled pair

The operational automaton stores only projections of the proof-level matched
phase (and, after a receive, projections of the two-candidate overlap).  This
file proves that when the projections meet at a later receive, the finite
decoders reconstruct exactly the latent proof object.  These are correctness
lemmas about the distributed pair; no process is given an orientation or a
strict-leader bit.
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

/-- A right-oriented proof phase is recovered exactly from its two finite
projections. -/
theorem profiledMatchedRightOfControls_of_phase
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsRight) :
    profiledMatchedRightOfControls A firstBank phase.oneControl
        phase.twoControl = some phase := by
  classical
  cases phase with
  | firstRight owner receiver sameKey =>
      simp [profiledMatchedRightOfControls, ProfiledMatchedPhase.oneControl,
        ProfiledMatchedPhase.twoControl, sameKey]
  | firstLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.IsRight] at h
  | bankRight owner receiver sameKey =>
      simp [profiledMatchedRightOfControls, ProfiledMatchedPhase.oneControl,
        ProfiledMatchedPhase.twoControl, sameKey]
  | bankLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.IsRight] at h

/-- Left-oriented mirror. -/
theorem profiledMatchedLeftOfControls_of_phase
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft) :
    profiledMatchedLeftOfControls A firstBank phase.oneControl
        phase.twoControl = some phase := by
  classical
  cases phase with
  | firstRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.IsLeft] at h
  | firstLeft receiver owner sameKey =>
      simp [profiledMatchedLeftOfControls, ProfiledMatchedPhase.oneControl,
        ProfiledMatchedPhase.twoControl, sameKey]
  | bankRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.IsLeft] at h
  | bankLeft receiver owner sameKey =>
      simp [profiledMatchedLeftOfControls, ProfiledMatchedPhase.oneControl,
        ProfiledMatchedPhase.twoControl, sameKey]

/-- The two locally stored overlap projections reconstruct the exact common
candidate pair, independently of the retained anchor value. -/
theorem profiledBothOfOverlapControls_of_candidates
    (anchor : Bool) (candidates : ProfiledBothCandidates A firstBank) :
    profiledBothOfOverlapControls A firstBank
        (anchor, candidates.oneControl A firstBank)
        (anchor, candidates.twoControl A firstBank) = some candidates := by
  classical
  unfold profiledBothOfOverlapControls
  simp only [Prod.fst, Prod.snd, if_pos rfl,
    ProfiledBothCandidates.oneControl,
    ProfiledBothCandidates.twoControl]
  rw [profiledMatchedRightOfControls_of_phase A firstBank candidates.right
      candidates.right_oriented,
    profiledMatchedLeftOfControls_of_phase A firstBank candidates.left
      candidates.left_oriented]
  simp [candidates.right_oriented, candidates.left_oriented]

/-- Entering an overlap from a genuine right phase returns the exact
two-candidate projections and cannot take the fallback. -/
theorem profiledOperationalPostRecvRight_of_phase
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsRight)
    (move : In₁ × In₂) (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromRight A firstBank move).2 = some candidates) :
    profiledOperationalPostRecvRight A firstBank phase.oneControl
        phase.twoControl move =
      ((phase.enterBothFromRight A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank false
          candidates)) := by
  unfold profiledOperationalPostRecvRight profiledPostRecvFromRight
  rw [profiledMatchedRightOfControls_of_phase A firstBank phase h]
  simp [hnext, profiledOperationalPostOfCandidates]

/-- Left-oriented mirror. -/
theorem profiledOperationalPostRecvLeft_of_phase
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft)
    (move : In₁ × In₂) (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromLeft A firstBank move).2 = some candidates) :
    profiledOperationalPostRecvLeft A firstBank phase.oneControl
        phase.twoControl move =
      ((phase.enterBothFromLeft A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank true
          candidates)) := by
  unfold profiledOperationalPostRecvLeft profiledPostRecvFromLeft
  rw [profiledMatchedLeftOfControls_of_phase A firstBank phase h]
  simp [hnext, profiledOperationalPostOfCandidates]

/-- Consecutive receives from a genuine overlap reconstruct the pair and run
the anchored refresh exactly. -/
theorem profiledOperationalPostRecvOverlap_of_candidates
    (anchor : Bool) (candidates next : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂)
    (hnext : (if anchor then
        candidates.repeatBothFromLeft A firstBank move
      else candidates.repeatBothFromRight A firstBank move).2 = some next) :
    profiledOperationalPostRecvOverlap A firstBank
        (anchor, candidates.oneControl A firstBank)
        (anchor, candidates.twoControl A firstBank) move =
      ((if anchor then
          candidates.repeatBothFromLeft A firstBank move
        else candidates.repeatBothFromRight A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank anchor next)) := by
  unfold profiledOperationalPostRecvOverlap
  rw [profiledBothOfOverlapControls_of_candidates A firstBank anchor candidates]
  simp [hnext]

/-! ## The four recurrent receive shapes -/

/-- A left phase is not spuriously decoded as a right phase. -/
theorem profiledMatchedRightOfControls_eq_none_of_left
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft) :
    profiledMatchedRightOfControls A firstBank phase.oneControl
        phase.twoControl = none := by
  classical
  cases phase <;>
    simp_all [profiledMatchedRightOfControls, ProfiledMatchedPhase.oneControl,
      ProfiledMatchedPhase.twoControl, ProfiledMatchedPhase.IsLeft]

/-- A resolved right pair enters precisely the candidate overlap computed by
the proof phase. -/
theorem profiledOperationalPostRecv_of_resolvedRight
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsRight)
    (move : In₁ × In₂) (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromRight A firstBank move).2 = some candidates) :
    profiledOperationalPostRecv A firstBank (.inl phase.oneControl)
        (.inl phase.twoControl) move =
      ((phase.enterBothFromRight A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank false
          candidates)) := by
  simp only [profiledOperationalPostRecv]
  rw [profiledMatchedRightOfControls_of_phase A firstBank phase h]
  exact profiledOperationalPostRecvRight_of_phase A firstBank phase h move
    candidates hnext

/-- Resolved left mirror. -/
theorem profiledOperationalPostRecv_of_resolvedLeft
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft)
    (move : In₁ × In₂) (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromLeft A firstBank move).2 = some candidates) :
    profiledOperationalPostRecv A firstBank (.inl phase.oneControl)
        (.inl phase.twoControl) move =
      ((phase.enterBothFromLeft A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank true
          candidates)) := by
  simp only [profiledOperationalPostRecv]
  rw [profiledMatchedRightOfControls_eq_none_of_left A firstBank phase h]
  exact profiledOperationalPostRecvLeft_of_phase A firstBank phase h move
    candidates hnext

/-- If process one has resolved the right candidate while process two still
retains both projections, their next receive reconstructs the same right
phase. -/
theorem profiledOperationalPostRecv_of_mixedRight
    (anchor : Bool) (candidates next : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂)
    (hnext : (candidates.right.enterBothFromRight A firstBank move).2 =
      some next) :
    profiledOperationalPostRecv A firstBank
        (.inl candidates.right.oneControl)
        (.inr (anchor, candidates.twoControl A firstBank)) move =
      ((candidates.right.enterBothFromRight A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank false next)) := by
  unfold profiledOperationalPostRecv
  exact profiledOperationalPostRecvRight_of_phase A firstBank
    candidates.right candidates.right_oriented move next hnext

/-- Mixed-left mirror. -/
theorem profiledOperationalPostRecv_of_mixedLeft
    (anchor : Bool) (candidates next : ProfiledBothCandidates A firstBank)
    (move : In₁ × In₂)
    (hnext : (candidates.left.enterBothFromLeft A firstBank move).2 =
      some next) :
    profiledOperationalPostRecv A firstBank
        (.inr (anchor, candidates.oneControl A firstBank))
        (.inl candidates.left.twoControl) move =
      ((candidates.left.enterBothFromLeft A firstBank move).1,
        some (profiledOperationalPostOfCandidates A firstBank true next)) := by
  unfold profiledOperationalPostRecv
  exact profiledOperationalPostRecvLeft_of_phase A firstBank
    candidates.left candidates.left_oriented move next hnext

/-! ## Strict local resolutions -/

/-- Process one's no-receive table is exactly the process-one projection of
a right-oriented phase continuation. -/
theorem profiledPostNoRecvOne_of_rightPhase
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsRight)
    (input : In₁) (inputTwo : In₂) :
    profiledPostNoRecvOne A firstBank phase.oneControl input =
      ((phase.continue A firstBank (input, inputTwo)).1.1,
        some (phase.continue A firstBank (input, inputTwo)).2.oneControl) := by
  cases phase <;>
    simp_all [profiledPostNoRecvOne, ProfiledMatchedPhase.oneControl,
      ProfiledMatchedPhase.continue, ProfiledMatchedPhase.IsRight]

/-- Process-two mirror for a left-oriented continuation. -/
theorem profiledPostNoRecvTwo_of_leftPhase
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft)
    (inputOne : In₁) (input : In₂) :
    profiledPostNoRecvTwo A firstBank phase.twoControl input =
      ((phase.continue A firstBank (inputOne, input)).1.2,
        some (phase.continue A firstBank (inputOne, input)).2.twoControl) := by
  cases phase <;>
    simp_all [profiledPostNoRecvTwo, ProfiledMatchedPhase.twoControl,
      ProfiledMatchedPhase.continue, ProfiledMatchedPhase.IsLeft]

/-- The process-two no-receive branch of a right phase is exactly the owner
projection of the right-to-left reversal.  The receipt bit affects only the
new receiver at process one, so this equality holds for either proof-side
value. -/
theorem profiledPostNoRecvTwo_of_reverseRightToLeft
    (phase next : ProfiledMatchedPhase A firstBank) (h : phase.IsRight)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseRightToLeft A firstBank move
      previouslyReceived).2 = some next) :
    profiledPostNoRecvTwo A firstBank phase.twoControl move.2 =
      ((phase.reverseRightToLeft A firstBank move
          previouslyReceived).1.2,
        some next.twoControl) := by
  cases phase with
  | firstRight owner receiver sameKey =>
      simp only [ProfiledMatchedPhase.reverseRightToLeft,
        ProfiledMatchedPhase.twoControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [profiledPostNoRecvTwo, *]
      · simp at hnext
  | firstLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.IsRight] at h
  | bankRight owner receiver sameKey =>
      simp only [ProfiledMatchedPhase.reverseRightToLeft,
        ProfiledMatchedPhase.twoControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [profiledPostNoRecvTwo, *]
      · simp at hnext
  | bankLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.IsRight] at h

/-- Process-one mirror for a left-to-right reversal. -/
theorem profiledPostNoRecvOne_of_reverseLeftToRight
    (phase next : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseLeftToRight A firstBank (move.2, move.1)
      previouslyReceived).2 = some next) :
    profiledPostNoRecvOne A firstBank phase.oneControl move.1 =
      ((phase.reverseLeftToRight A firstBank (move.2, move.1)
          previouslyReceived).1.1,
        some next.oneControl) := by
  cases phase with
  | firstRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.IsLeft] at h
  | firstLeft receiver owner sameKey =>
      simp only [ProfiledMatchedPhase.reverseLeftToRight,
        ProfiledMatchedPhase.oneControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [profiledPostNoRecvOne, *]
      · simp at hnext
  | bankRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.IsLeft] at h
  | bankLeft receiver owner sameKey =>
      simp only [ProfiledMatchedPhase.reverseLeftToRight,
        ProfiledMatchedPhase.oneControl] at hnext ⊢
      split at hnext
      · cases Option.some.inj hnext
        simp [profiledPostNoRecvOne, *]
      · simp at hnext

/-! ## Candidate identification -/

/-- The right projection created by an entry is the ordinary continuation of
the old right phase. -/
theorem enterBothFromRight_candidate_right
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsRight)
    (move : In₁ × In₂) (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromRight A firstBank move).2 = some candidates) :
    candidates.right = (phase.continue A firstBank move).2 := by
  unfold ProfiledMatchedPhase.enterBothFromRight at hnext
  dsimp only at hnext
  generalize hleft :
      (phase.reverseRightToLeft A firstBank move false).2 = left at hnext
  cases left with
  | none => simp [hleft] at hnext
  | some left =>
      have hright := phase.continue_isRight A firstBank move h
      by_cases hleftOriented : left.IsLeft
      · simp [hleft, hright, hleftOriented] at hnext
        cases hnext
        rfl
      · simp [hleft, hright, hleftOriented] at hnext

/-- The left projection created by a left entry is its ordinary continuation. -/
theorem enterBothFromLeft_candidate_left
    (phase : ProfiledMatchedPhase A firstBank) (h : phase.IsLeft)
    (move : In₁ × In₂) (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromLeft A firstBank move).2 = some candidates) :
    candidates.left = (phase.continue A firstBank move).2 := by
  unfold ProfiledMatchedPhase.enterBothFromLeft at hnext
  dsimp only at hnext
  generalize hright :
      (phase.reverseLeftToRight A firstBank (move.2, move.1) false).2 =
        right at hnext
  cases right with
  | none => simp [hright] at hnext
  | some right =>
      have hleft := phase.continue_isLeft A firstBank move h
      by_cases hrightOriented : right.IsRight
      · simp [hright, hleft, hrightOriented] at hnext
        cases hnext
        rfl
      · simp [hright, hleft, hrightOriented] at hnext

end

end

end DetParityAutomaton

end DistributedSynthesis
