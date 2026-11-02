/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGlobalBeliefMachine
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOverlapInvariant

/-!
# Reality of every reachable global profiled phase

The finite global machine is proof-only: its orientation is not exposed to
either process.  Nevertheless, from a real synchronized prefix, every global
step remains a concrete prefix of one of the four selected finite
controllers.  This excludes the totalization branches from all reachable
global beliefs without requiring the false exact-state alternating diamond.
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

/-- A right-oriented real phase remains real after any global round. -/
theorem isRealProfiledPhase_globalRightRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (hreal : IsRealProfiledPhase A firstBank state.phase)
    (hright : state.phase.IsRight)
    (round : EnvironmentRound In₁ In₂) :
    IsRealProfiledPhase A firstBank
      (profiledGlobalRightRound A firstBank state round).phase := by
  rcases isRealProfiledPhase_reverseRightToLeft A firstBank state.phase hreal
      hright (round.inputOne, round.inputTwo) state.receivedOne with
    ⟨reversed, hreversed, hrealReversed⟩
  cases hgraph : round.graph with
  | left =>
      simpa [profiledGlobalRightRound, hgraph, hreversed] using hrealReversed
  | right =>
      simpa [profiledGlobalRightRound, hgraph] using
        isRealProfiledPhase_continue A firstBank state.phase hreal
          (round.inputOne, round.inputTwo)
  | both =>
      simpa [profiledGlobalRightRound, hgraph] using
        isRealProfiledPhase_continue A firstBank state.phase hreal
          (round.inputOne, round.inputTwo)

/-- Left-oriented mirror. -/
theorem isRealProfiledPhase_globalLeftRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (hreal : IsRealProfiledPhase A firstBank state.phase)
    (hleft : state.phase.IsLeft)
    (round : EnvironmentRound In₁ In₂) :
    IsRealProfiledPhase A firstBank
      (profiledGlobalLeftRound A firstBank state round).phase := by
  rcases isRealProfiledPhase_reverseLeftToRight A firstBank state.phase hreal
      hleft (round.inputOne, round.inputTwo) state.receivedTwo with
    ⟨reversed, hreversed, hrealReversed⟩
  cases hgraph : round.graph with
  | left =>
      simpa [profiledGlobalLeftRound, hgraph] using
        isRealProfiledPhase_continue A firstBank state.phase hreal
          (round.inputOne, round.inputTwo)
  | right =>
      simpa [profiledGlobalLeftRound, hgraph, hreversed] using hrealReversed
  | both =>
      simpa [profiledGlobalLeftRound, hgraph] using
        isRealProfiledPhase_continue A firstBank state.phase hreal
          (round.inputOne, round.inputTwo)

/-- Every step of the global phase machine preserves reality. -/
theorem isRealProfiledPhase_globalRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (hreal : IsRealProfiledPhase A firstBank state.phase)
    (round : EnvironmentRound In₁ In₂) :
    IsRealProfiledPhase A firstBank
      (profiledGlobalPhaseRound A firstBank state round).phase := by
  cases hphase : state.phase with
  | firstRight owner receiver sameKey =>
      simpa [profiledGlobalPhaseRound, hphase] using
        isRealProfiledPhase_globalRightRound A firstBank state hreal
          (by simp [hphase, ProfiledMatchedPhase.IsRight]) round
  | firstLeft receiver owner sameKey =>
      simpa [profiledGlobalPhaseRound, hphase] using
        isRealProfiledPhase_globalLeftRound A firstBank state hreal
          (by simp [hphase, ProfiledMatchedPhase.IsLeft]) round
  | bankRight owner receiver sameKey =>
      simpa [profiledGlobalPhaseRound, hphase] using
        isRealProfiledPhase_globalRightRound A firstBank state hreal
          (by simp [hphase, ProfiledMatchedPhase.IsRight]) round
  | bankLeft receiver owner sameKey =>
      simpa [profiledGlobalPhaseRound, hphase] using
        isRealProfiledPhase_globalLeftRound A firstBank state hreal
          (by simp [hphase, ProfiledMatchedPhase.IsLeft]) round

/-- A successful right-to-left reversal is left-oriented. -/
theorem reverseRightToLeft_isLeft_of_eq_some
    (phase next : ProfiledMatchedPhase A firstBank)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseRightToLeft A firstBank move
      previouslyReceived).2 = some next) :
    next.IsLeft := by
  cases phase with
  | firstRight owner receiver sameKey =>
      simp only [ProfiledMatchedPhase.reverseRightToLeft] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [ProfiledMatchedPhase.IsLeft]
      all_goals simp at hnext
  | firstLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.reverseRightToLeft] at hnext
  | bankRight owner receiver sameKey =>
      simp only [ProfiledMatchedPhase.reverseRightToLeft] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [ProfiledMatchedPhase.IsLeft]
      all_goals simp at hnext
  | bankLeft receiver owner sameKey =>
      simp [ProfiledMatchedPhase.reverseRightToLeft] at hnext

/-- A successful left-to-right reversal is right-oriented. -/
theorem reverseLeftToRight_isRight_of_eq_some
    (phase next : ProfiledMatchedPhase A firstBank)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (hnext : (phase.reverseLeftToRight A firstBank (move.2, move.1)
      previouslyReceived).2 = some next) :
    next.IsRight := by
  cases phase with
  | firstRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.reverseLeftToRight] at hnext
  | firstLeft receiver owner sameKey =>
      simp only [ProfiledMatchedPhase.reverseLeftToRight] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [ProfiledMatchedPhase.IsRight]
      all_goals simp at hnext
  | bankRight owner receiver sameKey =>
      simp [ProfiledMatchedPhase.reverseLeftToRight] at hnext
  | bankLeft receiver owner sameKey =>
      simp only [ProfiledMatchedPhase.reverseLeftToRight] at hnext
      split at hnext
      next hOne hTwo =>
        cases Option.some.inj hnext
        simp [ProfiledMatchedPhase.IsRight]
      all_goals simp at hnext

/-- Entering an ambiguous round from a real right phase always produces two
real candidates. -/
theorem exists_real_candidates_enterBothFromRight
    (phase : ProfiledMatchedPhase A firstBank)
    (hreal : IsRealProfiledPhase A firstBank phase)
    (hright : phase.IsRight) (move : In₁ × In₂) :
    ∃ candidates,
      (phase.enterBothFromRight A firstBank move).2 = some candidates ∧
      IsRealProfiledPhase A firstBank candidates.right ∧
      IsRealProfiledPhase A firstBank candidates.left := by
  obtain ⟨left, hleft, hrealLeft⟩ :=
    isRealProfiledPhase_reverseRightToLeft A firstBank phase hreal hright move
      false
  have horientLeft : left.IsLeft :=
    reverseRightToLeft_isLeft_of_eq_some A firstBank phase left move false hleft
  have horientRight : (phase.continue A firstBank move).2.IsRight :=
    phase.continue_isRight A firstBank move hright
  let candidates : ProfiledBothCandidates A firstBank :=
    ⟨(phase.continue A firstBank move).2, left, horientRight, horientLeft⟩
  refine ⟨candidates, ?_,
    isRealProfiledPhase_continue A firstBank phase hreal move, hrealLeft⟩
  simp [ProfiledMatchedPhase.enterBothFromRight, hleft, horientRight,
    horientLeft, candidates]

/-- Left-oriented mirror. -/
theorem exists_real_candidates_enterBothFromLeft
    (phase : ProfiledMatchedPhase A firstBank)
    (hreal : IsRealProfiledPhase A firstBank phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂) :
    ∃ candidates,
      (phase.enterBothFromLeft A firstBank move).2 = some candidates ∧
      IsRealProfiledPhase A firstBank candidates.right ∧
      IsRealProfiledPhase A firstBank candidates.left := by
  obtain ⟨right, hright, hrealRight⟩ :=
    isRealProfiledPhase_reverseLeftToRight A firstBank phase hreal hleft move
      false
  have horientRight : right.IsRight :=
    reverseLeftToRight_isRight_of_eq_some A firstBank phase right move false
      hright
  have horientLeft : (phase.continue A firstBank move).2.IsLeft :=
    phase.continue_isLeft A firstBank move hleft
  let candidates : ProfiledBothCandidates A firstBank :=
    ⟨right, (phase.continue A firstBank move).2, horientRight, horientLeft⟩
  refine ⟨candidates, ?_, hrealRight,
    isRealProfiledPhase_continue A firstBank phase hreal move⟩
  simp [ProfiledMatchedPhase.enterBothFromLeft, hright, horientRight,
    horientLeft, candidates]

/-- Consecutive synchronization preserves real candidates for either retained
past anchor. -/
theorem exists_real_candidates_repeatBoth
    (anchor : Bool) (candidates : ProfiledBothCandidates A firstBank)
    (hrealRight : IsRealProfiledPhase A firstBank candidates.right)
    (hrealLeft : IsRealProfiledPhase A firstBank candidates.left)
    (move : In₁ × In₂) :
    ∃ next,
      (if anchor then candidates.repeatBothFromLeft A firstBank move
        else candidates.repeatBothFromRight A firstBank move).2 = some next ∧
      IsRealProfiledPhase A firstBank next.right ∧
      IsRealProfiledPhase A firstBank next.left := by
  cases anchor with
  | false =>
      simpa [ProfiledBothCandidates.repeatBothFromRight] using
        exists_real_candidates_enterBothFromRight A firstBank candidates.right
          hrealRight candidates.right_oriented move
  | true =>
      simpa [ProfiledBothCandidates.repeatBothFromLeft] using
        exists_real_candidates_enterBothFromLeft A firstBank candidates.left
          hrealLeft candidates.left_oriented move

/-- Reality along an arbitrary concrete environment prefix. -/
theorem isRealProfiledPhase_foldl_globalRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (hreal : IsRealProfiledPhase A firstBank state.phase)
    (rounds : List (EnvironmentRound In₁ In₂)) :
    IsRealProfiledPhase A firstBank
      (rounds.foldl (profiledGlobalPhaseRound A firstBank) state).phase := by
  induction rounds generalizing state with
  | nil => simpa using hreal
  | cons round rounds ih =>
      simp only [List.foldl_cons]
      exact ih _ (isRealProfiledPhase_globalRound A firstBank state hreal round)

end

end

end DetParityAutomaton

end DistributedSynthesis
