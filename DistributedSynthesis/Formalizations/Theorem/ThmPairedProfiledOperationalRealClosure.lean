/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGlobalRealInvariant
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalPostInvariant

/-!
# Real closure of the recurrent operational pair

This is the semantic strengthening of the five-shape reconstruction theorem.
Every proof-only phase represented by a reachable joint shape is a concrete
prefix of a selected finite controller.  Consequently every receive,
including repeated `both`, produces a genuine next overlap and never reaches
the totalization fallback.
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

/-- Both shadows of an overlap are real selected-controller prefixes. -/
def ProfiledBothCandidates.Real
    (candidates : ProfiledBothCandidates A firstBank) : Prop :=
  IsRealProfiledPhase A firstBank candidates.right ∧
    IsRealProfiledPhase A firstBank candidates.left

/-- Semantic reachability predicate for the five joint operational shapes. -/
def ProfiledOperationalPostShape.Real :
    ProfiledOperationalPostShape A firstBank → Prop
  | .resolvedRight phase _ => IsRealProfiledPhase A firstBank phase
  | .resolvedLeft phase _ => IsRealProfiledPhase A firstBank phase
  | .mixedRight _ candidates => candidates.Real A firstBank
  | .mixedLeft _ candidates => candidates.Real A firstBank
  | .overlap _ candidates => candidates.Real A firstBank

/-- The refreshed left shadow of a right entry is exactly the successful
right-to-left reversal. -/
theorem enterBothFromRight_candidate_left
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂)
    (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromRight A firstBank move).2 =
      some candidates) :
    (phase.reverseRightToLeft A firstBank move false).2 =
      some candidates.left := by
  unfold ProfiledMatchedPhase.enterBothFromRight at hnext
  dsimp only at hnext
  generalize hleft :
      (phase.reverseRightToLeft A firstBank move false).2 = left at hnext
  cases left with
  | none => simp [hleft] at hnext
  | some left =>
      by_cases hright : (phase.continue A firstBank move).2.IsRight
      · by_cases horiented : left.IsLeft
        · simp [hleft, hright, horiented] at hnext
          cases hnext
          rfl
        · simp [hleft, hright, horiented] at hnext
      · simp [hleft, hright] at hnext

/-- Right-shadow mirror for a left entry. -/
theorem enterBothFromLeft_candidate_right
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂)
    (candidates : ProfiledBothCandidates A firstBank)
    (hnext : (phase.enterBothFromLeft A firstBank move).2 =
      some candidates) :
    (phase.reverseLeftToRight A firstBank (move.2, move.1) false).2 =
      some candidates.right := by
  unfold ProfiledMatchedPhase.enterBothFromLeft at hnext
  dsimp only at hnext
  generalize hright :
      (phase.reverseLeftToRight A firstBank (move.2, move.1) false).2 =
        right at hnext
  cases right with
  | none => simp [hright] at hnext
  | some right =>
      by_cases horiented : right.IsRight
      · by_cases hleft : (phase.continue A firstBank move).2.IsLeft
        · simp [hright, horiented, hleft] at hnext
          cases hnext
          rfl
        · simp [hright, horiented, hleft] at hnext
      · simp [hright, horiented] at hnext

/-- A real shape always satisfies the receive-readiness premise. -/
theorem ProfiledOperationalPostShape.receiveReady_of_real
    (shape : ProfiledOperationalPostShape A firstBank)
    (hreal : shape.Real A firstBank) (move : In₁ × In₂) :
    shape.ReceiveReady A firstBank move := by
  cases shape with
  | resolvedRight phase oriented =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_candidates_enterBothFromRight A firstBank phase hreal
          oriented move
      simp [ProfiledOperationalPostShape.ReceiveReady, hnext]
  | resolvedLeft phase oriented =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_candidates_enterBothFromLeft A firstBank phase hreal
          oriented move
      simp [ProfiledOperationalPostShape.ReceiveReady, hnext]
  | mixedRight anchor candidates =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_candidates_enterBothFromRight A firstBank candidates.right
          hreal.1 candidates.right_oriented move
      simp [ProfiledOperationalPostShape.ReceiveReady, hnext]
  | mixedLeft anchor candidates =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_candidates_enterBothFromLeft A firstBank candidates.left
          hreal.2 candidates.left_oriented move
      simp [ProfiledOperationalPostShape.ReceiveReady, hnext]
  | overlap anchor candidates =>
      obtain ⟨next, hnext, _⟩ :=
        exists_real_candidates_repeatBoth A firstBank anchor candidates
          hreal.1 hreal.2 move
      simp [ProfiledOperationalPostShape.ReceiveReady, hnext]

/-- Every receive from a real recurrent joint shape returns another real
shape.  In particular the executable operation cannot take its fallback. -/
theorem profiledOperationalPostRecv_realShape
    (shape : ProfiledOperationalPostShape A firstBank)
    (hreal : shape.Real A firstBank) (move : In₁ × In₂) :
    ∃ (output : Out₁ × Out₂)
      (next : ProfiledOperationalPostShape A firstBank),
      profiledOperationalPostRecv A firstBank shape.oneControl
          shape.twoControl move =
        (output, some (next.oneControl, next.twoControl)) ∧
      next.Real A firstBank := by
  cases shape with
  | resolvedRight phase oriented =>
      obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
        exists_real_candidates_enterBothFromRight A firstBank phase hreal
          oriented move
      refine ⟨(phase.enterBothFromRight A firstBank move).1,
        .overlap false candidates, ?_, ?_⟩
      · simpa [ProfiledOperationalPostShape.oneControl,
          ProfiledOperationalPostShape.twoControl,
          profiledOperationalPostOfCandidates] using
          (profiledOperationalPostRecv_of_resolvedRight A firstBank phase
            oriented move candidates hcandidates)
      · exact ⟨hright, hleft⟩
  | resolvedLeft phase oriented =>
      obtain ⟨candidates, hcandidates, hright, hleft⟩ :=
        exists_real_candidates_enterBothFromLeft A firstBank phase hreal
          oriented move
      refine ⟨(phase.enterBothFromLeft A firstBank move).1,
        .overlap true candidates, ?_, ?_⟩
      · simpa [ProfiledOperationalPostShape.oneControl,
          ProfiledOperationalPostShape.twoControl,
          profiledOperationalPostOfCandidates] using
          (profiledOperationalPostRecv_of_resolvedLeft A firstBank phase
            oriented move candidates hcandidates)
      · exact ⟨hright, hleft⟩
  | mixedRight anchor candidates =>
      obtain ⟨fresh, hfresh, hright, hleft⟩ :=
        exists_real_candidates_enterBothFromRight A firstBank candidates.right
          hreal.1 candidates.right_oriented move
      refine ⟨(candidates.right.enterBothFromRight A firstBank move).1,
        .overlap false fresh, ?_, ?_⟩
      · simpa [ProfiledOperationalPostShape.oneControl,
          ProfiledOperationalPostShape.twoControl,
          profiledOperationalPostOfCandidates] using
          (profiledOperationalPostRecv_of_mixedRight A firstBank anchor
            candidates fresh move hfresh)
      · exact ⟨hright, hleft⟩
  | mixedLeft anchor candidates =>
      obtain ⟨fresh, hfresh, hright, hleft⟩ :=
        exists_real_candidates_enterBothFromLeft A firstBank candidates.left
          hreal.2 candidates.left_oriented move
      refine ⟨(candidates.left.enterBothFromLeft A firstBank move).1,
        .overlap true fresh, ?_, ?_⟩
      · simpa [ProfiledOperationalPostShape.oneControl,
          ProfiledOperationalPostShape.twoControl,
          profiledOperationalPostOfCandidates] using
          (profiledOperationalPostRecv_of_mixedLeft A firstBank anchor
            candidates fresh move hfresh)
      · exact ⟨hright, hleft⟩
  | overlap anchor candidates =>
      obtain ⟨fresh, hfresh, hright, hleft⟩ :=
        exists_real_candidates_repeatBoth A firstBank anchor candidates
          hreal.1 hreal.2 move
      refine ⟨(if anchor then
          candidates.repeatBothFromLeft A firstBank move
        else candidates.repeatBothFromRight A firstBank move).1,
        .overlap anchor fresh, ?_, ?_⟩
      · cases anchor <;>
          simpa [ProfiledOperationalPostShape.oneControl,
            ProfiledOperationalPostShape.twoControl,
            profiledOperationalPostRecv,
            profiledOperationalPostOfCandidates] using
            (profiledOperationalPostRecvOverlap_of_candidates A firstBank _
              candidates fresh move hfresh)
      · exact ⟨hright, hleft⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
