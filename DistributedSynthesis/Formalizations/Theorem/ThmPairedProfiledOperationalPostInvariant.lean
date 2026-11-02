/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalPairClosure

/-!
# Proof-only invariant for recurrent operational pairs

The two local summaries can be jointly in five reachable shapes.  This
inductive type exists only in the correctness proof; its constructor is not
available to either process.  The receive-closure theorem below proves that
all five shapes reconstruct a genuine phase/candidate pair and hence avoid
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

/-- The five joint shapes induced by two genuinely local carriers. -/
inductive ProfiledOperationalPostShape where
  | resolvedRight (phase : ProfiledMatchedPhase A firstBank)
      (oriented : phase.IsRight)
  | resolvedLeft (phase : ProfiledMatchedPhase A firstBank)
      (oriented : phase.IsLeft)
  | mixedRight (anchor : Bool)
      (candidates : ProfiledBothCandidates A firstBank)
  | mixedLeft (anchor : Bool)
      (candidates : ProfiledBothCandidates A firstBank)
  | overlap (anchor : Bool)
      (candidates : ProfiledBothCandidates A firstBank)

/-- Process-one projection of the proof-only joint shape. -/
def ProfiledOperationalPostShape.oneControl :
    ProfiledOperationalPostShape A firstBank →
      ProfiledOperationalPostOne A firstBank
  | .resolvedRight phase _ => .inl phase.oneControl
  | .resolvedLeft phase _ => .inl phase.oneControl
  | .mixedRight _ candidates => .inl candidates.right.oneControl
  | .mixedLeft anchor candidates =>
      .inr (anchor, candidates.oneControl A firstBank)
  | .overlap anchor candidates =>
      .inr (anchor, candidates.oneControl A firstBank)

/-- Process-two projection. -/
def ProfiledOperationalPostShape.twoControl :
    ProfiledOperationalPostShape A firstBank →
      ProfiledOperationalPostTwo A firstBank
  | .resolvedRight phase _ => .inl phase.twoControl
  | .resolvedLeft phase _ => .inl phase.twoControl
  | .mixedRight anchor candidates =>
      .inr (anchor, candidates.twoControl A firstBank)
  | .mixedLeft _ candidates => .inl candidates.left.twoControl
  | .overlap anchor candidates =>
      .inr (anchor, candidates.twoControl A firstBank)

/-- The only semantic premise needed at a receive: a real resolved anchor has
a staged successor.  Full overlaps need no premise because both already
activated candidates advance totality. -/
def ProfiledOperationalPostShape.ReceiveReady
    (shape : ProfiledOperationalPostShape A firstBank)
    (move : In₁ × In₂) : Prop :=
  match shape with
  | .resolvedRight phase _ =>
      (phase.enterBothFromRight A firstBank move).2.isSome
  | .resolvedLeft phase _ =>
      (phase.enterBothFromLeft A firstBank move).2.isSome
  | .mixedRight _ candidates =>
      (candidates.right.enterBothFromRight A firstBank move).2.isSome
  | .mixedLeft _ candidates =>
      (candidates.left.enterBothFromLeft A firstBank move).2.isSome
  | .overlap anchor candidates =>
      (if anchor then candidates.repeatBothFromLeft A firstBank move
        else candidates.repeatBothFromRight A firstBank move).2.isSome

/-- Every ready recurrent shape takes a genuine receive transition.  The
returned local controls are again projections of one proof-only shape, so the
fallback pair is unreachable. -/
theorem profiledOperationalPostRecv_shape
    (shape : ProfiledOperationalPostShape A firstBank)
    (move : In₁ × In₂) (hready : shape.ReceiveReady A firstBank move) :
    ∃ (output : Out₁ × Out₂)
      (next : ProfiledOperationalPostShape A firstBank),
      profiledOperationalPostRecv A firstBank shape.oneControl
          shape.twoControl move =
        (output, some (next.oneControl, next.twoControl)) := by
  classical
  cases shape with
  | resolvedRight phase oriented =>
      simp only [ProfiledOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨candidates, hnext⟩
      refine ⟨(phase.enterBothFromRight A firstBank move).1,
        .overlap false candidates, ?_⟩
      simpa [ProfiledOperationalPostShape.oneControl,
        ProfiledOperationalPostShape.twoControl,
        profiledOperationalPostOfCandidates] using
        (profiledOperationalPostRecv_of_resolvedRight A firstBank phase
          oriented move candidates hnext)
  | resolvedLeft phase oriented =>
      simp only [ProfiledOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨candidates, hnext⟩
      refine ⟨(phase.enterBothFromLeft A firstBank move).1,
        .overlap true candidates, ?_⟩
      simpa [ProfiledOperationalPostShape.oneControl,
        ProfiledOperationalPostShape.twoControl,
        profiledOperationalPostOfCandidates] using
        (profiledOperationalPostRecv_of_resolvedLeft A firstBank phase
          oriented move candidates hnext)
  | mixedRight anchor candidates =>
      simp only [ProfiledOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨next, hnext⟩
      refine ⟨(candidates.right.enterBothFromRight A firstBank move).1,
        .overlap false next, ?_⟩
      simpa [ProfiledOperationalPostShape.oneControl,
        ProfiledOperationalPostShape.twoControl,
        profiledOperationalPostOfCandidates] using
        (profiledOperationalPostRecv_of_mixedRight A firstBank anchor
          candidates next move hnext)
  | mixedLeft anchor candidates =>
      simp only [ProfiledOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨next, hnext⟩
      refine ⟨(candidates.left.enterBothFromLeft A firstBank move).1,
        .overlap true next, ?_⟩
      simpa [ProfiledOperationalPostShape.oneControl,
        ProfiledOperationalPostShape.twoControl,
        profiledOperationalPostOfCandidates] using
        (profiledOperationalPostRecv_of_mixedLeft A firstBank anchor
          candidates next move hnext)
  | overlap anchor candidates =>
      simp only [ProfiledOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨next, hnext⟩
      refine ⟨(if anchor then
          (candidates.repeatBothFromLeft A firstBank move).1
        else (candidates.repeatBothFromRight A firstBank move).1),
        ProfiledOperationalPostShape.overlap anchor next, ?_⟩
      cases anchor <;>
        simpa [ProfiledOperationalPostShape.oneControl,
          ProfiledOperationalPostShape.twoControl,
          profiledOperationalPostRecv,
          profiledOperationalPostOfCandidates] using
          (profiledOperationalPostRecvOverlap_of_candidates A firstBank _
            candidates next move hnext)

end

end

end DetParityAutomaton

end DistributedSynthesis
