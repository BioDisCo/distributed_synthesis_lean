/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalPairClosure

/-!
# Proof-only invariant for the end-to-end recurrent carrier

The executable carrier stores only local projections.  This five-shape type
reassembles them in the correctness proof.  In particular it is not runtime
state and gives neither process an orientation or strict-leader signal.

The receive theorem below isolates the only remaining premise needed to rule
out totalization: the selected controller transition has staged a successor.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-- The five jointly reachable shapes of the two local post-initial states. -/
inductive EndToEndOperationalPostShape where
  | resolvedRight (phase : EndToEndMatchedPhase A package)
      (oriented : phase.IsRight)
  | resolvedLeft (phase : EndToEndMatchedPhase A package)
      (oriented : phase.IsLeft)
  | mixedRight (anchor : Bool)
      (candidates : EndToEndBothCandidates A package)
  | mixedLeft (anchor : Bool)
      (candidates : EndToEndBothCandidates A package)
  | overlap (anchor : Bool)
      (candidates : EndToEndBothCandidates A package)

def EndToEndOperationalPostShape.oneControl :
    EndToEndOperationalPostShape A package →
      EndToEndOperationalPostOne A package
  | .resolvedRight phase _ => .inl phase.oneControl
  | .resolvedLeft phase _ => .inl phase.oneControl
  | .mixedRight _ candidates => .inl candidates.right.oneControl
  | .mixedLeft anchor candidates =>
      .inr (anchor, candidates.oneControl A package)
  | .overlap anchor candidates =>
      .inr (anchor, candidates.oneControl A package)

def EndToEndOperationalPostShape.twoControl :
    EndToEndOperationalPostShape A package →
      EndToEndOperationalPostTwo A package
  | .resolvedRight phase _ => .inl phase.twoControl
  | .resolvedLeft phase _ => .inl phase.twoControl
  | .mixedRight anchor candidates =>
      .inr (anchor, candidates.twoControl A package)
  | .mixedLeft _ candidates => .inl candidates.left.twoControl
  | .overlap anchor candidates =>
      .inr (anchor, candidates.twoControl A package)

/-- The successful-staging premise at a synchronized receive. -/
def EndToEndOperationalPostShape.ReceiveReady
    (shape : EndToEndOperationalPostShape A package)
    (move : In₁ × In₂) : Prop :=
  match shape with
  | .resolvedRight phase _ =>
      (phase.enterBothFromRight A package move).2.isSome
  | .resolvedLeft phase _ =>
      (phase.enterBothFromLeft A package move).2.isSome
  | .mixedRight _ candidates =>
      (candidates.right.enterBothFromRight A package move).2.isSome
  | .mixedLeft _ candidates =>
      (candidates.left.enterBothFromLeft A package move).2.isSome
  | .overlap anchor candidates =>
      (if anchor then candidates.repeatBothFromLeft A package move
        else candidates.repeatBothFromRight A package move).2.isSome

/-- A ready synchronized receive is genuine and returns another overlap
shape.  Therefore the executable fallback is unreachable on such a step. -/
theorem endToEndOperationalPostRecv_shape
    (shape : EndToEndOperationalPostShape A package)
    (move : In₁ × In₂) (hready : shape.ReceiveReady A package move) :
    ∃ (output : Out₁ × Out₂)
      (next : EndToEndOperationalPostShape A package),
      endToEndOperationalPostRecv A package shape.oneControl
          shape.twoControl move =
        (output, some (next.oneControl, next.twoControl)) := by
  classical
  cases shape with
  | resolvedRight phase oriented =>
      simp only [EndToEndOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨candidates, hnext⟩
      refine ⟨(phase.enterBothFromRight A package move).1,
        .overlap false candidates, ?_⟩
      simpa [EndToEndOperationalPostShape.oneControl,
        EndToEndOperationalPostShape.twoControl,
        endToEndOperationalPostOfCandidates] using
        (endToEndOperationalPostRecv_of_resolvedRight A package phase
          oriented move candidates hnext)
  | resolvedLeft phase oriented =>
      simp only [EndToEndOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨candidates, hnext⟩
      refine ⟨(phase.enterBothFromLeft A package move).1,
        .overlap true candidates, ?_⟩
      simpa [EndToEndOperationalPostShape.oneControl,
        EndToEndOperationalPostShape.twoControl,
        endToEndOperationalPostOfCandidates] using
        (endToEndOperationalPostRecv_of_resolvedLeft A package phase
          oriented move candidates hnext)
  | mixedRight anchor candidates =>
      simp only [EndToEndOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨next, hnext⟩
      refine ⟨(candidates.right.enterBothFromRight A package move).1,
        .overlap false next, ?_⟩
      simpa [EndToEndOperationalPostShape.oneControl,
        EndToEndOperationalPostShape.twoControl,
        endToEndOperationalPostOfCandidates] using
        (endToEndOperationalPostRecv_of_mixedRight A package anchor
          candidates next move hnext)
  | mixedLeft anchor candidates =>
      simp only [EndToEndOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨next, hnext⟩
      refine ⟨(candidates.left.enterBothFromLeft A package move).1,
        .overlap true next, ?_⟩
      simpa [EndToEndOperationalPostShape.oneControl,
        EndToEndOperationalPostShape.twoControl,
        endToEndOperationalPostOfCandidates] using
        (endToEndOperationalPostRecv_of_mixedLeft A package anchor
          candidates next move hnext)
  | overlap anchor candidates =>
      simp only [EndToEndOperationalPostShape.ReceiveReady,
        Option.isSome_iff_exists] at hready
      rcases hready with ⟨next, hnext⟩
      refine ⟨(if anchor then
          (candidates.repeatBothFromLeft A package move).1
        else (candidates.repeatBothFromRight A package move).1),
        EndToEndOperationalPostShape.overlap anchor next, ?_⟩
      cases anchor <;>
        simpa [EndToEndOperationalPostShape.oneControl,
          EndToEndOperationalPostShape.twoControl,
          endToEndOperationalPostRecv,
          endToEndOperationalPostOfCandidates] using
          (endToEndOperationalPostRecvOverlap_of_candidates A package _
            candidates next move hnext)

end

end DetParityAutomaton

end DistributedSynthesis
