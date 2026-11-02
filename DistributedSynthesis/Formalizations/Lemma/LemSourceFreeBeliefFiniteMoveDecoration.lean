/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Finite decoration of an occurrence-sensitive source-free move

A semantic tree is often rationalized first and only later asked to choose a
finite operational witness.  At a hidden cross anchor that timing is too
late: independently reconstructing a witness from the public child code can
select an unrelated semantic occurrence.

This file records the safe timing rule generically.  A finite annotation is
attached to each semantic move *before* the one outer rationalization.  The
public child-code transition ignores the annotation, while a source-free
finite predicate checks that it is an admissible witness for that move.  The
existing code-parity certificate then lifts without changing either its T1
equation or any branch word.
-/

namespace DistributedSynthesis

universe u v w z a b

section

variable {Direction : Type u} {Move : Type v} {Extra : Type b}
variable {BeliefCode : Type z}
variable [Fintype BeliefCode]

/-- Attach one finite operational witness to the move at every exact semantic
occurrence.  Semantic states and their transition are unchanged. -/
def SourceFreeBeliefSemanticTree.decorateMove
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (extra : raw.Semantic → Extra) :
    SourceFreeBeliefSemanticTree.{u, max v b, z, a}
      Direction (Move × Extra) BeliefCode where
  Semantic := raw.Semantic
  initial := raw.initial
  step := raw.step
  code := raw.code
  move := fun state ↦ (raw.move state, extra state)

/-- The source-free finite validity relation for a decorated move. -/
def sourceFreeBeliefDecoratedValid
    (Valid : BeliefCode → Move → Prop)
    (ExtraValid : BeliefCode → Move → Extra → Prop)
    (code : BeliefCode) (move : Move × Extra) : Prop :=
  Valid code move.1 ∧ ExtraValid code move.1 move.2

/-- The annotation is operational payload only; the public belief successor
remains the already checked source-free transition. -/
def sourceFreeBeliefDecoratedNext
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : BeliefCode) (move : Move × Extra) (direction : Direction) :
    BeliefCode :=
  next code move.1 direction

namespace SourceFreeBeliefSemanticTree

variable
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (extra : raw.Semantic → Extra)

omit [Fintype BeliefCode] in
@[simp] theorem decorateMove_stateAt (node : TreeNode Direction) :
    (raw.decorateMove extra).stateAt node = raw.stateAt node :=
  rfl

omit [Fintype BeliefCode] in
@[simp] theorem decorateMove_childCodeWord
    (branch : Nat → Direction) :
    (raw.decorateMove extra).childCodeWord branch =
      raw.childCodeWord branch :=
  rfl

end SourceFreeBeliefSemanticTree

omit [Fintype BeliefCode] in
/-- A code-parity certificate survives any finite pre-rational annotation
whose admissibility is proved at the same semantic occurrence. -/
theorem SourceFreeBeliefCodeParityCertificate.decorateMove
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid
      next raw)
    (extra : raw.Semantic → Extra)
    (ExtraValid : BeliefCode → Move → Extra → Prop)
    (hextra : ∀ node : TreeNode Direction,
      ExtraValid (raw.code (raw.stateAt node))
        (raw.move (raw.stateAt node)) (extra (raw.stateAt node))) :
    SourceFreeBeliefCodeParityCertificate D initialCode
      (sourceFreeBeliefDecoratedValid Valid ExtraValid)
      (sourceFreeBeliefDecoratedNext next) (raw.decorateMove extra) where
  initial_code := certificate.initial_code
  valid := by
    intro node
    exact ⟨certificate.valid node, hextra node⟩
  next_code := by
    intro node direction
    exact certificate.next_code node direction
  accepts := by
    intro branch
    exact certificate.accepts branch

end

end DistributedSynthesis
