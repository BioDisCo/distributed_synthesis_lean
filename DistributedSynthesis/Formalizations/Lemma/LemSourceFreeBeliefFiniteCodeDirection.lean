/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Finite child-code directions for source-free semantic trees

When the objective automaton reads only the finite child belief code, the raw
direction of a source-free semantic tree need not remain the direction type of
the rationalized tree automaton.  At a fixed code and move, use the requested
child code as a finite tag and choose one raw direction realizing that code.
Unrealizable tags use an arbitrary fallback direction.

Every raw direction is represented by its actual child code.  Therefore the
finite-tag successor agrees with the raw successor on every real direction,
while every finite-tag branch expands to a genuine raw branch.  A raw
code-parity certificate consequently yields a finite-direction certificate
and hence a rational policy by the checked finite tree-automaton theorem.  No
arbitrary-direction rational-run hypothesis is used.
-/

namespace DistributedSynthesis

universe u v w z a

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode] [Nonempty Direction]

/-- Chosen raw representative of a requested finite child code.  If the tag
is outside the image of the raw successor, use an arbitrary raw direction. -/
noncomputable def sourceFreeBeliefRawDirectionOfChildCode
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : BeliefCode) (move : Move) (childCode : BeliefCode) : Direction := by
  classical
  exact if h : ∃ direction, next code move direction = childCode then
    Classical.choose h
  else Classical.choice inferInstance

omit [Fintype BeliefCode] in
/-- Every actual raw direction is represented exactly by the tag equal to its
own child code. -/
theorem sourceFreeBeliefRawDirectionOfChildCode_next_eq
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : BeliefCode) (move : Move) (direction : Direction) :
    next code move
        (sourceFreeBeliefRawDirectionOfChildCode next code move
          (next code move direction)) =
      next code move direction := by
  classical
  simp only [sourceFreeBeliefRawDirectionOfChildCode]
  split
  next h => exact Classical.choose_spec h
  next h => exact (h ⟨direction, rfl⟩).elim

/-- Total finite-tag successor.  The tag alphabet is the finite belief-code
type itself. -/
noncomputable def sourceFreeBeliefFiniteCodeNext
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : BeliefCode) (move : Move) (childCode : BeliefCode) : BeliefCode :=
  next code move
    (sourceFreeBeliefRawDirectionOfChildCode next code move childCode)

omit [Fintype BeliefCode] in
/-- On the tag announced by a real raw direction, the finite successor is the
literal raw successor. -/
theorem sourceFreeBeliefFiniteCodeNext_of_direction
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : BeliefCode) (move : Move) (direction : Direction) :
    sourceFreeBeliefFiniteCodeNext next code move
        (next code move direction) =
      next code move direction := by
  exact sourceFreeBeliefRawDirectionOfChildCode_next_eq next code move
    direction

/-- Drive an exact raw semantic tree by finite child-code tags through the
chosen raw representatives. -/
noncomputable def sourceFreeBeliefFiniteCodeSemanticTree
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    SourceFreeBeliefSemanticTree BeliefCode Move BeliefCode where
  Semantic := raw.Semantic
  initial := raw.initial
  step := fun state childCode =>
    raw.step state
      (sourceFreeBeliefRawDirectionOfChildCode next (raw.code state)
        (raw.move state) childCode)
  code := raw.code
  move := raw.move

omit [Fintype BeliefCode] in
/-- Every finite-tag node denotes a literal node of the original raw tree. -/
theorem sourceFreeBeliefFiniteCodeSemanticTree_exists_rawNode
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (node : TreeNode BeliefCode) :
    ∃ rawNode : TreeNode Direction,
      (sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt node =
        raw.stateAt rawNode := by
  induction node using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton node childCode ih =>
      rcases ih with ⟨rawNode, hstate⟩
      let direction := sourceFreeBeliefRawDirectionOfChildCode next
        (raw.code (raw.stateAt rawNode)) (raw.move (raw.stateAt rawNode))
        childCode
      refine ⟨rawNode ++ [direction], ?_⟩
      rw [(sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt_append,
        raw.stateAt_append, hstate]
      rfl

/-- Raw direction selected at time `n` along one finite-tag branch. -/
noncomputable def sourceFreeBeliefRawBranchOfFiniteCodeBranch
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (branch : Nat → BeliefCode) : Nat → Direction :=
  fun n =>
    let finite := sourceFreeBeliefFiniteCodeSemanticTree raw next
    let state := finite.stateAt (branchNode branch n)
    sourceFreeBeliefRawDirectionOfChildCode next (raw.code state)
      (raw.move state) (branch n)

omit [Fintype BeliefCode] in
/-- Along a branch, the finite-tag state is exactly the raw state reached by
the recursively expanded raw directions. -/
theorem sourceFreeBeliefFiniteCodeBranch_stateAt
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (branch : Nat → BeliefCode) (n : Nat) :
    let finite := sourceFreeBeliefFiniteCodeSemanticTree raw next
    let rawBranch := sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next
      branch
    finite.stateAt (branchNode branch n) =
      raw.stateAt (branchNode rawBranch n) := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        show branchNode
            (sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next branch)
              (n + 1) =
          branchNode
              (sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next branch) n ++
            [sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next branch n]
          from rfl,
        (sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt_append,
        raw.stateAt_append]
      rw [ih]
      simp only [sourceFreeBeliefFiniteCodeSemanticTree,
        sourceFreeBeliefRawBranchOfFiniteCodeBranch]
      congr 1
      rw [← ih]
      change sourceFreeBeliefRawDirectionOfChildCode next
          (raw.code
            ((sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt
              (branchNode branch n)))
          (raw.move
            ((sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt
              (branchNode branch n)))
          (branch n) =
        sourceFreeBeliefRawDirectionOfChildCode next
          (raw.code
            ((sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt
              (branchNode branch n)))
          (raw.move
            ((sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt
              (branchNode branch n)))
          (branch n)
      rfl

omit [Fintype BeliefCode] in
/-- The finite and expanded raw branches have the same successive child-code
word. -/
theorem sourceFreeBeliefFiniteCode_childCodeWord_eq_raw
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (branch : Nat → BeliefCode) :
    let finite := sourceFreeBeliefFiniteCodeSemanticTree raw next
    let rawBranch := sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next
      branch
    finite.childCodeWord branch = raw.childCodeWord rawBranch := by
  funext n
  change raw.code
      ((sourceFreeBeliefFiniteCodeSemanticTree raw next).stateAt
        (branchNode branch (n + 1))) =
    raw.code
      (raw.stateAt
        (branchNode
          (sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next branch)
          (n + 1)))
  rw [sourceFreeBeliefFiniteCodeBranch_stateAt raw next branch (n + 1)]

namespace SourceFreeBeliefCodeParityCertificate

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid next
    raw)

include certificate

omit [Fintype BeliefCode] in
/-- Restrict a raw code-parity certificate to the finite child-code direction
alphabet. -/
theorem finiteCodeDirectionCertificate :
    let finite := sourceFreeBeliefFiniteCodeSemanticTree raw next
    SourceFreeBeliefCodeParityCertificate D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext next) finite := by
  let finite := sourceFreeBeliefFiniteCodeSemanticTree raw next
  refine {
    initial_code := certificate.initial_code
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    rcases sourceFreeBeliefFiniteCodeSemanticTree_exists_rawNode raw next node
      with ⟨rawNode, hstate⟩
    change Valid (raw.code (finite.stateAt node))
      (raw.move (finite.stateAt node))
    rw [hstate]
    exact certificate.valid rawNode
  · intro node childCode
    rcases sourceFreeBeliefFiniteCodeSemanticTree_exists_rawNode raw next node
      with ⟨rawNode, hstate⟩
    change raw.code
        (raw.step (finite.stateAt node)
          (sourceFreeBeliefRawDirectionOfChildCode next
            (raw.code (finite.stateAt node)) (raw.move (finite.stateAt node))
            childCode)) =
      next (raw.code (finite.stateAt node)) (raw.move (finite.stateAt node))
        (sourceFreeBeliefRawDirectionOfChildCode next
          (raw.code (finite.stateAt node)) (raw.move (finite.stateAt node))
          childCode)
    rw [hstate]
    exact certificate.next_code rawNode _
  · intro branch
    let rawBranch := sourceFreeBeliefRawBranchOfFiniteCodeBranch raw next
      branch
    have haccepts := certificate.accepts rawBranch
    rw [sourceFreeBeliefFiniteCode_childCodeWord_eq_raw raw next branch]
    exact haccepts

/-- A raw code-parity certificate always yields a rational policy over the
finite child-code direction alphabet.  This invokes only the checked
finite-direction rational-run theorem. -/
theorem nonempty_finiteCodeDirectionRationalPolicy :
    Nonempty (SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext next)) := by
  let finite := sourceFreeBeliefFiniteCodeSemanticTree raw next
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    D initialCode Valid (sourceFreeBeliefFiniteCodeNext next) finite
    (certificate.finiteCodeDirectionCertificate D initialCode Valid next raw)
    (InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _)

end SourceFreeBeliefCodeParityCertificate

end

end DistributedSynthesis
