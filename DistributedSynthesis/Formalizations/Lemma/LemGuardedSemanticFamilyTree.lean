/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization

/-!
# A semantic family tree with an explicit coherent branch

A public family controller observes a finite direction together with the
family advertised for the child.  The full observation tree also contains
histories which advertise an arbitrary, semantically false child family.
Those histories need a legal fallback move, but they must not be confused
with an execution of the model.

This file packages the distinction once.  Along a coherent history, the
stored family is exactly the family extracted from the recursively reached
semantic state and the tree uses the semantic move.  Once a history becomes
incoherent, the tree uses an arbitrary legal move at the advertised family.
In particular, rationalization may safely totalize the full observation
tree while a later coverage theorem proves that a real execution stays on a
coherent, live hidden thread.
-/

namespace DistributedSynthesis

universe u v w x

section

variable {Semantic : Type u} {Direction : Type v}
variable {Family : Type w} {Move : Type x}
variable [Inhabited Direction]
variable [DecidableEq Family]

/-- The public observation made after a move: a finite direction and the
family claimed for the reached child. -/
abbrev GuardedSemanticFamilyObservation := Direction × Family

/-- Proof-side fold state.  The Boolean is sticky: it records that every
family seen so far was the family of the recursively reached semantic state.
-/
abbrev GuardedSemanticFamilyTraceState := Semantic × Bool

/-- Fold a public observation history while checking its family claims. -/
noncomputable def guardedSemanticFamilyTraceStateAt
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (node : TreeNode
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family))) :
    GuardedSemanticFamilyTraceState
      (Semantic := Semantic) := by
  classical
  exact node.foldl (fun current observation =>
    let next := step current.1 observation.1
    (next, current.2 && decide (observation.2 = familyOf next)))
    (initial, true)

omit [Inhabited Direction] in
theorem guardedSemanticFamilyTraceStateAt_append
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (node : TreeNode
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family)))
    (observation : GuardedSemanticFamilyObservation
      (Direction := Direction) (Family := Family)) :
    guardedSemanticFamilyTraceStateAt initial step familyOf
        (node ++ [observation]) =
      let current :=
        guardedSemanticFamilyTraceStateAt initial step familyOf node
      let next := step current.1 observation.1
      (next, current.2 && decide (observation.2 = familyOf next)) := by
  classical
  simp [guardedSemanticFamilyTraceStateAt]
  rfl

/-- At a coherent node, its current advertised family is exactly the family
of the recursively reached semantic state. -/
theorem guardedSemanticFamilyTraceStateAt_current_family
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (initialFamily : Family)
    (hinitial : initialFamily = familyOf initial)
    (node : TreeNode
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family)))
    (hcoherent :
      (guardedSemanticFamilyTraceStateAt initial step familyOf node).2 =
        true) :
    (observableAt ((default : Direction), initialFamily) node).2 =
      familyOf
        (guardedSemanticFamilyTraceStateAt initial step familyOf node).1 := by
  classical
  cases node using List.reverseRecOn with
  | nil => simpa [guardedSemanticFamilyTraceStateAt, observableAt] using hinitial
  | append_singleton node observation =>
      rw [guardedSemanticFamilyTraceStateAt_append] at hcoherent ⊢
      have hclaim : observation.2 = familyOf
          (step
            (guardedSemanticFamilyTraceStateAt initial step familyOf node).1
            observation.1) := by
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcoherent).2
      simpa [observableAt] using hclaim

omit [Inhabited Direction] in
/-- Appending the semantically correct child family preserves coherence. -/
theorem guardedSemanticFamilyTraceStateAt_append_coherent
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (node : TreeNode
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family)))
    (hcoherent :
      (guardedSemanticFamilyTraceStateAt initial step familyOf node).2 =
        true)
    (direction : Direction) :
    (guardedSemanticFamilyTraceStateAt initial step familyOf
      (node ++ [(direction,
        familyOf (step
          (guardedSemanticFamilyTraceStateAt initial step familyOf node).1
          direction))])).2 = true := by
  classical
  rw [guardedSemanticFamilyTraceStateAt_append]
  simp [hcoherent]

omit [Inhabited Direction] in
/-- The semantic component of the correct child is the literal semantic
successor. -/
theorem guardedSemanticFamilyTraceStateAt_append_fst
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (node : TreeNode
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family)))
    (observation : GuardedSemanticFamilyObservation
      (Direction := Direction) (Family := Family)) :
    (guardedSemanticFamilyTraceStateAt initial step familyOf
      (node ++ [observation])).1 =
        step
          (guardedSemanticFamilyTraceStateAt initial step familyOf node).1
          observation.1 := by
  classical
  rw [guardedSemanticFamilyTraceStateAt_append]

/-- Choose one legal totalization move for an incoherent advertised family. -/
noncomputable def guardedSemanticFamilyFallbackMove
    (Valid : Family → Move → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (family : Family) : Move :=
  Classical.choose (htotal family)

omit [DecidableEq Family] in
theorem guardedSemanticFamilyFallbackMove_valid
    (Valid : Family → Move → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (family : Family) :
    Valid family (guardedSemanticFamilyFallbackMove Valid htotal family) :=
  Classical.choose_spec (htotal family)

/-- Total public tree: use the exact semantic move while the family history
is coherent, and a legal fallback after the first false family claim. -/
noncomputable def guardedSemanticFamilyTree
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → Move)
    (Valid : Family → Move → Prop)
    (htotal : ∀ family, ∃ move, Valid family move) :
    LabeledTree
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family)) Move := fun node =>
  let current := guardedSemanticFamilyTraceStateAt initial step familyOf node
  if current.2 = true then semanticMove current.1
  else
    guardedSemanticFamilyFallbackMove Valid htotal
      (observableAt ((default : Direction), familyOf initial) node).2

/-- The totalized tree chooses legal moves at every public node. -/
theorem guardedSemanticFamilyTree_movesValid
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → Move)
    (Valid : Family → Move → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (hsemantic : ∀ state, Valid (familyOf state) (semanticMove state)) :
    ObservableMovesValid ((default : Direction), familyOf initial)
      (fun observation move => Valid observation.2 move)
      (guardedSemanticFamilyTree initial step familyOf semanticMove Valid
        htotal) := by
  classical
  intro node
  let current := guardedSemanticFamilyTraceStateAt initial step familyOf node
  by_cases hcoherent : current.2 = true
  · have hfamily := guardedSemanticFamilyTraceStateAt_current_family
      initial step familyOf (familyOf initial) rfl node hcoherent
    simp only [guardedSemanticFamilyTree, current, hcoherent, if_true]
    rw [hfamily]
    exact hsemantic current.1
  · simp only [guardedSemanticFamilyTree, current, hcoherent, if_false]
    exact guardedSemanticFamilyFallbackMove_valid Valid htotal _

/-- On a coherent history the public label is exactly the move extracted
from its one recursively reached semantic state. -/
theorem guardedSemanticFamilyTree_eq_semanticMove
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → Move)
    (Valid : Family → Move → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (node : TreeNode
      (GuardedSemanticFamilyObservation
        (Direction := Direction) (Family := Family)))
    (hcoherent :
      (guardedSemanticFamilyTraceStateAt initial step familyOf node).2 =
        true) :
    guardedSemanticFamilyTree initial step familyOf semanticMove Valid htotal
        node =
      semanticMove
        (guardedSemanticFamilyTraceStateAt initial step familyOf node).1 := by
  simp [guardedSemanticFamilyTree, hcoherent]

/-! ## Canonical live branch -/

/-- Semantic state reached after the first `n` directions of a branch. -/
def guardedSemanticFamilyIterate
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (branch : Nat → Direction) : Nat → Semantic
  | 0 => initial
  | n + 1 => step (guardedSemanticFamilyIterate initial step branch n)
      (branch n)

/-- Advertise, after every direction, the family of its literal semantic
successor.  This is the branch which a model readback/coverage theorem must
identify with the real execution. -/
def guardedSemanticFamilyObservationBranch
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (branch : Nat → Direction) :
    Nat → GuardedSemanticFamilyObservation
      (Direction := Direction) (Family := Family) := fun n =>
  (branch n,
    familyOf (guardedSemanticFamilyIterate initial step branch (n + 1)))

omit [Inhabited Direction] in
/-- The canonical observation branch is coherent at every finite prefix and
its stored semantic state is the literal recursive iterate. -/
theorem guardedSemanticFamilyTraceStateAt_branchNode
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (branch : Nat → Direction) : ∀ n,
    guardedSemanticFamilyTraceStateAt initial step familyOf
        (branchNode
          (guardedSemanticFamilyObservationBranch initial step familyOf
            branch) n) =
      (guardedSemanticFamilyIterate initial step branch n, true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode
          (guardedSemanticFamilyObservationBranch initial step familyOf
            branch) (n + 1) =
          branchNode
            (guardedSemanticFamilyObservationBranch initial step familyOf
              branch) n ++
            [guardedSemanticFamilyObservationBranch initial step familyOf
              branch n] from rfl,
        guardedSemanticFamilyTraceStateAt_append, ih]
      simp [guardedSemanticFamilyObservationBranch,
        guardedSemanticFamilyIterate]

/-- Along the canonical coherent branch, the totalized public tree uses the
semantic move at every level. -/
theorem guardedSemanticFamilyTree_branchNode
    (initial : Semantic)
    (step : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → Move)
    (Valid : Family → Move → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (branch : Nat → Direction)
    (n : Nat) :
    guardedSemanticFamilyTree initial step familyOf semanticMove Valid htotal
        (branchNode
          (guardedSemanticFamilyObservationBranch initial step familyOf
            branch) n) =
      semanticMove (guardedSemanticFamilyIterate initial step branch n) := by
  rw [guardedSemanticFamilyTree_eq_semanticMove initial step familyOf
    semanticMove Valid htotal]
  · rw [guardedSemanticFamilyTraceStateAt_branchNode]
  · rw [guardedSemanticFamilyTraceStateAt_branchNode]

end

end DistributedSynthesis
