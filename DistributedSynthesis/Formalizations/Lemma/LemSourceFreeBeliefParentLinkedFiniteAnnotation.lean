/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodeDirection

/-!
# Parent-linked finite annotations for source-free belief trees

A finite witness attached only to the current semantic move can be lost when
rationalization reuses another occurrence of the same public code.  The safe
variant lets the parent move choose the annotations of *all* of its children.
The child transition then installs the selected annotation in the public
finite code.  Consequently, the annotation at a rational child is literally
the entry selected by its rational parent; no semantic representative is
reconstructed after rationalization.

This file isolates that construction from any particular hierarchy or block
model.  `Direction` and `Move` may be infinite.  Only the public belief code
and the installed annotation are finite.  The final section gives both
interfaces used downstream:

* an explicit rational-run-basis theorem for the original direction type;
* unconditional rationalization for finite directions, and for arbitrary
  nonempty directions after replacing them by finite child-code tags.

The construction is proof/controller data only.  It does not give a process
the graph, an orientation, a leader bit, or a semantic history.
-/

namespace DistributedSynthesis

universe u v w z a b

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable {Annotation : Type b}
variable [Fintype BeliefCode] [Fintype Annotation]

/-- Public finite code enriched by the annotation selected at this node. -/
abbrev SourceFreeBeliefParentLinkedCode := BeliefCode × Annotation

/-- A raw move together with the complete table of annotations to install at
its children.  The table may be infinite when `Direction` is infinite; it is
chosen as move payload, never stored in the finite automaton state. -/
abbrev SourceFreeBeliefParentLinkedMove :=
  Move × (Direction → Annotation)

/-- Source-free legality of a parent-linked move.  `LinkValid` is the
model-specific local law tying the current finite annotation and the complete
child table to the selected raw move. -/
def sourceFreeBeliefParentLinkedValid
    (Valid : BeliefCode → Move → Prop)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (code : SourceFreeBeliefParentLinkedCode
      (BeliefCode := BeliefCode) (Annotation := Annotation))
    (move : SourceFreeBeliefParentLinkedMove
      (Direction := Direction) (Move := Move) (Annotation := Annotation)) :
    Prop :=
  Valid code.1 move.1 ∧ LinkValid code.1 code.2 move.1 move.2

/-- The ordinary public code follows the old source-free transition; the
annotation component is copied literally from the parent's selected table. -/
def sourceFreeBeliefParentLinkedNext
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : SourceFreeBeliefParentLinkedCode
      (BeliefCode := BeliefCode) (Annotation := Annotation))
    (move : SourceFreeBeliefParentLinkedMove
      (Direction := Direction) (Move := Move) (Annotation := Annotation))
    (direction : Direction) :
    SourceFreeBeliefParentLinkedCode
      (BeliefCode := BeliefCode) (Annotation := Annotation) :=
  (next code.1 move.1 direction, move.2 direction)

omit [Fintype BeliefCode] [Fintype Annotation] in
@[simp] theorem sourceFreeBeliefParentLinkedNext_fst
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : SourceFreeBeliefParentLinkedCode
      (BeliefCode := BeliefCode) (Annotation := Annotation))
    (move : SourceFreeBeliefParentLinkedMove
      (Direction := Direction) (Move := Move) (Annotation := Annotation))
    (direction : Direction) :
    (sourceFreeBeliefParentLinkedNext next code move direction).1 =
      next code.1 move.1 direction :=
  rfl

omit [Fintype BeliefCode] [Fintype Annotation] in
/-- The key no-mosaic equation: the installed child annotation is exactly
the entry selected by the same parent move. -/
@[simp] theorem sourceFreeBeliefParentLinkedNext_snd
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : SourceFreeBeliefParentLinkedCode
      (BeliefCode := BeliefCode) (Annotation := Annotation))
    (move : SourceFreeBeliefParentLinkedMove
      (Direction := Direction) (Move := Move) (Annotation := Annotation))
    (direction : Direction) :
    (sourceFreeBeliefParentLinkedNext next code move direction).2 =
      move.2 direction :=
  rfl

/-- Enrich an exact semantic unfolding before rationalization.  The parent
move contains the annotations of its literal semantic children. -/
def SourceFreeBeliefSemanticTree.parentLinkFiniteAnnotation
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (annotation : raw.Semantic → Annotation) :
    SourceFreeBeliefSemanticTree
      Direction
      (SourceFreeBeliefParentLinkedMove
        (Direction := Direction) (Move := Move) (Annotation := Annotation))
      (SourceFreeBeliefParentLinkedCode
        (BeliefCode := BeliefCode) (Annotation := Annotation)) where
  Semantic := raw.Semantic
  initial := raw.initial
  step := raw.step
  code := fun state ↦ (raw.code state, annotation state)
  move := fun state ↦
    (raw.move state, fun direction ↦ annotation (raw.step state direction))

namespace SourceFreeBeliefSemanticTree

variable
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (annotation : raw.Semantic → Annotation)

section
omit [Fintype BeliefCode] [Fintype Annotation]

@[simp] theorem parentLinkFiniteAnnotation_stateAt
    (node : TreeNode Direction) :
    (raw.parentLinkFiniteAnnotation annotation).stateAt node =
      raw.stateAt node :=
  rfl

@[simp] theorem parentLinkFiniteAnnotation_code_fst
    (state : raw.Semantic) :
    ((raw.parentLinkFiniteAnnotation annotation).code state).1 =
      raw.code state :=
  rfl

@[simp] theorem parentLinkFiniteAnnotation_code_snd
    (state : raw.Semantic) :
    ((raw.parentLinkFiniteAnnotation annotation).code state).2 =
      annotation state :=
  rfl

@[simp] theorem parentLinkFiniteAnnotation_move_fst
    (state : raw.Semantic) :
    ((raw.parentLinkFiniteAnnotation annotation).move state).1 =
      raw.move state :=
  rfl

/-- At the semantic level the complete table also names the exact literal
child.  Together with `sourceFreeBeliefParentLinkedNext_snd`, this is the
parent/child linkage preserved by the rational policy. -/
@[simp] theorem parentLinkFiniteAnnotation_move_snd
    (state : raw.Semantic) (direction : Direction) :
    ((raw.parentLinkFiniteAnnotation annotation).move state).2 direction =
      annotation (raw.step state direction) :=
  rfl

/-- Projecting the enriched child-code word recovers the original word. -/
theorem parentLinkFiniteAnnotation_childCodeWord_fst
    (branch : Nat → Direction) :
    OmegaWord.map Prod.fst
        ((raw.parentLinkFiniteAnnotation annotation).childCodeWord branch) =
      raw.childCodeWord branch := by
  funext n
  rfl

end

end SourceFreeBeliefSemanticTree

/-- The old code objective ignores the installed finite annotation. -/
noncomputable def sourceFreeBeliefParentLinkedCodeParityDPA
    (D : DetParityAutomaton.{z, w} BeliefCode) :
    DetParityAutomaton
      (SourceFreeBeliefParentLinkedCode
        (BeliefCode := BeliefCode) (Annotation := Annotation)) :=
  D.comap Prod.fst

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

omit [Fintype BeliefCode] [Fintype Annotation] in
/-- Lift a code-parity certificate through a finite parent-linked annotation.
The sole new model obligation is `LinkValid` at each exact semantic node. -/
theorem parentLinkFiniteAnnotation
    (annotation : raw.Semantic → Annotation)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (hlink : ∀ node : TreeNode Direction,
      LinkValid
        (raw.code (raw.stateAt node))
        (annotation (raw.stateAt node))
        (raw.move (raw.stateAt node))
        (fun direction ↦
          annotation (raw.step (raw.stateAt node) direction))) :
    SourceFreeBeliefCodeParityCertificate
      (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := Annotation) D)
      (initialCode, annotation raw.initial)
      (sourceFreeBeliefParentLinkedValid Valid LinkValid)
      (sourceFreeBeliefParentLinkedNext next)
      (raw.parentLinkFiniteAnnotation annotation) := by
  refine {
    initial_code := ?_
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · apply Prod.ext
    · exact certificate.initial_code
    · rfl
  · intro node
    exact ⟨certificate.valid node, hlink node⟩
  · intro node direction
    apply Prod.ext
    · exact certificate.next_code node direction
    · rfl
  · intro branch
    rw [sourceFreeBeliefParentLinkedCodeParityDPA,
      DetParityAutomaton.comap_accepts_iff,
      raw.parentLinkFiniteAnnotation_childCodeWord_fst annotation]
    exact certificate.accepts branch

/-- Rationalization over the original direction alphabet, parameterized by
the corresponding input-free rational-run basis.  This is the most general
interface and makes no finiteness assumption on `Direction`. -/
theorem nonempty_parentLinkedRationalPolicy
    (annotation : raw.Semantic → Annotation)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (hlink : ∀ node : TreeNode Direction,
      LinkValid
        (raw.code (raw.stateAt node))
        (annotation (raw.stateAt node))
        (raw.move (raw.stateAt node))
        (fun direction ↦
          annotation (raw.step (raw.stateAt node) direction)))
    (basis :
      (sourceFreeBeliefCodeParityRunAutomaton
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, annotation raw.initial)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefParentLinkedNext next)).RationalRunBasis) :
    Nonempty
      (SourceFreeBeliefCodeParityRationalPolicy
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, annotation raw.initial)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefParentLinkedNext next)) := by
  let linked := raw.parentLinkFiniteAnnotation annotation
  let linkedCertificate := certificate.parentLinkFiniteAnnotation D initialCode
    Valid next raw annotation LinkValid hlink
  exact linkedCertificate.nonempty_rationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := Annotation) D)
    (initialCode, annotation raw.initial)
    (sourceFreeBeliefParentLinkedValid Valid LinkValid)
    (sourceFreeBeliefParentLinkedNext next)
    linked basis

/-- With a finite original direction alphabet, parent-linked rationalization
is unconditional by the checked finite tree-automaton theorem. -/
theorem nonempty_parentLinkedRationalPolicy_of_finite
    [Fintype Direction]
    (annotation : raw.Semantic → Annotation)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (hlink : ∀ node : TreeNode Direction,
      LinkValid
        (raw.code (raw.stateAt node))
        (annotation (raw.stateAt node))
        (raw.move (raw.stateAt node))
        (fun direction ↦
          annotation (raw.step (raw.stateAt node) direction))) :
    Nonempty
      (SourceFreeBeliefCodeParityRationalPolicy
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, annotation raw.initial)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefParentLinkedNext next)) := by
  apply certificate.nonempty_parentLinkedRationalPolicy D initialCode Valid next
    raw annotation LinkValid hlink
  exact InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _

/-- For arbitrary nonempty directions, replace raw directions by the finite
linked child-code alphabet and rationalize unconditionally.  In particular a
whole block may remain semantic direction data without becoming runtime
information available to a process. -/
theorem nonempty_parentLinkedFiniteCodeDirectionRationalPolicy
    [Nonempty Direction]
    (annotation : raw.Semantic → Annotation)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (hlink : ∀ node : TreeNode Direction,
      LinkValid
        (raw.code (raw.stateAt node))
        (annotation (raw.stateAt node))
        (raw.move (raw.stateAt node))
        (fun direction ↦
          annotation (raw.step (raw.stateAt node) direction))) :
    Nonempty
      (SourceFreeBeliefCodeParityRationalPolicy
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, annotation raw.initial)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext next))) := by
  let linked := raw.parentLinkFiniteAnnotation annotation
  let linkedCertificate := certificate.parentLinkFiniteAnnotation D initialCode
    Valid next raw annotation LinkValid hlink
  exact linkedCertificate.nonempty_finiteCodeDirectionRationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := Annotation) D)
    (initialCode, annotation raw.initial)
    (sourceFreeBeliefParentLinkedValid Valid LinkValid)
    (sourceFreeBeliefParentLinkedNext next)
    linked

end SourceFreeBeliefCodeParityCertificate

namespace SourceFreeBeliefCodeParityRationalPolicy

/-- Legality of a reachable parent-linked policy state exposes one raw move,
its complete child-annotation table, and the exact successor equation.  The
model-specific link law comes from the *same* selected transition. -/
theorem exists_parentLinkedMove
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialAnnotation : Annotation)
    (Valid : BeliefCode → Move → Prop)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy :
      SourceFreeBeliefCodeParityRationalPolicy
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, initialAnnotation)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefParentLinkedNext next))
    (state :
      (sourceFreeBeliefCodeParityRunAutomaton
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, initialAnnotation)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefParentLinkedNext next)).State)
    (hreachable :
      policy.Reachable
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, initialAnnotation)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefParentLinkedNext next) state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := Direction) (Move := Move) (Annotation := Annotation),
      Valid state.1.1 move.1 ∧
        LinkValid state.1.1 state.1.2 move.1 move.2 ∧
        ∀ direction,
          policy.successor state direction =
            let childCode :=
              sourceFreeBeliefParentLinkedNext next state.1 move direction
            (childCode,
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation := Annotation) D).step state.2 childCode) := by
  rcases policy.exists_sourceFreeMove
      (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := Annotation) D)
      (initialCode, initialAnnotation)
      (sourceFreeBeliefParentLinkedValid Valid LinkValid)
      (sourceFreeBeliefParentLinkedNext next)
      state hreachable with ⟨move, hvalid, hsuccessor⟩
  exact ⟨move, hvalid.1, hvalid.2, hsuccessor⟩

/-- Arbitrary-direction companion for the finite-child-code policy.  Querying
the policy with the actual finite child code of a raw direction recovers that
exact child code, hence in particular the annotation selected by the parent.
The raw direction itself is not placed in the finite policy state. -/
theorem exists_parentLinkedMove_finiteCodeDirection
    [Nonempty Direction]
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialAnnotation : Annotation)
    (Valid : BeliefCode → Move → Prop)
    (LinkValid : BeliefCode → Annotation → Move →
      (Direction → Annotation) → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy :
      SourceFreeBeliefCodeParityRationalPolicy
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, initialAnnotation)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext next)))
    (state :
      (sourceFreeBeliefCodeParityRunAutomaton
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, initialAnnotation)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext next))).State)
    (hreachable :
      policy.Reachable
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation := Annotation) D)
        (initialCode, initialAnnotation)
        (sourceFreeBeliefParentLinkedValid Valid LinkValid)
        (sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext next)) state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := Direction) (Move := Move) (Annotation := Annotation),
      Valid state.1.1 move.1 ∧
        LinkValid state.1.1 state.1.2 move.1 move.2 ∧
        ∀ direction : Direction,
          policy.successor state
              (sourceFreeBeliefParentLinkedNext next state.1 move direction) =
            let childCode :=
              sourceFreeBeliefParentLinkedNext next state.1 move direction
            (childCode,
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation := Annotation) D).step state.2 childCode) := by
  rcases policy.exists_sourceFreeMove
      (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := Annotation) D)
      (initialCode, initialAnnotation)
      (sourceFreeBeliefParentLinkedValid Valid LinkValid)
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext next))
      state hreachable with ⟨move, hvalid, hsuccessor⟩
  refine ⟨move, hvalid.1, hvalid.2, ?_⟩
  intro direction
  simpa only [sourceFreeBeliefFiniteCodeNext_of_direction] using
    hsuccessor
      (sourceFreeBeliefParentLinkedNext next state.1 move direction)

end SourceFreeBeliefCodeParityRationalPolicy

end

end DistributedSynthesis
