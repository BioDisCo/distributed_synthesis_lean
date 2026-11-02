/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorFamilyTotality
import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorTreeRationalization

/-!
# Assembly of a guarded semantic family tree

This module joins the three generic ingredients used by the concrete optional
family adapter:

* `guardedSemanticFamilyTree` totalizes false advertised child families;
* `HiddenDescriptorFamilySemanticGuard` supplies exact-edge totality on the
  coherent branch and one-origin semantic lifting for every surviving thread;
* parity of every literal semantic branch supplies the objective.

The result has two deliberately different conclusions.  The complete public
observation tree has a winning state-controlled replacement: false-family
branches are legal and any incoherent hidden resolution dies harmlessly.  On
every canonical coherent direction branch of the original semantic tree,
coverage additionally constructs a nonempty infinite exact thread.  Thus the
accepting dead state is never used as evidence that a real semantic execution
exists.

No orientation, lane shape, leader bit, or selected family member occurs in
the API.  Those remain proof-side content of the concrete `Live`,
`Represented`, `Supported`, and `ExactEdge` predicates.
-/

namespace DistributedSynthesis

universe u v m b x y

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b} {Semantic : Type y}
variable [Fintype Code] [Fintype MoveIdentity]
variable [Fintype FamilyMove] [Fintype Direction]
variable [Inhabited Direction]

/-- All model-facing hypotheses for the guarded family-tree assembly.

The public semantic successor is driven by the finite `Direction`; the
semantic lifter retained by `guard` may inspect the full exact target, but its
chosen direction has the same proof-side type. -/
structure GuardedHiddenDescriptorTreePackage
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (semanticMove : Semantic → FamilyMove)
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (initial : Semantic) : Type (max u v m b x y) where
  guard : HiddenDescriptorFamilySemanticGuard D semanticStep
    semanticDescriptor Represented Live ExactEdge Valid Supported
  initial_control : (semanticDescriptor initial).control = D.initial
  initial_live : Live (semanticDescriptor initial) (familyOf initial)
  valid_total : ∀ family, ∃ move, Valid family move
  semantic_move_valid : ∀ state,
    Valid (familyOf state) (semanticMove state)
  semantic_observation_supported : ∀ state direction,
    Supported (familyOf state) (semanticMove state) direction
      (familyOf (semanticStep state direction))
  semantic_branch_accepts : ∀ branch : Nat → Direction,
    D.Accepts (fun n =>
      (semanticDescriptor
        ((branchNode branch (n + 1)).foldl semanticStep initial)).code)

namespace GuardedHiddenDescriptorTreePackage

variable
  (semanticStep : Semantic → Direction → Semantic)
  (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))
  (semanticMove : Semantic → FamilyMove)
  (Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Prop)
  (Live : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Prop)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
  (Supported : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
    HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Prop)
  (initial : Semantic)
  (package : GuardedHiddenDescriptorTreePackage D semanticStep
    semanticDescriptor familyOf semanticMove Represented Live ExactEdge Valid
    Supported initial)

/-- The total public semantic tree.  At a false advertised-family history it
uses a legal fallback move; on a coherent history it uses `semanticMove`. -/
noncomputable def tree : LabeledTree
    (HiddenDescriptorTreeObservation
      (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))) FamilyMove :=
  guardedSemanticFamilyTree initial semanticStep familyOf semanticMove Valid
    package.valid_total

omit [Fintype FamilyMove] [Fintype Direction] in
/-- Every node of the totalized public tree chooses a valid move, including
nodes below a false advertised family. -/
theorem tree_movesValid :
    ObservableMovesValid
      ((default : Direction), familyOf initial)
      (fun observation move => Valid observation.2 move)
      (package.tree D semanticStep semanticDescriptor familyOf semanticMove
        Represented Live ExactEdge Valid Supported initial) := by
  exact guardedSemanticFamilyTree_movesValid initial semanticStep familyOf
    semanticMove Valid package.valid_total package.semantic_move_valid

omit [Fintype FamilyMove] [Fintype Direction] in
/-- Every surviving exact thread on every ambient observation branch is a
single literal semantic branch and hence satisfies parity.  No existence is
claimed for a false-family branch. -/
theorem thread_accepts
    (branch : Nat → HiddenDescriptorTreeObservation
      (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity)))
    (thread : HiddenDescriptorContinuityThread D
      (semanticDescriptor initial) ExactEdge
      (observableThreadWord
        (package.tree D semanticStep semanticDescriptor familyOf semanticMove
          Represented Live ExactEdge Valid Supported initial)
        branch)) :
    D.Accepts thread.childCodeWord := by
  exact hiddenDescriptorThread_accepts_of_semanticEdgeLifter D semanticStep
    semanticDescriptor initial ExactEdge package.guard.semanticLifter
    (observableThreadWord
      (package.tree D semanticStep semanticDescriptor familyOf semanticMove
        Represented Live ExactEdge Valid Supported initial)
      branch)
    thread package.semantic_branch_accepts

/-- The complete guarded semantic tree wins the observable hidden-descriptor
monitor.  Incoherent family advertisements are harmless; coherent surviving
threads carry the semantic parity proof. -/
theorem tree_winning [DecidableRel Valid] :
    (hiddenDescriptorContinuityTreeMonitor D
      (semanticDescriptor initial) ExactEdge (familyOf initial) Valid)
        |>.WinningTree
          (package.tree D semanticStep semanticDescriptor familyOf semanticMove
            Represented Live ExactEdge Valid Supported initial) := by
  exact (hiddenDescriptorContinuityTreeMonitor_winning_iff D
    (semanticDescriptor initial) package.initial_control ExactEdge
    (familyOf initial) Valid
    (package.tree D semanticStep semanticDescriptor familyOf semanticMove
      Represented Live ExactEdge Valid Supported initial)).2
      ⟨package.tree_movesValid D semanticStep semanticDescriptor familyOf
          semanticMove Represented Live ExactEdge Valid Supported initial,
        package.thread_accepts D semanticStep semanticDescriptor familyOf
          semanticMove Represented Live ExactEdge Valid Supported initial⟩

include package

/-- Rationalize the complete winning tree once.  The returned controller is
finite and state-controlled and still wins the validity/hidden-thread
monitor. -/
theorem exists_stateControlled_winning [DecidableRel Valid] :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (hiddenDescriptorContinuityTreeMonitor D
          (semanticDescriptor initial) ExactEdge (familyOf initial) Valid
          |>.toRunAutomaton),
      (hiddenDescriptorContinuityTreeMonitor D
        (semanticDescriptor initial) ExactEdge (familyOf initial) Valid)
          |>.WinningTree table.toTransitionRationalTree.labeledTree := by
  exact exists_stateControlled_hiddenDescriptorContinuityTree D
    (semanticDescriptor initial) package.initial_control ExactEdge
    (familyOf initial) Valid
    (package.tree D semanticStep semanticDescriptor familyOf semanticMove
      Represented Live ExactEdge Valid Supported initial)
    (package.tree_movesValid D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial)
    (package.thread_accepts D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial)

/-- The public word on one canonical coherent direction branch. -/
noncomputable def canonicalWord (branch : Nat → Direction) :=
  guardedHiddenDescriptorFamilyWord D initial semanticStep familyOf
    semanticMove Valid package.valid_total branch

/-- Every canonical direction branch satisfies the validity/support laws
required by exact-edge coverage. -/
noncomputable def canonicalWordAdmissible (branch : Nat → Direction) :
    HiddenDescriptorFamilyWordAdmissible D Live
      (semanticDescriptor initial) (familyOf initial) Valid Supported
      (package.canonicalWord D semanticStep semanticDescriptor familyOf
        semanticMove Represented Live ExactEdge Valid Supported initial
        branch) :=
  guardedHiddenDescriptorFamilyWordAdmissible D initial semanticStep
    semanticDescriptor familyOf semanticMove Live Valid Supported
    package.valid_total package.initial_live package.semantic_move_valid
    package.semantic_observation_supported branch

/-- Canonical exact thread selected recursively by coverage. -/
noncomputable def canonicalThread (branch : Nat → Direction) :
    HiddenDescriptorContinuityThread D (semanticDescriptor initial) ExactEdge
      (package.canonicalWord D semanticStep semanticDescriptor familyOf
        semanticMove Represented Live ExactEdge Valid Supported initial
        branch) :=
  package.guard.totality.admissibleThread D Represented Live ExactEdge Valid
    Supported (semanticDescriptor initial) (familyOf initial)
    (package.canonicalWord D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)
    (package.canonicalWordAdmissible D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)

omit [Fintype FamilyMove] [Fintype Direction] in
/-- Dead-state vacuity is impossible on every canonical coherent direction
branch: at least one infinite exact thread exists. -/
theorem canonicalThread_nonempty (branch : Nat → Direction) :
    Nonempty
      (HiddenDescriptorContinuityThread D (semanticDescriptor initial)
        ExactEdge
        (package.canonicalWord D semanticStep semanticDescriptor familyOf
          semanticMove Represented Live ExactEdge Valid Supported initial
          branch)) :=
  ⟨package.canonicalThread D semanticStep semanticDescriptor familyOf
    semanticMove Represented Live ExactEdge Valid Supported initial branch⟩

omit [Fintype FamilyMove] [Fintype Direction] in
/-- The canonical exact thread is literally a live run of the hidden system. -/
theorem canonicalThread_isRun (branch : Nat → Direction) :
    (hiddenDescriptorContinuitySystem D (semanticDescriptor initial) ExactEdge)
        |>.IsRun
          (package.canonicalWord D semanticStep semanticDescriptor familyOf
            semanticMove Represented Live ExactEdge Valid Supported initial
            branch)
          (HiddenDescriptorContinuityThread.stateAt D
            (semanticDescriptor initial) ExactEdge
            (package.canonicalWord D semanticStep semanticDescriptor familyOf
              semanticMove Represented Live ExactEdge Valid Supported initial
              branch)
            (package.canonicalThread D semanticStep semanticDescriptor familyOf
              semanticMove Represented Live ExactEdge Valid Supported initial
              branch)) :=
  HiddenDescriptorContinuityThread.isRun D (semanticDescriptor initial)
    ExactEdge _ _

/-- Final generic join: a winning state-controlled public tree exists, while
every canonical coherent semantic direction branch of the source tree has a
nonempty exact hidden thread. -/
theorem exists_stateControlled_winning_and_canonicalThreads
    [DecidableRel Valid] :
    (∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (hiddenDescriptorContinuityTreeMonitor D
          (semanticDescriptor initial) ExactEdge (familyOf initial) Valid
          |>.toRunAutomaton),
      (hiddenDescriptorContinuityTreeMonitor D
        (semanticDescriptor initial) ExactEdge (familyOf initial) Valid)
          |>.WinningTree table.toTransitionRationalTree.labeledTree) ∧
      ∀ branch : Nat → Direction,
        Nonempty
          (HiddenDescriptorContinuityThread D (semanticDescriptor initial)
            ExactEdge
            (package.canonicalWord D semanticStep semanticDescriptor familyOf
              semanticMove Represented Live ExactEdge Valid Supported initial
              branch)) :=
  ⟨package.exists_stateControlled_winning D semanticStep semanticDescriptor
      familyOf semanticMove Represented Live ExactEdge Valid Supported initial,
    package.canonicalThread_nonempty D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial⟩

end GuardedHiddenDescriptorTreePackage

end

end DistributedSynthesis
