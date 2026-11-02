/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFamilyAwareHiddenDescriptorThreadLifting

/-!
# Family-aware assembly of a guarded semantic family tree

This is the faithful guarded-tree assembly for the staged finite-family
construction.  Its exact-edge lift may use validity at the current public
family and must recover both the literal semantic child descriptor and its
literal child family.  Thus the proof never assumes that a hidden descriptor
alone determines its source fibre.

The complete public tree is total: below a falsely advertised family it uses
an arbitrary legal fallback.  Such a branch may have no infinite exact thread
and is accepted only through the monitor's harmless dead state.  Separately,
every canonical coherent direction branch is `Supported`; family totality
therefore constructs a nonempty infinite live exact thread, and the
family-aware lift identifies that thread with one literal semantic branch.

All family and lane distinctions are proof-side finite control.  No process
is given an orientation, lane shape, selected family member, or strict-leader
signal.
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

/-- The corrected model-facing package for the guarded family tree.

`totality` is used only on canonical `Supported` observations, while
`semanticLifter` controls every exact thread that survives in the complete
totalized public tree.  In contrast to `HiddenDescriptorFamilySemanticGuard`,
the lift retains the current public family and also checks the next family. -/
structure FamilyAwareGuardedHiddenDescriptorTreePackage
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
  totality : HiddenDescriptorFamilyTotality D Represented Live ExactEdge Valid
    Supported
  semanticLifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
    semanticDescriptor familyOf ExactEdge Valid
  initial_control : (semanticDescriptor initial).control = D.initial
  initial_live : Live (semanticDescriptor initial) (familyOf initial)
  valid_total : ∀ family, ∃ move, Valid family move
  semantic_move_valid : ∀ state,
    Valid (familyOf state) (semanticMove state)
  semantic_observation_supported : ∀ state direction,
    Supported (familyOf state) (semanticMove state) direction
      (familyOf (semanticStep state direction))
  semantic_branch_accepts : ∀ branch : Nat → Direction,
    D.Accepts (fun n ↦
      (semanticDescriptor
        ((branchNode branch (n + 1)).foldl semanticStep initial)).code)

namespace FamilyAwareGuardedHiddenDescriptorTreePackage

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
  (package : FamilyAwareGuardedHiddenDescriptorTreePackage D semanticStep
    semanticDescriptor familyOf semanticMove Represented Live ExactEdge Valid
    Supported initial)

/-- The total public tree: literal semantic moves on coherent histories and a
legal fallback below false advertised families. -/
noncomputable def tree : LabeledTree
    (HiddenDescriptorTreeObservation
      (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))) FamilyMove :=
  guardedSemanticFamilyTree initial semanticStep familyOf semanticMove Valid
    package.valid_total

omit [Fintype FamilyMove] [Fintype Direction] in
/-- Every node, including one below a false family advertisement, carries a
move valid for the currently advertised finite family. -/
theorem tree_movesValid :
    ObservableMovesValid
      ((default : Direction), familyOf initial)
      (fun observation move ↦ Valid observation.2 move)
      (package.tree D semanticStep semanticDescriptor familyOf semanticMove
        Represented Live ExactEdge Valid Supported initial) := by
  exact guardedSemanticFamilyTree_movesValid initial semanticStep familyOf
    semanticMove Valid package.valid_total package.semantic_move_valid

omit [Fintype FamilyMove] [Fintype Direction] in
/-- Every exact thread surviving on an arbitrary public branch is one
literal semantic branch.  False-family branches are allowed to have no such
thread; this theorem does not turn that vacuity into a recovery claim. -/
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
  apply package.semanticLifter.thread_accepts D semanticStep
    semanticDescriptor familyOf ExactEdge Valid initial (familyOf initial)
    (observableThreadWord
      (package.tree D semanticStep semanticDescriptor familyOf semanticMove
        Represented Live ExactEdge Valid Supported initial)
      branch)
    thread rfl
  · intro n
    have hnode := package.tree_movesValid D semanticStep semanticDescriptor
      familyOf semanticMove Represented Live ExactEdge Valid Supported initial
      (branchNode branch n)
    rw [familyAwareHiddenDescriptorFamilyAt_observableThreadWord
      (familyOf initial)
      (package.tree D semanticStep semanticDescriptor familyOf semanticMove
        Represented Live ExactEdge Valid Supported initial)
      branch n]
    exact hnode
  · exact package.semantic_branch_accepts

/-- The complete totalized public tree wins the hidden-descriptor monitor by
the family-aware lift. -/
theorem tree_winning [DecidableRel Valid] :
    (hiddenDescriptorContinuityTreeMonitor D
      (semanticDescriptor initial) ExactEdge (familyOf initial) Valid)
        |>.WinningTree
          (package.tree D semanticStep semanticDescriptor familyOf semanticMove
            Represented Live ExactEdge Valid Supported initial) := by
  exact familyAware_hiddenDescriptorContinuityTree_winning D semanticStep
    semanticDescriptor familyOf ExactEdge Valid package.semanticLifter initial
    (familyOf initial) rfl package.initial_control
    (package.tree D semanticStep semanticDescriptor familyOf semanticMove
      Represented Live ExactEdge Valid Supported initial)
    (package.tree_movesValid D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial)
    package.semantic_branch_accepts

include package

/-- Rationalize the complete winning tree once. -/
theorem exists_stateControlled_winning [DecidableRel Valid] :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (hiddenDescriptorContinuityTreeMonitor D
          (semanticDescriptor initial) ExactEdge (familyOf initial) Valid
          |>.toRunAutomaton),
      (hiddenDescriptorContinuityTreeMonitor D
        (semanticDescriptor initial) ExactEdge (familyOf initial) Valid)
          |>.WinningTree table.toTransitionRationalTree.labeledTree := by
  exact exists_stateControlled_familyAwareHiddenDescriptorContinuityTree D
    semanticStep semanticDescriptor familyOf ExactEdge Valid
    package.semanticLifter initial (familyOf initial) rfl
    package.initial_control
    (package.tree D semanticStep semanticDescriptor familyOf semanticMove
      Represented Live ExactEdge Valid Supported initial)
    (package.tree_movesValid D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial)
    package.semantic_branch_accepts

/-- Public word on a canonical coherent semantic-family branch. -/
noncomputable def canonicalWord (branch : Nat → Direction) :=
  guardedHiddenDescriptorFamilyWord D initial semanticStep familyOf
    semanticMove Valid package.valid_total branch

/-- Canonical coherent branches satisfy validity and the model's `Supported`
successor-family law. -/
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

/-- Infinite live exact thread selected recursively by supported coverage. -/
noncomputable def canonicalThread (branch : Nat → Direction) :
    HiddenDescriptorContinuityThread D (semanticDescriptor initial) ExactEdge
      (package.canonicalWord D semanticStep semanticDescriptor familyOf
        semanticMove Represented Live ExactEdge Valid Supported initial
        branch) :=
  package.totality.admissibleThread D Represented Live ExactEdge Valid
    Supported (semanticDescriptor initial) (familyOf initial)
    (package.canonicalWord D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)
    (package.canonicalWordAdmissible D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)

section
omit [Fintype FamilyMove] [Fintype Direction]

/-- The accepting dead state is not being used as recovery evidence on a
canonical coherent branch. -/
theorem canonicalThread_nonempty (branch : Nat → Direction) :
    Nonempty
      (HiddenDescriptorContinuityThread D (semanticDescriptor initial)
        ExactEdge
        (package.canonicalWord D semanticStep semanticDescriptor familyOf
          semanticMove Represented Live ExactEdge Valid Supported initial
          branch)) :=
  ⟨package.canonicalThread D semanticStep semanticDescriptor familyOf
    semanticMove Represented Live ExactEdge Valid Supported initial branch⟩

/-- The chosen canonical thread remains synchronized with both the literal
semantic descriptor and its literal public family at every depth. -/
theorem canonicalThread_descriptor_eq_and_family_eq
    (branch : Nat → Direction) (n : Nat) :
    let word := package.canonicalWord D semanticStep semanticDescriptor
      familyOf semanticMove Represented Live ExactEdge Valid Supported initial
      branch
    let thread := package.canonicalThread D semanticStep semanticDescriptor
      familyOf semanticMove Represented Live ExactEdge Valid Supported initial
      branch
    thread.descriptor n =
        semanticDescriptor
          (familyAwareHiddenDescriptorSemanticAt initial semanticStep word n) ∧
      familyAwareHiddenDescriptorFamilyAt (familyOf initial) word n =
        familyOf
          (familyAwareHiddenDescriptorSemanticAt initial semanticStep word n) := by
  dsimp only
  apply package.semanticLifter.descriptor_eq_and_family_eq D semanticStep
    semanticDescriptor familyOf ExactEdge Valid initial (familyOf initial)
    (package.canonicalWord D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)
    (package.canonicalThread D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)
    rfl
  intro k
  exact (package.canonicalWordAdmissible D semanticStep semanticDescriptor
    familyOf semanticMove Represented Live ExactEdge Valid Supported initial
    branch).valid k

/-- The canonical live exact thread satisfies parity through the same
family-aware semantic synchronization, not through dead-state vacuity. -/
theorem canonicalThread_accepts (branch : Nat → Direction) :
    D.Accepts
      (package.canonicalThread D semanticStep semanticDescriptor familyOf
        semanticMove Represented Live ExactEdge Valid Supported initial branch
        |>.childCodeWord) := by
  apply package.semanticLifter.thread_accepts D semanticStep semanticDescriptor
    familyOf ExactEdge Valid initial (familyOf initial)
    (package.canonicalWord D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)
    (package.canonicalThread D semanticStep semanticDescriptor familyOf
      semanticMove Represented Live ExactEdge Valid Supported initial branch)
    rfl
  · intro n
    exact (package.canonicalWordAdmissible D semanticStep semanticDescriptor
      familyOf semanticMove Represented Live ExactEdge Valid Supported initial
      branch).valid n
  · exact package.semantic_branch_accepts

/-- The canonical exact thread is an actual run of the hidden transition
system. -/
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

end

/-- Final corrected generic join: one finite state-controlled winning public
tree exists, and every canonical coherent semantic branch has a nonempty live
exact thread. -/
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

end FamilyAwareGuardedHiddenDescriptorTreePackage

end

end DistributedSynthesis
