/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorSemanticThreadLifting
import DistributedSynthesis.Formalizations.Lemma.LemGuardedSemanticFamilyTree

/-!
# Non-vacuous hidden-descriptor continuity

The accepting `dead` state of `hiddenDescriptorContinuitySystem` is necessary:
the universal resolution type contains many targets which are not exact
successors, and those resolutions must impose no parity obligation.  It also
means, however, that universal acceptance alone does **not** assert that a
single persistent descriptor thread exists.

This file isolates the exact additional condition.  A hidden descriptor is
represented at a public two-fibre family when it belongs to both components.
A valid public move and a supported public successor observation must provide
an exact, control-correct target for every descriptor carrying the concrete
`Live` provenance; live descriptors satisfy a model-provided `Represented`
predicate and exact
targets retain that provenance in the advertised next family.  Recursing this
one-step coverage constructs an infinite live thread.  Consequently the
acceptance theorem is no longer vacuous, and the existing semantic edge
lifter turns the same persistent thread into one literal semantic branch.

The extra `Live` predicate is essential.  Bare membership in finite images
does not itself provide one common semantic source; asking coverage for every
bare family member would reintroduce the forbidden rectangle/common-point
principle.  The concrete adapter should take `Live` to mean "has the retained
literal semantic provenance".  `Represented` is parameterized because a
mixed right-only family is `(image, ∅)` and a mixed left-only family is
`(∅, image)`; only live-both states use intersection membership.

`Supported` is deliberately separate from node-local `Valid`.  The ambient
branch alphabet may contain impossible `(direction, nextFamily)` pairs.  Such
pairs may harmlessly have no live thread.  On every pair representing a real
model transition, the concrete adapter must prove `Supported`.  Taking
`Supported := True` recovers the stronger all-observations totality law.
-/

namespace DistributedSynthesis

universe u v m b x y z

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable {Semantic : Type y} {SemanticDirection : Type z}
variable [Fintype Code] [Fintype MoveIdentity]

/-- The public family code used below: the two finite local-fibre images of
the complete hidden descriptor. -/
abbrev HiddenDescriptorTwoFibreFamily :=
  FiniteTwoFibreCode
    (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity))

noncomputable instance hiddenDescriptorTwoFibreFamily_decidableEq :
    DecidableEq
      (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity)) :=
  Classical.decEq _

/-- A descriptor is genuinely represented by a two-fibre family when it is
present in both local images.  This is the pointed invariant which the bare
two-sorted family run does not retain. -/
def HiddenDescriptorRepresented
    (descriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) : Prop :=
  descriptor ∈ family.1 ∧ descriptor ∈ family.2

/-- The family visible at time `n`: initially `initialFamily`, and thereafter
the family advertised by the preceding public letter. -/
def hiddenDescriptorFamilyAt
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity)))) :
    Nat → HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity)
  | 0 => initialFamily
  | n + 1 => (word n).2.2

@[simp] theorem hiddenDescriptorFamilyAt_zero
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity)))) :
    hiddenDescriptorFamilyAt D initialFamily word 0 = initialFamily :=
  rfl

@[simp] theorem hiddenDescriptorFamilyAt_succ
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))))
    (n : Nat) :
    hiddenDescriptorFamilyAt D initialFamily word (n + 1) = (word n).2.2 :=
  rfl

/-- Model-independent one-step totality interface.

`Valid` checks the family move at the current public family.  `Supported`
marks those successor observations which claim to be genuine model
transitions.  `Live` retains the proof-side common semantic origin.  Coverage
is required only for live descriptors on supported observations. -/
structure HiddenDescriptorFamilyTotality
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
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop) : Prop where
  live_represented : ∀ current currentFamily,
    Live current currentFamily →
      Represented current currentFamily
  target_live : ∀ current currentFamily move direction nextFamily target,
    Live current currentFamily →
    Valid currentFamily move →
    Supported currentFamily move direction nextFamily →
    ExactEdge current move direction nextFamily target →
    Live target nextFamily
  covers : ∀ current currentFamily move direction nextFamily,
    Live current currentFamily →
    Valid currentFamily move →
    Supported currentFamily move direction nextFamily →
    ∃ target,
      ExactEdge current move direction nextFamily target ∧
        target.control = D.step current.control target.code

/-- A fixed public word follows the node-local validity law and uses only
successor observations declared supported by the concrete model. -/
structure HiddenDescriptorFamilyWordAdmissible
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity)))) : Prop where
  initial_live : Live initialDescriptor initialFamily
  valid : ∀ n,
    Valid (hiddenDescriptorFamilyAt D initialFamily word n) (word n).1
  supported : ∀ n,
    Supported (hiddenDescriptorFamilyAt D initialFamily word n) (word n).1
      (word n).2.1 (word n).2.2

namespace HiddenDescriptorFamilyTotality

variable
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
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
  (Supported : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
    HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Prop)
  (totality : HiddenDescriptorFamilyTotality D Represented Live ExactEdge Valid
    Supported)
  (initialDescriptor : HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (initialFamily : HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))
  (word : OmegaWord (HiddenDescriptorFamilyLetter
    (FamilyMove := FamilyMove) (Direction := Direction)
    (FamilyCode := HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))))
  (hadmissible : HiddenDescriptorFamilyWordAdmissible D Live initialDescriptor
    initialFamily Valid Supported word)

/-- One chosen covered target from a represented current descriptor. -/
noncomputable def nextDescriptor
    (n : Nat)
    (current : { descriptor : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) //
      Live descriptor
        (hiddenDescriptorFamilyAt D initialFamily word n) }) :
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) :=
  Classical.choose (totality.covers current.1
    (hiddenDescriptorFamilyAt D initialFamily word n) (word n).1
    (word n).2.1 (word n).2.2 current.2 (hadmissible.valid n)
    (hadmissible.supported n))

theorem nextDescriptor_spec
    (n : Nat)
    (current : { descriptor : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) //
      Live descriptor
        (hiddenDescriptorFamilyAt D initialFamily word n) }) :
    ExactEdge current.1 (word n).1 (word n).2.1 (word n).2.2
        (HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid
          Supported totality initialDescriptor initialFamily word hadmissible n
          current) ∧
      (HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid
          Supported totality initialDescriptor initialFamily word hadmissible n
          current).control =
        D.step current.1.control
          (HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid
            Supported totality initialDescriptor initialFamily word hadmissible
            n current).code :=
  Classical.choose_spec (totality.covers current.1
    (hiddenDescriptorFamilyAt D initialFamily word n) (word n).1
    (word n).2.1 (word n).2.2 current.2 (hadmissible.valid n)
    (hadmissible.supported n))

/-- The chosen covered target, packaged with its membership in the next
two-fibre family. -/
noncomputable def nextMember
    (n : Nat)
    (current : { descriptor : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) //
      Live descriptor
        (hiddenDescriptorFamilyAt D initialFamily word n) }) :
    { descriptor : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) //
      Live descriptor
        (hiddenDescriptorFamilyAt D initialFamily word (n + 1)) } := by
  let target := HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid
    Supported totality initialDescriptor initialFamily word hadmissible n current
  refine ⟨target, ?_⟩
  rw [hiddenDescriptorFamilyAt_succ]
  exact totality.target_live current.1
    (hiddenDescriptorFamilyAt D initialFamily word n) (word n).1
    (word n).2.1 (word n).2.2 target current.2 (hadmissible.valid n)
    (hadmissible.supported n)
    (HiddenDescriptorFamilyTotality.nextDescriptor_spec D Represented Live ExactEdge Valid
      Supported totality initialDescriptor initialFamily word hadmissible n
      current).1

/-- The recursively retained pointed family member. -/
noncomputable def memberAt : ∀ n,
    { descriptor : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) //
      Live descriptor
        (hiddenDescriptorFamilyAt D initialFamily word n) }
  | 0 => ⟨initialDescriptor, hadmissible.initial_live⟩
  | n + 1 => HiddenDescriptorFamilyTotality.nextMember D Represented Live ExactEdge Valid
      Supported totality initialDescriptor initialFamily word hadmissible n
        (memberAt n)

@[simp] theorem memberAt_zero :
    (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible 0).1 =
        initialDescriptor :=
  rfl

/-- Every point of the recursively retained provenance thread is represented
in both components of the current public family. -/
theorem memberAt_represented (n : Nat) :
    Represented
      (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
        totality initialDescriptor initialFamily word hadmissible n).1
      (hiddenDescriptorFamilyAt D initialFamily word n) :=
  totality.live_represented _ _
    (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible n).2

theorem memberAt_edge (n : Nat) :
    ExactEdge
      (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
        totality initialDescriptor initialFamily word hadmissible n).1
      (word n).1 (word n).2.1 (word n).2.2
      (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
        totality initialDescriptor initialFamily word hadmissible (n + 1)).1 := by
  change ExactEdge
    (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible n).1
    (word n).1 (word n).2.1 (word n).2.2
    (HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible n
        (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
          totality initialDescriptor initialFamily word hadmissible n))
  exact (HiddenDescriptorFamilyTotality.nextDescriptor_spec D Represented Live ExactEdge Valid
    Supported totality initialDescriptor initialFamily word hadmissible n
      (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
        totality initialDescriptor initialFamily word hadmissible n)).1

theorem memberAt_controlStep (n : Nat) :
    (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible
      (n + 1)).1.control =
      D.step
        (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
          totality initialDescriptor initialFamily word hadmissible n).1.control
        (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
          totality initialDescriptor initialFamily word hadmissible
          (n + 1)).1.code := by
  change
    (HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible n
        (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
          totality initialDescriptor initialFamily word hadmissible n)).control =
      D.step
        (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
          totality initialDescriptor initialFamily word hadmissible n).1.control
        (HiddenDescriptorFamilyTotality.nextDescriptor D Represented Live ExactEdge Valid
          Supported totality initialDescriptor initialFamily word hadmissible n
            (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
              totality initialDescriptor initialFamily word hadmissible n)).code
  exact (HiddenDescriptorFamilyTotality.nextDescriptor_spec D Represented Live ExactEdge Valid
    Supported totality initialDescriptor initialFamily word hadmissible n
      (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
        totality initialDescriptor initialFamily word hadmissible n)).2

/-- Every admissible word has a persistent exact descriptor thread.  This is
the non-vacuity theorem missing from universal acceptance by itself. -/
noncomputable def admissibleThread :
    HiddenDescriptorContinuityThread D initialDescriptor ExactEdge word where
  descriptor := fun n =>
    (HiddenDescriptorFamilyTotality.memberAt D Represented Live ExactEdge Valid Supported
      totality initialDescriptor initialFamily word hadmissible n).1
  initial := HiddenDescriptorFamilyTotality.memberAt_zero D Represented Live ExactEdge Valid
    Supported totality initialDescriptor initialFamily word hadmissible
  exactEdge := HiddenDescriptorFamilyTotality.memberAt_edge D Represented Live ExactEdge Valid
    Supported totality initialDescriptor initialFamily word hadmissible
  controlStep := HiddenDescriptorFamilyTotality.memberAt_controlStep D Represented Live
    ExactEdge Valid Supported totality initialDescriptor initialFamily word
    hadmissible

include totality hadmissible
theorem nonempty_admissibleThread :
    Nonempty
      (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge word) :=
  ⟨HiddenDescriptorFamilyTotality.admissibleThread D Represented Live ExactEdge Valid
    Supported totality initialDescriptor initialFamily word hadmissible⟩

/-- The canonical covered thread is a run which stays live at every depth. -/
theorem admissibleThread_isRun :
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).IsRun
      word
      (HiddenDescriptorContinuityThread.stateAt D initialDescriptor ExactEdge
        word (HiddenDescriptorFamilyTotality.admissibleThread D Represented Live ExactEdge Valid
          Supported totality initialDescriptor initialFamily word
          hadmissible)) :=
  HiddenDescriptorContinuityThread.isRun D initialDescriptor ExactEdge word _

/-- On an admissible word, the hidden monitor's exact characterization is
provably non-vacuous. -/
theorem universalRunDPA_accepts_iff_nonvacuous
    (hinitialControl : initialDescriptor.control = D.initial) :
    ((hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge)
        |>.universalRunDPA.Accepts word) ↔
      Nonempty
          (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
            word) ∧
        ∀ thread : HiddenDescriptorContinuityThread D initialDescriptor
            ExactEdge word,
          D.Accepts thread.childCodeWord := by
  rw [hiddenDescriptorContinuitySystem_universalRunDPA_accepts_iff D
    initialDescriptor hinitialControl ExactEdge word]
  constructor
  · intro hthreads
    exact ⟨HiddenDescriptorFamilyTotality.nonempty_admissibleThread D Represented Live
      ExactEdge Valid Supported totality initialDescriptor initialFamily word
      hadmissible, hthreads⟩
  · exact fun h => h.2

end HiddenDescriptorFamilyTotality

/-! ## The canonical coherent branch of a totalized family tree -/

variable [Inhabited Direction]

/-- Public word read on the canonical coherent observation branch of a
guarded semantic family tree.  False advertised-family branches remain in
the total tree, but do not occur in this word. -/
noncomputable def guardedHiddenDescriptorFamilyWord
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (semanticMove : Semantic → FamilyMove)
    (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (branch : Nat → Direction) :
    OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))) :=
  observableThreadWord
    (guardedSemanticFamilyTree initial semanticStep familyOf semanticMove
      Valid htotal)
    (guardedSemanticFamilyObservationBranch initial semanticStep familyOf
      branch)

/-- Along the canonical branch, the public current family is exactly the
family of the recursively reached semantic state. -/
theorem hiddenDescriptorFamilyAt_guardedWord
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (semanticMove : Semantic → FamilyMove)
    (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (branch : Nat → Direction) : ∀ n,
    hiddenDescriptorFamilyAt D (familyOf initial)
      (guardedHiddenDescriptorFamilyWord D initial semanticStep familyOf
        semanticMove Valid htotal branch) n =
      familyOf (guardedSemanticFamilyIterate initial semanticStep branch n) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

/-- The canonical branch of `guardedSemanticFamilyTree` satisfies exactly
the admissibility assumptions consumed by the non-vacuity theorem.

This is the reusable join with the totalization layer: no coverage is asked
on a false advertised family, while every direction branch has its canonical
coherent family branch. -/
noncomputable def guardedHiddenDescriptorFamilyWordAdmissible
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (semanticMove : Semantic → FamilyMove)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (hinitial : Live (semanticDescriptor initial) (familyOf initial))
    (hvalid : ∀ state, Valid (familyOf state) (semanticMove state))
    (hsupported : ∀ state direction,
      Supported (familyOf state) (semanticMove state) direction
        (familyOf (semanticStep state direction)))
    (branch : Nat → Direction) :
    HiddenDescriptorFamilyWordAdmissible D Live (semanticDescriptor initial)
      (familyOf initial) Valid Supported
      (guardedHiddenDescriptorFamilyWord D initial semanticStep familyOf
        semanticMove Valid htotal branch) where
  initial_live := hinitial
  valid := by
    intro n
    rw [hiddenDescriptorFamilyAt_guardedWord D initial semanticStep familyOf
      semanticMove Valid htotal branch n]
    change Valid _
      (guardedSemanticFamilyTree initial semanticStep familyOf semanticMove
        Valid htotal
        (branchNode
          (guardedSemanticFamilyObservationBranch initial semanticStep familyOf
            branch) n))
    rw [guardedSemanticFamilyTree_branchNode initial semanticStep familyOf
      semanticMove Valid htotal branch n]
    exact hvalid _
  supported := by
    intro n
    rw [hiddenDescriptorFamilyAt_guardedWord D initial semanticStep familyOf
      semanticMove Valid htotal branch n]
    change Supported _
      (guardedSemanticFamilyTree initial semanticStep familyOf semanticMove
        Valid htotal
        (branchNode
          (guardedSemanticFamilyObservationBranch initial semanticStep familyOf
            branch) n))
      (branch n)
      (familyOf
        (guardedSemanticFamilyIterate initial semanticStep branch (n + 1)))
    rw [guardedSemanticFamilyTree_branchNode initial semanticStep familyOf
      semanticMove Valid htotal branch n]
    change Supported _ _ _
      (familyOf
        (semanticStep
          (guardedSemanticFamilyIterate initial semanticStep branch n)
          (branch n)))
    exact hsupported _ _

/-! ## Coupling non-vacuity to one-origin semantic lifting -/

/-- The two obligations needed at the model boundary: supported public
letters are total on represented descriptors, and every exact edge lifts
from the current semantic representative. -/
structure HiddenDescriptorFamilySemanticGuard
    (semanticStep : Semantic → SemanticDirection → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
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
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop) where
  totality : HiddenDescriptorFamilyTotality D Represented Live ExactEdge Valid
    Supported
  semanticLifter : HiddenDescriptorSemanticEdgeLifter D semanticStep
    semanticDescriptor ExactEdge

namespace HiddenDescriptorFamilySemanticGuard

variable
  (semanticStep : Semantic → SemanticDirection → Semantic)
  (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
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
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
  (Supported : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
    HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Prop)
  (guard : HiddenDescriptorFamilySemanticGuard D semanticStep
    semanticDescriptor Represented Live ExactEdge Valid Supported)
  (initial : Semantic)
  (initialFamily : HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity))
  (word : OmegaWord (HiddenDescriptorFamilyLetter
    (FamilyMove := FamilyMove) (Direction := Direction)
    (FamilyCode := HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))))
  (hadmissible : HiddenDescriptorFamilyWordAdmissible D Live
    (semanticDescriptor initial) initialFamily Valid Supported word)

omit [Inhabited Direction] in
/-- The concrete live thread supplied by coverage is the positive-time
descriptor stream of one literal semantic branch. -/
theorem admissibleThread_childDescriptorWord_eq :
    (fun n =>
      (HiddenDescriptorFamilyTotality.admissibleThread D Represented Live ExactEdge Valid
        Supported guard.totality (semanticDescriptor initial) initialFamily
        word hadmissible)
        |>.descriptor (n + 1)) =
      fun n => semanticDescriptor
        ((branchNode
          (HiddenDescriptorSemanticEdgeLifter.liftedBranch
            (D := D) (semanticStep := semanticStep)
            (semanticDescriptor := semanticDescriptor) (initial := initial)
            (ExactEdge := ExactEdge) (lifter := guard.semanticLifter)
            (word := word)
            (thread := HiddenDescriptorFamilyTotality.admissibleThread D Represented Live
              ExactEdge Valid Supported guard.totality
              (semanticDescriptor initial) initialFamily word hadmissible))
          (n + 1)).foldl semanticStep initial) := by
  exact HiddenDescriptorSemanticEdgeLifter.childDescriptorWord_eq
    (D := D) (semanticStep := semanticStep)
    (semanticDescriptor := semanticDescriptor) (initial := initial)
    (ExactEdge := ExactEdge) (lifter := guard.semanticLifter) (word := word)
    (thread := HiddenDescriptorFamilyTotality.admissibleThread D Represented Live ExactEdge
      Valid Supported guard.totality (semanticDescriptor initial)
      initialFamily word hadmissible)

end HiddenDescriptorFamilySemanticGuard

end

end DistributedSynthesis
