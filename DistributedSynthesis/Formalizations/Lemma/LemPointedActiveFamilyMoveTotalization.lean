/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemActiveFamilyMoveTotalization
import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyPointedFamilyTable

/-!
# Active-family totalization for pointed successors

The pointed relational route needs a total public move tree, but only active
families carry an actual descriptor.  We wrap genuine moves in `Option`:
`none` is valid exactly at inactive families, and has neither pointed support
nor an exact edge.  Hence a live branch can never use the fallback.

A canonical public tree chooses one genuine good move at every active family
and `none` elsewhere.  It depends only on the currently advertised public
family.  Feeding this tree to fixed-policy extraction removes any need for a
semantic-state source tree, while keeping descriptors, orientations, lanes,
and strict-leader information proof-side.
-/

namespace DistributedSynthesis

universe u v m b x

section


variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {Move : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]
variable [Inhabited Direction]

/-- Descriptor-pointed support lifted through `Option`.  The fallback has no
supported successor. -/
def ActiveFamilyOptionPointedSupported
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop) :
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      Option Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop
  | current, family, some move, direction, nextFamily =>
      Supported current family move direction nextFamily
  | _, _, none, _, _ => False

omit [Inhabited Direction] in
@[simp] theorem activeFamilyOptionPointedSupported_none
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (current : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity))
    (family nextFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (direction : Direction) :
    ¬ ActiveFamilyOptionPointedSupported D Supported current family none
      direction nextFamily := by
  simp [ActiveFamilyOptionPointedSupported]

omit [Inhabited Direction] in
@[simp] theorem activeFamilyOptionExactEdge_none
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (current target : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (direction : Direction) :
    ¬ ActiveFamilyOptionExactEdge D ExactEdge current none direction family
      target := by
  simp [ActiveFamilyOptionExactEdge]

namespace PointedHiddenDescriptorFamilyTotality

/-- Pointed one-step totality survives active-family optional completion.
The `none` validity case contradicts the current live descriptor, and its
support/exact relations are definitionally false. -/
def optionTotalization
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
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (totality : PointedHiddenDescriptorFamilyTotality D Represented Live
      ExactEdge Good Supported) :
    PointedHiddenDescriptorFamilyTotality D Represented Live
      (ActiveFamilyOptionExactEdge D ExactEdge)
      (ActiveFamilyOptionValid D Live Good)
      (ActiveFamilyOptionPointedSupported D Supported) where
  live_represented := totality.live_represented
  supported_exists := by
    intro current currentFamily move direction hlive hvalid
    cases move with
    | none => exact False.elim (hvalid ⟨current, hlive⟩)
    | some move =>
        exact totality.supported_exists current currentFamily move direction
          hlive hvalid
  target_live := by
    intro current currentFamily move direction nextFamily target hlive hvalid
      hsupported hedge
    cases move with
    | none => exact hsupported.elim
    | some move =>
        exact totality.target_live current currentFamily move direction
          nextFamily target hlive hvalid hsupported hedge
  covers := by
    intro current currentFamily move direction nextFamily hlive hvalid
      hsupported
    cases move with
    | none => exact hsupported.elim
    | some move =>
        exact totality.covers current currentFamily move direction nextFamily
          hlive hvalid hsupported

end PointedHiddenDescriptorFamilyTotality

/-! ## Canonical public tree without a semantic source -/

/-- Canonical optional move chosen from active-family existence alone. -/
noncomputable def pointedActiveFamilyCanonicalMove
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move)
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) : Option Move :=
  Classical.choose (activeFamilyOptionValid_total D Live Good active_good family)

theorem pointedActiveFamilyCanonicalMove_valid
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move)
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) :
    ActiveFamilyOptionValid D Live Good family
      (pointedActiveFamilyCanonicalMove D Live Good active_good family) :=
  Classical.choose_spec
    (activeFamilyOptionValid_total D Live Good active_good family)

/-- At a family containing a live descriptor, the canonical move is
necessarily a genuine `some`; it cannot use the inactive fallback. -/
theorem pointedActiveFamilyCanonicalMove_some_of_live
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move)
    (descriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (hlive : Live descriptor family) :
    ∃ move,
      pointedActiveFamilyCanonicalMove D Live Good active_good family =
          some move ∧
        Good family move := by
  have hvalid := pointedActiveFamilyCanonicalMove_valid D Live Good active_good
    family
  cases hmove : pointedActiveFamilyCanonicalMove D Live Good active_good family
    with
  | none =>
      exact False.elim
        (not_activeFamilyOptionValid_none_of_live D Live Good hlive
          (hmove ▸ hvalid))
  | some move =>
      refine ⟨move, rfl, ?_⟩
      simpa only [hmove, ActiveFamilyOptionValid] using hvalid

/-- Total public family tree selected solely from the current advertised
family.  Directions and hidden descriptors do not influence its labels. -/
noncomputable def pointedActiveFamilyCanonicalTree
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move)
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) :
    LabeledTree
      (HiddenDescriptorTreeObservation
        (Direction := Direction)
        (FamilyCode := HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity))) (Option Move) := fun node =>
  pointedActiveFamilyCanonicalMove D Live Good active_good
    (observableAt ((default : Direction), initialFamily) node).2

omit [Inhabited Direction] in
/-- The canonical active-family tree is valid at every public node. -/
theorem pointedActiveFamilyCanonicalTree_movesValid
    [Inhabited Direction]
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move)
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) :
    ObservableMovesValid ((default : Direction), initialFamily)
      (fun observation move ↦
        ActiveFamilyOptionValid D Live Good observation.2 move)
      (pointedActiveFamilyCanonicalTree D Live Good active_good
        initialFamily) := by
  intro node
  simpa only [pointedActiveFamilyCanonicalTree] using
    pointedActiveFamilyCanonicalMove_valid D Live Good active_good
      (observableAt ((default : Direction), initialFamily) node).2

end


/-! ## One-arrow fixed-policy extraction -/

universe c q mv dir dc i₁ i₂ o₁ o₂ pa

namespace DetParityAutomaton

variable {In₁ : Type i₁} {In₂ : Type i₂} {Out₁ : Type o₁} {Out₂ : Type o₂}
variable
  (A : DetParityAutomaton.{max i₁ i₂ o₁ o₂, pa}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

variable {Code : Type c} {MoveIdentity : Type q}
variable (D : DetParityAutomaton.{c, dc} Code)
variable {Move : Type mv} {Direction : Type dir}
variable [Fintype Code] [Fintype MoveIdentity]
variable [Fintype Move] [Fintype Direction] [Inhabited Direction]

variable
  (Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (Live : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    Move → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Good : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Move → Prop)
  (Supported : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    Move → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)

local instance : DecidableRel (ActiveFamilyOptionValid D Live Good) :=
  fun _ _ ↦ Classical.propDecidable _

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Active-family existence alone supplies the valid source tree required by
fixed-policy extraction.  The resulting one finite table wins the fixed
hidden policy and has a genuine pointed exact branch for every direction
word. -/
theorem exists_fixedPolicyPointedActiveFamilyTable
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (totality : PointedHiddenDescriptorFamilyTotality D Represented Live
      ExactEdge Good Supported)
    (initialLive : Live initialDescriptor initialFamily)
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move) :
    ∃ package : FixedPolicyPointedFamilyTablePackage A policy D Represented
        Live (ActiveFamilyOptionExactEdge D ExactEdge)
        (ActiveFamilyOptionValid D Live Good)
        (ActiveFamilyOptionPointedSupported D Supported)
        initialRoot initialDescriptor initialFamily,
      ∀ branch : Nat → Direction,
        Nonempty (HiddenDescriptorContinuityThread D initialDescriptor
          (ActiveFamilyOptionExactEdge D ExactEdge)
          (package.pointed.word D initialDescriptor initialFamily branch)) := by
  apply exists_fixedPolicyPointedFamilyTable_of_movesValid A policy D
    Represented Live (ActiveFamilyOptionExactEdge D ExactEdge)
    (ActiveFamilyOptionValid D Live Good)
    (ActiveFamilyOptionPointedSupported D Supported)
    initialRoot hinitial initialDescriptor initialFamily
    (totality.optionTotalization D Represented Live ExactEdge Good Supported)
    initialLive
    (pointedActiveFamilyCanonicalTree D Live Good active_good initialFamily)
  exact pointedActiveFamilyCanonicalTree_movesValid D Live Good active_good
    initialFamily

end

end DetParityAutomaton


end DistributedSynthesis
