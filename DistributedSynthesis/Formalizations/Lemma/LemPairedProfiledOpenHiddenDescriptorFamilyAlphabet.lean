/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyProvenanceReindexing
import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedReindexing
import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSemanticLocalFibres
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedHiddenDescriptorContinuity

/-!
# A fixed alphabet for hidden-descriptor fibre moves

The finite family move must have a type determined by finite data, not by a
chosen semantic witness.  The hidden descriptor already stores the old finite
indexed move.  Its right and left components therefore canonically determine
the source-root types and block monitors used by the two descriptor unions.

Ill-shaped descriptors have an empty root type.  They remain in the ambient
finite descriptor type, but contribute no root to an attained live semantic
fibre.  This makes the definitions total without inventing a fallback source,
orientation, or leader bit.

The last definitions package the two weak union moves over one finite
two-fibre code.  Semantic witnesses are used later only to prove the strong
provenance law for an attained code; they do not occur in this runtime move
alphabet.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Full finite hidden descriptors -/

/-- The fixed hidden descriptor used by the source-indexed construction.  Its
move identity is the old finite semantic move, not the new union controller. -/
abbrev ProfiledOpenIndexedOldMoveHiddenDescriptor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  ProfiledOpenIndexedHiddenDescriptor A
    (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A) initialCode

/-- The finite public carrier of the two local hidden-descriptor images. -/
abbrev ProfiledOpenIndexedHiddenDescriptorFamilyCode
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  FiniteTwoFibreCode
    (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode)

/-! ## Canonical root types read from the old move identity -/

/-- Right roots carried by a finite old move.  Non-right moves contribute no
root, rather than an arbitrary fallback right source. -/
abbrev ProfiledOpenCanonicalRightRootOfMove (_I : Type i) :
    ProfiledOpenClassifiedMove A → Type (max i u v x y s)
  | .right source _ => ULift.{max i u v x y s} { root // root ∈ source.1 }
  | .sink | .left _ _ => ULift.{max i u v x y s} PEmpty

/-- Left mirror of `ProfiledOpenCanonicalRightRootOfMove`. -/
abbrev ProfiledOpenCanonicalLeftRootOfMove (_I : Type i) :
    ProfiledOpenClassifiedMove A → Type (max i u v x y s)
  | .left source _ => ULift.{max i u v x y s} { root // root ∈ source.1 }
  | .sink | .right _ _ => ULift.{max i u v x y s} PEmpty

/-- Canonical right root type of a full hidden descriptor. -/
abbrev ProfiledOpenHiddenDescriptorRightRoot
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) :=
  ProfiledOpenCanonicalRightRootOfMove A I descriptor.moveIdentity.1

/-- Canonical left root type of a full hidden descriptor. -/
abbrev ProfiledOpenHiddenDescriptorLeftRoot
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) :=
  ProfiledOpenCanonicalLeftRootOfMove A I descriptor.moveIdentity.2

noncomputable instance profiledOpenCanonicalRightRootOfMove_fintype
    (move : ProfiledOpenClassifiedMove A) :
    Fintype (ProfiledOpenCanonicalRightRootOfMove A I move) := by
  classical
  cases move <;> infer_instance

noncomputable instance profiledOpenCanonicalLeftRootOfMove_fintype
    (move : ProfiledOpenClassifiedMove A) :
    Fintype (ProfiledOpenCanonicalLeftRootOfMove A I move) := by
  classical
  cases move <;> infer_instance

noncomputable instance profiledOpenHiddenDescriptorRightRoot_decidableEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) :
    DecidableEq (ProfiledOpenHiddenDescriptorRightRoot A (I := I)
      descriptor) :=
  Classical.decEq _

noncomputable instance profiledOpenHiddenDescriptorLeftRoot_decidableEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) :
    DecidableEq (ProfiledOpenHiddenDescriptorLeftRoot A (I := I)
      descriptor) :=
  Classical.decEq _

/-! ## Canonical monitors and finite weak table laws -/

/-- The right block monitor determined by the descriptor's old right move. -/
noncomputable def profiledOpenCanonicalRightMonitorOfMove (_I : Type i) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenCanonicalRightRootOfMove A _I move →
        BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A)
          Out₁
  | .right source _, root =>
      profiledOpenRightClassifiedRootMonitor A root.down.1
  | .sink, root => nomatch root.down
  | .left _ _, root => nomatch root.down

/-- The canonical left block monitor. -/
noncomputable def profiledOpenCanonicalLeftMonitorOfMove (_I : Type i) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenCanonicalLeftRootOfMove A _I move →
        BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A)
          Out₂
  | .left source _, root =>
      profiledOpenLeftClassifiedRootMonitor A root.down.1
  | .sink, root => nomatch root.down
  | .right _ _, root => nomatch root.down

/-- Descriptor-indexed right monitor, with no semantic representative in its
type. -/
noncomputable abbrev profiledOpenHiddenDescriptorRightMonitor
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (root : ProfiledOpenHiddenDescriptorRightRoot A descriptor) :=
  profiledOpenCanonicalRightMonitorOfMove A I
    descriptor.moveIdentity.1 root

/-- Descriptor-indexed left monitor. -/
noncomputable abbrev profiledOpenHiddenDescriptorLeftMonitor
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (root : ProfiledOpenHiddenDescriptorLeftRoot A descriptor) :=
  profiledOpenCanonicalLeftMonitorOfMove A I
    descriptor.moveIdentity.2 root

/-- Insert a root of a concrete right source into the canonical root type of
a descriptor whose old move is propositionally that right move.  Keeping the
equality explicit avoids treating an arbitrary representative of the same
finite image as the current semantic source. -/
noncomputable def profiledOpenCanonicalRightRootOfEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.right source table)
    (root : { root // root ∈ source.1 }) :
    ProfiledOpenCanonicalRightRootOfMove A I move := by
  rw [hmove]
  exact ULift.up root

noncomputable def profiledOpenHiddenDescriptorRightRootOfEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : descriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (root : { root // root ∈ source.1 }) :
    ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor :=
  profiledOpenCanonicalRightRootOfEqOfMove A (I := I)
    descriptor.moveIdentity.1 source table hmove root

/-- Left mirror of `profiledOpenHiddenDescriptorRightRootOfEq`. -/
noncomputable def profiledOpenCanonicalLeftRootOfEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.left source table)
    (root : { root // root ∈ source.1 }) :
    ProfiledOpenCanonicalLeftRootOfMove A I move := by
  rw [hmove]
  exact ULift.up root

noncomputable def profiledOpenHiddenDescriptorLeftRootOfEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : descriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (root : { root // root ∈ source.1 }) :
    ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor :=
  profiledOpenCanonicalLeftRootOfEqOfMove A (I := I)
    descriptor.moveIdentity.2 source table hmove root

/-- Read a concrete right-source root from the canonical root of an arbitrary
finite classified move.  Stating the dependent transport at the move level
keeps elimination independent of the larger hidden descriptor record. -/
noncomputable def profiledOpenCanonicalRightRootToEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : move =
      ProfiledOpenClassifiedMove.right source table)
    (root : ProfiledOpenCanonicalRightRootOfMove A I move) :
    { root // root ∈ source.1 } := by
  rw [hmove] at root
  exact root.down

noncomputable def profiledOpenCanonicalLeftRootToEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : move =
      ProfiledOpenClassifiedMove.left source table)
    (root : ProfiledOpenCanonicalLeftRootOfMove A I move) :
    { root // root ∈ source.1 } := by
  rw [hmove] at root
  exact root.down

/-- Descriptor wrapper of the move-level right projection. -/
noncomputable def profiledOpenHiddenDescriptorRightRootToEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : descriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (root : ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor) :
    { root // root ∈ source.1 } :=
  profiledOpenCanonicalRightRootToEqOfMove A (I := I)
    descriptor.moveIdentity.1
    source table hmove root

/-- Descriptor wrapper of the move-level left projection. -/
noncomputable def profiledOpenHiddenDescriptorLeftRootToEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : descriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (root : ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor) :
    { root // root ∈ source.1 } :=
  profiledOpenCanonicalLeftRootToEqOfMove A (I := I)
    descriptor.moveIdentity.2
    source table hmove root

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenCanonicalRightRootToEq_rootOfEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.right source table)
    (root : { root // root ∈ source.1 }) :
    profiledOpenCanonicalRightRootToEqOfMove A (I := I) move source table hmove
        (profiledOpenCanonicalRightRootOfEqOfMove A (I := I) move source table
          hmove root) = root := by
  cases hmove
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenCanonicalLeftRootToEq_rootOfEqOfMove
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.left source table)
    (root : { root // root ∈ source.1 }) :
    profiledOpenCanonicalLeftRootToEqOfMove A (I := I) move source table hmove
        (profiledOpenCanonicalLeftRootOfEqOfMove A (I := I) move source table
          hmove root) = root := by
  cases hmove
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenHiddenDescriptorRightRootToEq_rootOfEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : descriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (root : { root // root ∈ source.1 }) :
    profiledOpenHiddenDescriptorRightRootToEq A descriptor source table hmove
        (profiledOpenHiddenDescriptorRightRootOfEq A descriptor source table
          hmove root) = root :=
  profiledOpenCanonicalRightRootToEq_rootOfEqOfMove A (I := I)
    descriptor.moveIdentity.1 source table hmove root

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : descriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (root : { root // root ∈ source.1 }) :
    profiledOpenHiddenDescriptorLeftRootToEq A descriptor source table hmove
        (profiledOpenHiddenDescriptorLeftRootOfEq A descriptor source table
          hmove root) = root :=
  profiledOpenCanonicalLeftRootToEq_rootOfEqOfMove A (I := I)
    descriptor.moveIdentity.2 source table hmove root

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenCanonicalRightMonitor_eq_ofEq
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.right source table)
    (root : ProfiledOpenCanonicalRightRootOfMove A I move) :
    profiledOpenCanonicalRightMonitorOfMove A I move root =
      profiledOpenRightClassifiedRootMonitor A
        (profiledOpenCanonicalRightRootToEqOfMove A (I := I) move source table hmove
          root).1 := by
  cases hmove
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenCanonicalLeftMonitor_eq_ofEq
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.left source table)
    (root : ProfiledOpenCanonicalLeftRootOfMove A I move) :
    profiledOpenCanonicalLeftMonitorOfMove A I move root =
      profiledOpenLeftClassifiedRootMonitor A
        (profiledOpenCanonicalLeftRootToEqOfMove A (I := I) move source table hmove
          root).1 := by
  cases hmove
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenHiddenDescriptorRightMonitor_eq_ofEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : descriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (root : ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor) :
    profiledOpenHiddenDescriptorRightMonitor A descriptor root =
      profiledOpenRightClassifiedRootMonitor A
        (profiledOpenHiddenDescriptorRightRootToEq A descriptor source table
          hmove root).1 := by
  exact profiledOpenCanonicalRightMonitor_eq_ofEq A (I := I)
    descriptor.moveIdentity.1 source table hmove root

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenHiddenDescriptorLeftMonitor_eq_ofEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : descriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (root : ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor) :
    profiledOpenHiddenDescriptorLeftMonitor A descriptor root =
      profiledOpenLeftClassifiedRootMonitor A
        (profiledOpenHiddenDescriptorLeftRootToEq A descriptor source table
          hmove root).1 := by
  exact profiledOpenCanonicalLeftMonitor_eq_ofEq A (I := I)
    descriptor.moveIdentity.2 source table hmove root

/-- Weak finite right table law at the old-move level.  Isolating the
dependent match here makes later source equalities ordinary constructor
transport, rather than elimination through a larger hidden descriptor. -/
def profiledOpenCanonicalRightWeakAllowedOfMove (_I : Type i) :
    (move : ProfiledOpenClassifiedMove A) →
      (((ProfiledOpenCanonicalRightRootOfMove A _I move × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop
  | .right source _, responses =>
      ProfiledOpenRightClassifiedTableAllowed A source (fun input =>
        responses ((ULift.up input.1.1, input.1.2), input.2))
  | .sink, _ | .left _ _, _ => False

/-- Weak finite right table law read canonically from the old move identity.
It is false on an ill-shaped descriptor, which is harmless because such a
descriptor has no right root in an attained live fibre. -/
def ProfiledOpenHiddenDescriptorRightWeakAllowed
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  profiledOpenCanonicalRightWeakAllowedOfMove A I
    descriptor.moveIdentity.1 responses

/-- Move-level weak left table law. -/
def profiledOpenCanonicalLeftWeakAllowedOfMove (_I : Type i) :
    (move : ProfiledOpenClassifiedMove A) →
      (((ProfiledOpenCanonicalLeftRootOfMove A _I move × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop
  | .left source _, responses =>
      ProfiledOpenLeftClassifiedTableAllowed A source (fun input =>
        responses ((ULift.up input.1.1, input.1.2), input.2))
  | .sink, _ | .right _ _, _ => False

/-- Weak left table law. -/
def ProfiledOpenHiddenDescriptorLeftWeakAllowed
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  profiledOpenCanonicalLeftWeakAllowedOfMove A I
    descriptor.moveIdentity.2 responses

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Move-level transport of a concrete right table law. -/
theorem profiledOpenCanonicalRightWeakAllowedOfMove_ofEq
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.right source table)
    (responses :
      ((ProfiledOpenCanonicalRightRootOfMove A I move × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A)
    (hallowed : ProfiledOpenRightClassifiedTableAllowed A source (fun input =>
      responses
        ((profiledOpenCanonicalRightRootOfEqOfMove A (I := I) move source
            table hmove input.1.1,
          input.1.2), input.2))) :
    profiledOpenCanonicalRightWeakAllowedOfMove A I move responses := by
  cases hmove
  exact hallowed

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Move-level transport of a concrete left table law. -/
theorem profiledOpenCanonicalLeftWeakAllowedOfMove_ofEq
    (move : ProfiledOpenClassifiedMove A)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : move = ProfiledOpenClassifiedMove.left source table)
    (responses :
      ((ProfiledOpenCanonicalLeftRootOfMove A I move × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A)
    (hallowed : ProfiledOpenLeftClassifiedTableAllowed A source (fun input =>
      responses
        ((profiledOpenCanonicalLeftRootOfEqOfMove A (I := I) move source
            table hmove input.1.1,
          input.1.2), input.2))) :
    profiledOpenCanonicalLeftWeakAllowedOfMove A I move responses := by
  cases hmove
  exact hallowed

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Transport a concrete right-source table law into the canonical hidden
descriptor presentation.  The equality is kept explicit: no representative
source is selected from the public finite image. -/
theorem profiledOpenHiddenDescriptorRightWeakAllowed_ofEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (hmove : descriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right source table)
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A)
    (hallowed : ProfiledOpenRightClassifiedTableAllowed A source (fun input =>
      responses
        ((profiledOpenHiddenDescriptorRightRootOfEq A descriptor source table
            hmove input.1.1,
          input.1.2), input.2))) :
    ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor responses := by
  exact profiledOpenCanonicalRightWeakAllowedOfMove_ofEq A (I := I)
    descriptor.moveIdentity.1 source table hmove responses hallowed

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of
`profiledOpenHiddenDescriptorRightWeakAllowed_ofEq`. -/
theorem profiledOpenHiddenDescriptorLeftWeakAllowed_ofEq
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (hmove : descriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left source table)
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A)
    (hallowed : ProfiledOpenLeftClassifiedTableAllowed A source (fun input =>
      responses
        ((profiledOpenHiddenDescriptorLeftRootOfEq A descriptor source table
            hmove input.1.1,
          input.1.2), input.2))) :
    ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor responses := by
  exact profiledOpenCanonicalLeftWeakAllowedOfMove_ofEq A (I := I)
    descriptor.moveIdentity.2 source table hmove responses hallowed

/-! ## Fixed move alphabet over one two-fibre code -/

/-- The active right descriptor carrier of a finite family code. -/
abbrev ProfiledOpenHiddenDescriptorRightCarrier
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  { descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode // descriptor ∈ family.1 }

/-- Active left descriptor carrier. -/
abbrev ProfiledOpenHiddenDescriptorLeftCarrier
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  { descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode // descriptor ∈ family.2 }

noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    Fintype (ProfiledOpenHiddenDescriptorRightCarrier A family) := by
  classical
  infer_instance

noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    DecidableEq (ProfiledOpenHiddenDescriptorRightCarrier A family) :=
  Classical.decEq _

noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    Fintype (ProfiledOpenHiddenDescriptorLeftCarrier A family) := by
  classical
  infer_instance

noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    DecidableEq (ProfiledOpenHiddenDescriptorLeftCarrier A family) :=
  Classical.decEq _

/-- One finite right union move for the descriptor family stored in `family`.
The semantic provenance certificate is deliberately not part of this runtime
alphabet. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorRightFamilyMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  FiniteDescriptorFamilyAllowedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family =>
      ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor.1)
    (fun descriptor root =>
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (fun descriptor responses =>
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)

/-- Left union move over the second family component. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorLeftFamilyMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  FiniteDescriptorFamilyAllowedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family =>
      ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor.1)
    (fun descriptor root =>
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (fun descriptor responses =>
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)

/-- Both independently typed union tables selected at one public family. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedFamilyMoveAt
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  ProfiledOpenHiddenDescriptorRightFamilyMove A family ×
    ProfiledOpenHiddenDescriptorLeftFamilyMove A family

/-- A single fixed finite move alphabet.  The family tag is included in the
finite value; validity later requires it to equal the current public code. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedFamilyMove
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode,
    ProfiledOpenHiddenDescriptorPairedFamilyMoveAt A family

set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) :
    Fintype (ProfiledOpenHiddenDescriptorPairedFamilyMove A initialCode) := by
  classical
  infer_instance

/-! ## Root-pinned fixed alphabet

The weak alphabet above is sufficient for finite successor-table laws, but it
does not remember the exact first record used by the source-indexed semantic
extraction.  Reindexing an already extracted pinned controller is not a cast:
its monitor state contains that record.  The sound fixed alphabet therefore
stores the finite record table as part of the move value and performs the
root pin *inside* the canonical descriptor-indexed monitor.

This is still a finite alphabet.  Different exact histories with the same
two-fibre code may choose different record tables; the later input-free
rationalization chooses among these finitely many values.  In particular we
do not select one semantic source, or one table, once and for all for an image
code. -/

/-- First record already stored at the root of an old finite right table.
The extra member-controller flag only selects the requested receiver root; it
does not alter the old table's sender component. -/
noncomputable def profiledOpenCanonicalRightExpectedOfMove (_I : Type i) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenCanonicalRightRootOfMove A _I move →
        In₂ × In₁ →
          RealizedBlockRound In₂ In₁
            (ProfiledOpenRightClassifiedOutput A) Out₁
  | .right source table, root, input =>
      let monitors := fun member : { root // root ∈ source.1 } =>
        profiledOpenRightClassifiedRootMonitor A member.1
      let controller := finiteRootMemberController monitors
        table.toTransitionRationalTree root.down
      narrowedRecord (monitors root.down) (controller.labeledTree [])
        (monitors root.down).initial input
  | .sink, root, _ => nomatch root.down
  | .left _ _, root, _ => nomatch root.down

/-- Left root record read from the old left classified table. -/
noncomputable def profiledOpenCanonicalLeftExpectedOfMove (_I : Type i) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenCanonicalLeftRootOfMove A _I move →
        In₁ × In₂ →
          RealizedBlockRound In₁ In₂
            (ProfiledOpenLeftClassifiedOutput A) Out₂
  | .left source table, root, input =>
      let monitors := fun member : { root // root ∈ source.1 } =>
        profiledOpenLeftClassifiedRootMonitor A member.1
      let controller := finiteRootMemberController monitors
        table.toTransitionRationalTree root.down
      narrowedRecord (monitors root.down) (controller.labeledTree [])
        (monitors root.down).initial input
  | .sink, root, _ => nomatch root.down
  | .right _ _, root, _ => nomatch root.down

/-- Canonical right first record of one full hidden descriptor. -/
noncomputable def profiledOpenHiddenDescriptorRightCanonicalExpected
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (root : ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor)
    (input : In₂ × In₁) :
    RealizedBlockRound In₂ In₁
      (ProfiledOpenRightClassifiedOutput A) Out₁ :=
  profiledOpenCanonicalRightExpectedOfMove A I
    descriptor.moveIdentity.1 root input

/-- Canonical left first record. -/
noncomputable def profiledOpenHiddenDescriptorLeftCanonicalExpected
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (root : ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor)
    (input : In₁ × In₂) :
    RealizedBlockRound In₁ In₂
      (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
  profiledOpenCanonicalLeftExpectedOfMove A I
    descriptor.moveIdentity.2 root input

/-- Finite first-record table for all right descriptor/root members of one
family. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorRightExpected
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A family =>
        ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor.1)) →
    In₂ × In₁ →
      RealizedBlockRound In₂ In₁
        (ProfiledOpenRightClassifiedOutput A) Out₁

/-- Left first-record table. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorLeftExpected
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A family =>
        ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor.1)) →
    In₁ × In₂ →
      RealizedBlockRound In₁ In₂
        (ProfiledOpenLeftClassifiedOutput A) Out₂

noncomputable instance
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    Fintype (ProfiledOpenHiddenDescriptorRightExpected A family) := by
  classical
  infer_instance

noncomputable instance
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    Fintype (ProfiledOpenHiddenDescriptorLeftExpected A family) := by
  classical
  infer_instance

/-- Canonically typed right union controller, pinned to an explicitly stored
finite expected-record table. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorRightPinnedFamilyMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (expected : ProfiledOpenHiddenDescriptorRightExpected A family) :=
  FiniteDescriptorFamilyPinnedAllowedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family =>
      ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor.1)
    (fun descriptor root =>
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (fun descriptor responses =>
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    expected

/-- Left pinned union controller. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (expected : ProfiledOpenHiddenDescriptorLeftExpected A family) :=
  FiniteDescriptorFamilyPinnedAllowedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family =>
      ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor.1)
    (fun descriptor root =>
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (fun descriptor responses =>
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    expected

/-! ### Canonical root-pinned specialization

For the concrete old-move hidden descriptor the expected table need not be a
free coordinate: it can be read from the old classified table itself.  The
separate all-table alphabet above remains useful as the generic target for a
direct source extraction; the theorem equating its semantic expected table
with this canonical one is the exact model adapter still required. -/

noncomputable def profiledOpenHiddenDescriptorRightFamilyCanonicalExpected
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    ProfiledOpenHiddenDescriptorRightExpected A family :=
  fun member input =>
    profiledOpenHiddenDescriptorRightCanonicalExpected A member.1.1
      member.2 input

noncomputable def profiledOpenHiddenDescriptorLeftFamilyCanonicalExpected
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    ProfiledOpenHiddenDescriptorLeftExpected A family :=
  fun member input =>
    profiledOpenHiddenDescriptorLeftCanonicalExpected A member.1.1
      member.2 input

/-- Right canonical pinned move type over a family. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorRightCanonicalPinnedMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A family
    (profiledOpenHiddenDescriptorRightFamilyCanonicalExpected A family)

/-- Left canonical pinned move type. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorLeftCanonicalPinnedMove
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A family
    (profiledOpenHiddenDescriptorLeftFamilyCanonicalExpected A family)

noncomputable abbrev ProfiledOpenHiddenDescriptorPairedCanonicalPinnedMoveAt
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  ProfiledOpenHiddenDescriptorRightCanonicalPinnedMove A family ×
    ProfiledOpenHiddenDescriptorLeftCanonicalPinnedMove A family

noncomputable instance
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    Fintype
      (ProfiledOpenHiddenDescriptorPairedCanonicalPinnedMoveAt A family) := by
  classical
  infer_instance

/-- Smallest fixed root-pinned alphabet when the old classified move is the
proof-side identity coordinate. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedCanonicalPinnedMove
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode,
    ProfiledOpenHiddenDescriptorPairedCanonicalPinnedMoveAt A family

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) :
    Fintype
      (ProfiledOpenHiddenDescriptorPairedCanonicalPinnedMove A
        initialCode) := by
  classical
  infer_instance

/-- All finite data selected at one public family code: both first-record
tables and both root-pinned union controllers. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :=
  Σ rightExpected : ProfiledOpenHiddenDescriptorRightExpected A family,
    Σ leftExpected : ProfiledOpenHiddenDescriptorLeftExpected A family,
      ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A family
          rightExpected ×
        ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A family leftExpected

noncomputable instance
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode) :
    Fintype
      (ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family) := by
  classical
  infer_instance

/-- Final source-independent, root-pinned family-move alphabet. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode,
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance (initialCode : ProfiledOpenIndexedBiBeliefCode A
    (I := I)) :
    Fintype
      (ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode) := by
  classical
  infer_instance

end

end DetParityAutomaton

end DistributedSynthesis
