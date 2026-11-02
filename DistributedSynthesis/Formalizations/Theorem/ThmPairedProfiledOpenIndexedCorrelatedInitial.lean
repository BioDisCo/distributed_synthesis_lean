/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCorrelatedSemanticParity
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCodeParity

/-!
# Initial correlated semantic lanes

The recursive correlated construction starts at a recurrent paired entry,
not at an artificial all-empty node.  This file embeds every concrete
right/left realization into one common finite lineage type, namely the
already finite classified-anchor alphabet.  A right root occupies its
literal `.right` lineage and a left root its literal `.left` lineage.

The construction is proof-side.  It does not expose an orientation or a
strict-leader bit to either process.  In particular, the one-active-lane
constructors are the form used after the initial delayed handoff: which
constructor applies is a theorem about the actual history, not a local
controller branch on hidden orientation.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Literal finite-lineage embeddings -/

/-- A right source member is stored at the lineage bearing its literal
classified right anchor. -/
noncomputable def profiledOpenIndexedRightMemberAt
    (source : ProfiledOpenRightViewClass A) :
    ProfiledOpenClassifiedAnchor A → Option {root // root ∈ source.1} := by
  classical
  exact fun
    | .right root =>
        if hroot : root ∈ source.1 then some ⟨root, hroot⟩ else none
    | .sink | .left _ => none

/-- Left-source mirror. -/
noncomputable def profiledOpenIndexedLeftMemberAt
    (source : ProfiledOpenLeftViewClass A) :
    ProfiledOpenClassifiedAnchor A → Option {root // root ∈ source.1} := by
  classical
  exact fun
    | .left root =>
        if hroot : root ∈ source.1 then some ⟨root, hroot⟩ else none
    | .sink | .right _ => none

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedRightMemberAt_self
    (source : ProfiledOpenRightViewClass A)
    (member : {root // root ∈ source.1}) :
    profiledOpenIndexedRightMemberAt A source (.right member.1) =
      some member := by
  simp [profiledOpenIndexedRightMemberAt, member.2]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedLeftMemberAt_self
    (source : ProfiledOpenLeftViewClass A)
    (member : {root // root ∈ source.1}) :
    profiledOpenIndexedLeftMemberAt A source (.left member.1) =
      some member := by
  simp [profiledOpenIndexedLeftMemberAt, member.2]

/-- Embed any realized right view class into the common finite lineage
alphabet without merging distinct roots. -/
noncomputable def profiledOpenIndexedRightLaneOfRealization
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) where
  source := source
  realization := realization
  memberAt := profiledOpenIndexedRightMemberAt A source
  covers := by
    intro member
    exact ⟨.right member.1,
      profiledOpenIndexedRightMemberAt_self A source member⟩

/-- Embed any realized left view class. -/
noncomputable def profiledOpenIndexedLeftLaneOfRealization
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) where
  source := source
  realization := realization
  memberAt := profiledOpenIndexedLeftMemberAt A source
  covers := by
    intro member
    exact ⟨.left member.1,
      profiledOpenIndexedLeftMemberAt_self A source member⟩

/-! ## Active recurrent states -/

/-- Both literal realized lanes, when both proof-side orientations are being
carried simultaneously. -/
noncomputable def profiledOpenIndexedCorrelatedStateOfRealizations
    {rightSource : ProfiledOpenRightViewClass A}
    {leftSource : ProfiledOpenLeftViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis rightSource)
    (left : ProfiledOpenLeftRealization A strategy hwin basis leftSource) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) :=
  { right := some
      (profiledOpenIndexedRightLaneOfRealization A strategy hwin basis right)
    left := some
      (profiledOpenIndexedLeftLaneOfRealization A strategy hwin basis left) }

/-- A genuine process-one paired entry activates only the right semantic
lane.  The absent mirror is represented explicitly by `none`. -/
noncomputable def profiledOpenIndexedRightStateOfRealization
    {source : ProfiledOpenRightViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis source) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) :=
  { right := some
      (profiledOpenIndexedRightLaneOfRealization A strategy hwin basis right)
    left := none }

/-- Process-two/left-entry mirror. -/
noncomputable def profiledOpenIndexedLeftStateOfRealization
    {source : ProfiledOpenLeftViewClass A}
    (left : ProfiledOpenLeftRealization A strategy hwin basis source) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) :=
  { right := none
    left := some
      (profiledOpenIndexedLeftLaneOfRealization A strategy hwin basis left) }

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The right-only state retains every source member at its literal lineage. -/
@[simp] theorem profiledOpenIndexedRightStateOfRealization_slot
    {source : ProfiledOpenRightViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1}) :
    (profiledOpenIndexedRightStateOfRealization A strategy hwin basis right
      |>.code A strategy hwin basis).rightSlots (.right member.1) =
      some (.right member.1) := by
  simp [profiledOpenIndexedRightStateOfRealization,
    ProfiledOpenIndexedCorrelatedSemanticState.code,
    ProfiledOpenIndexedRightSemanticShadow.slots,
    profiledOpenIndexedRightLaneOfRealization]

/-- Its inactive left lane is literally empty. -/
@[simp] theorem profiledOpenIndexedRightStateOfRealization_leftSlot
    {source : ProfiledOpenRightViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis source)
    (lineage : ProfiledOpenClassifiedAnchor A) :
    (profiledOpenIndexedRightStateOfRealization A strategy hwin basis right
      |>.code A strategy hwin basis).leftSlots lineage = none := by
  rfl

/-- Left-only slot mirror. -/
@[simp] theorem profiledOpenIndexedLeftStateOfRealization_slot
    {source : ProfiledOpenLeftViewClass A}
    (left : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1}) :
    (profiledOpenIndexedLeftStateOfRealization A strategy hwin basis left
      |>.code A strategy hwin basis).leftSlots (.left member.1) =
      some (.left member.1) := by
  simp [profiledOpenIndexedLeftStateOfRealization,
    ProfiledOpenIndexedCorrelatedSemanticState.code,
    ProfiledOpenIndexedLeftSemanticShadow.slots,
    profiledOpenIndexedLeftLaneOfRealization]

@[simp] theorem profiledOpenIndexedLeftStateOfRealization_rightSlot
    {source : ProfiledOpenLeftViewClass A}
    (left : ProfiledOpenLeftRealization A strategy hwin basis source)
    (lineage : ProfiledOpenClassifiedAnchor A) :
    (profiledOpenIndexedLeftStateOfRealization A strategy hwin basis left
      |>.code A strategy hwin basis).rightSlots lineage = none := by
  rfl

end

/-! ## Direct entry-to-state bridge -/

/-- Canonical one-root realization of a concrete process-one paired entry. -/
noncomputable def profiledOpenIndexedRightEntryRealization
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State) :=
  profiledOpenRightSemanticSourceRealization A strategy hwin
    (fun _ : Unit => entry) (fun _ : Unit => minimum) ()
    (by intro index; cases index; rfl) basis

/-- Canonical one-root realization of a concrete process-two paired entry. -/
noncomputable def profiledOpenIndexedLeftEntryRealization
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State) :=
  profiledOpenLeftSemanticSourceRealization A strategy hwin
    (fun _ : Unit => entry) (fun _ : Unit => minimum) ()
    (by intro index; cases index; rfl) basis

/-- The recurrent correlated state installed from a process-one paired
memory. -/
noncomputable def profiledOpenIndexedRightEntryState
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) :=
  profiledOpenIndexedRightStateOfRealization A strategy hwin basis
    (profiledOpenIndexedRightEntryRealization A strategy hwin basis entry
      minimum)

/-- Process-two paired-memory mirror. -/
noncomputable def profiledOpenIndexedLeftEntryState
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := ProfiledOpenClassifiedAnchor A) :=
  profiledOpenIndexedLeftStateOfRealization A strategy hwin basis
    (profiledOpenIndexedLeftEntryRealization A strategy hwin basis entry
      minimum)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A concrete process-one entry produces a genuinely active initial code. -/
theorem profiledOpenIndexedRightEntryState_nonempty
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State) :
    ∃ lineage root,
      (profiledOpenIndexedRightEntryState A strategy hwin basis entry minimum
        |>.code A strategy hwin basis).rightSlots lineage =
        some (.right root) := by
  let realization := profiledOpenIndexedRightEntryRealization A strategy hwin
    basis entry minimum
  let member := realization.pivot
  exact ⟨.right member.1, member.1,
    profiledOpenIndexedRightStateOfRealization_slot A strategy hwin basis
      realization member⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two entry mirror. -/
theorem profiledOpenIndexedLeftEntryState_nonempty
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State) :
    ∃ lineage root,
      (profiledOpenIndexedLeftEntryState A strategy hwin basis entry minimum
        |>.code A strategy hwin basis).leftSlots lineage =
        some (.left root) := by
  let realization := profiledOpenIndexedLeftEntryRealization A strategy hwin
    basis entry minimum
  let member := realization.pivot
  exact ⟨.left member.1, member.1,
    profiledOpenIndexedLeftStateOfRealization_slot A strategy hwin basis
      realization member⟩

/-! ## Entry-level parity adapters -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The actual recurrent state installed from a process-one paired memory
has the complete code-observable semantic parity certificate. -/
theorem profiledOpenIndexedRightEntryState_codeParityCertificate
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State) :
    let initial := profiledOpenIndexedRightEntryState A strategy hwin basis
      entry minimum
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    ProfiledOpenIndexedBiBeliefCodeSemanticCertificate A
      (initial.code A strategy hwin basis) raw := by
  exact profiledOpenIndexedCorrelatedSemanticTree_codeParityCertificate A
    strategy hwin basis
    (profiledOpenIndexedRightEntryState A strategy hwin basis entry minimum)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two paired-memory mirror. -/
theorem profiledOpenIndexedLeftEntryState_codeParityCertificate
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State) :
    let initial := profiledOpenIndexedLeftEntryState A strategy hwin basis
      entry minimum
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    ProfiledOpenIndexedBiBeliefCodeSemanticCertificate A
      (initial.code A strategy hwin basis) raw := by
  exact profiledOpenIndexedCorrelatedSemanticTree_codeParityCertificate A
    strategy hwin basis
    (profiledOpenIndexedLeftEntryState A strategy hwin basis entry minimum)

end

end DetParityAutomaton

end DistributedSynthesis
