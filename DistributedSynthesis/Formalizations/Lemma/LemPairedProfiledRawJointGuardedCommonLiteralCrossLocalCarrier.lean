/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierRound
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCrossReceiverPhysicalProjection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPreselection

/-!
# Concrete local carriers for the retained literal cross tables

The decorated common policy retains one right and one left literal
cross-table ID.  This file turns those IDs into fixed finite local state
types.  In a right block process one stores the shared blind-sender control
and process two stores the member-specific receiver control; the left block
is symmetric.

The table ID itself is part of both local states.  The sender state contains
no hidden member bit.  Every transition below accepts only the endpoint's
ordinary input (and, for a receive, the delivered partner input).  No graph,
orientation, leader bit, strict-leader bit, or semantic history is an
executable argument.
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

/-! ## Concrete right carrier -/

private noncomputable abbrev RightBaseMonitor
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A) :=
  profiledRawJointRightPhysicalSiblingMonitor A descriptor false

private noncomputable abbrev RightMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor (RightBaseMonitor A)

private abbrev RightFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed (RightBaseMonitor A)

private abbrev RightSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed (RightBaseMonitor A)

/-- Process one's graph-blind state while a retained right table runs. -/
noncomputable abbrev ProfiledRawJointGuardedCommonRightLiteralCrossSenderState :=
  FiniteCrossAnchorDescriptorFirstTwoSenderState (RightMonitor A)
    (RightFirstAllowed A) (RightSecondAllowed A)

/-- Process two's informed state.  Its Boolean member is private finite
state, installed at the resolving local event rather than queried from the
current graph. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState :=
  FiniteCrossAnchorDescriptorFirstTwoReceiverState (RightMonitor A)
    (RightFirstAllowed A) (RightSecondAllowed A)

noncomputable instance
    profiledRawJointGuardedCommonRightLiteralCrossSenderStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A) := by
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonRightLiteralCrossReceiverStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A) := by
  infer_instance

noncomputable def profiledRawJointGuardedCommonRightLiteralCrossSenderInitial
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A) :
    ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A :=
  finiteCrossAnchorDescriptorFirstTwoSenderInitial (RightMonitor A)
    (RightFirstAllowed A) (RightSecondAllowed A) move

noncomputable def profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A :=
  finiteCrossAnchorDescriptorFirstTwoReceiverInitial (RightMonitor A)
    (RightFirstAllowed A) (RightSecondAllowed A) move anchor

/-- One continuing right-block step of the blind process. -/
noncomputable def profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv
    (state : ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A)
    (input : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A :=
  finiteCrossAnchorDescriptorFirstTwoSenderNoRecv (RightMonitor A)
    (RightFirstAllowed A) (RightSecondAllowed A) state input

/-- One continuing right-block receive of process two.  The full finite
certificate output is retained here; the physical-output projection is kept
as a separate downstream lemma. -/
noncomputable def profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv
    (state : ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A)
    (own : In₂) (delivered : In₁) :=
  finiteCrossAnchorDescriptorFirstTwoReceiverRecv (RightMonitor A)
    (RightFirstAllowed A) (RightSecondAllowed A) state own delivered

/-- Physical process-two receive map obtained by forgetting the target
certificate and taking the already verified `informedBoth` coordinate. -/
noncomputable def
    profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical
    (state : ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A :=
  let result :=
    profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A state own
      delivered
  (profiledRawJointTargetRightReceiverResultPhysicalOutput result, result.2)

/-! ## Concrete left carrier -/

private noncomputable abbrev LeftBaseMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :=
  profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor

private noncomputable abbrev LeftMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor (LeftBaseMonitor A)

private abbrev LeftFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed (LeftBaseMonitor A)

private abbrev LeftSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed (LeftBaseMonitor A)

/-- Process two's graph-blind sender state in a left block. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState :=
  FiniteCrossAnchorDescriptorFirstTwoSenderState (LeftMonitor A)
    (LeftFirstAllowed A) (LeftSecondAllowed A)

/-- Process one's informed receiver state in a left block. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState :=
  FiniteCrossAnchorDescriptorFirstTwoReceiverState (LeftMonitor A)
    (LeftFirstAllowed A) (LeftSecondAllowed A)

noncomputable instance
    profiledRawJointGuardedCommonLeftLiteralCrossSenderStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A) := by
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A) := by
  infer_instance

noncomputable def profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) :
    ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A :=
  finiteCrossAnchorDescriptorFirstTwoSenderInitial (LeftMonitor A)
    (LeftFirstAllowed A) (LeftSecondAllowed A) move

noncomputable def profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A :=
  finiteCrossAnchorDescriptorFirstTwoReceiverInitial (LeftMonitor A)
    (LeftFirstAllowed A) (LeftSecondAllowed A) move anchor

/-- One continuing left-block step of the blind process two. -/
noncomputable def profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv
    (state : ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A)
    (input : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A :=
  finiteCrossAnchorDescriptorFirstTwoSenderNoRecv (LeftMonitor A)
    (LeftFirstAllowed A) (LeftSecondAllowed A) state input

/-- One continuing left-block receive of process one. -/
noncomputable def profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv
    (state : ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A)
    (own : In₁) (delivered : In₂) :=
  finiteCrossAnchorDescriptorFirstTwoReceiverRecv (LeftMonitor A)
    (LeftFirstAllowed A) (LeftSecondAllowed A) state own delivered

/-- Physical process-one mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical
    (state : ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A :=
  let result :=
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A state own
      delivered
  (profiledRawJointTargetLeftReceiverResultPhysicalOutput result, result.2)

/-! ## One fixed pair of exceptional local state alphabets -/

/-- Process one's recurrent cross-table state.  The sum tag is an installed
local phase tag, not an orientation observation. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLiteralCrossOneState :=
  ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A ⊕
    ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A

/-- Process-two mirror. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLiteralCrossTwoState :=
  ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A ⊕
    ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A

noncomputable instance profiledRawJointGuardedCommonLiteralCrossOneStateFintype :
    Fintype (ProfiledRawJointGuardedCommonLiteralCrossOneState A) := by
  infer_instance

noncomputable instance profiledRawJointGuardedCommonLiteralCrossTwoStateFintype :
    Fintype (ProfiledRawJointGuardedCommonLiteralCrossTwoState A) := by
  infer_instance

/-- Install the right table stored in one common-policy annotation. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossRightInitial
    (extra : ProfiledRawJointGuardedCommonLiteralCrossExtra A)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  (.inl
      (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A extra.1),
    .inl
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        anchor))

/-- Install the left table stored in the same annotation. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossLeftInitial
    (extra : ProfiledRawJointGuardedCommonLiteralCrossExtra A)
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  (.inr
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        anchor),
    .inr
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A extra.2))

/-! ## Installed-ID and synchronization laws -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointGuardedCommonRightLiteralCrossSenderInitial_move
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A) :
    (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move).1 =
      move :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial_move
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) :
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
      anchor).1 = move :=
  rfl

theorem profiledRawJointGuardedCommonRightLiteralCross_initial_controls_eq
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) :
    (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A move).2 =
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor).2.2.1 := by
  cases anchor <;> rfl

@[simp] theorem profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial_move
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) :
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move).1 =
      move :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial_move
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) :
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
      anchor).1 = move :=
  rfl

theorem profiledRawJointGuardedCommonLeftLiteralCross_initial_controls_eq
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) :
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A move).2 =
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor).2.2.1 := by
  cases anchor <;> rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
