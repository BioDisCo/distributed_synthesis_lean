/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedFirstLocalHandoff

/-!
# Finite profiled recurrent phase carriers and matched readback

The carrier contains only locally meaningful modes.  In a right block,
process one stores an owner controller and process two stores the matching
receiver monitor; the left orientation is symmetric.  The first guarded
block and the ordinary recurrent bank are separate finite summands.

The dependent lookup functions are totalized on mismatched keys.  On the
reachable paired invariant the keys agree, so the delivered partner summary
selects exactly the controller used by the receiver.  This is a local
same-key invariant, not knowledge of the strict leader.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- Post-initial finite modes of process one. -/
abbrev ProfiledPhaseOneControl :=
  ProfiledGuardedFirstRightOwnerControl A firstBank ⊕
    ProfiledGuardedFirstLeftActiveReceiverControl A ⊕
    ProfiledBankRightOwnerControl A ⊕
    ProfiledBankLeftReceiverControl A

/-- Post-initial finite modes of process two. -/
abbrev ProfiledPhaseTwoControl :=
  ProfiledGuardedFirstRightActiveReceiverControl A ⊕
    ProfiledGuardedFirstLeftOwnerControl A firstBank ⊕
    ProfiledBankRightReceiverControl A ⊕
    ProfiledBankLeftOwnerControl A

noncomputable instance : Fintype (ProfiledPhaseOneControl A firstBank) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledPhaseTwoControl A firstBank) := by
  classical
  infer_instance

/-! ## Matched exceptional-block lookup and readback -/

noncomputable def profiledGuardedFirstRightOwnerControlFor
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank) :
    (firstBank.rightController receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (firstBank.rightController receiver.1).initial

noncomputable def profiledGuardedFirstLeftOwnerControlFor
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank) :
    (firstBank.leftController receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (firstBank.leftController receiver.1).initial

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstRightOwnerControlFor_of_key_eq
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (h : owner.1 = receiver.1) :
    profiledGuardedFirstRightOwnerControlFor A firstBank receiver owner =
      h ▸ owner.2 := by
  classical
  simp [profiledGuardedFirstRightOwnerControlFor, h]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstLeftOwnerControlFor_of_key_eq
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (h : owner.1 = receiver.1) :
    profiledGuardedFirstLeftOwnerControlFor A firstBank receiver owner =
      h ▸ owner.2 := by
  classical
  simp [profiledGuardedFirstLeftOwnerControlFor, h]

noncomputable def continueProfiledGuardedFirstRightReceiver
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (move : In₂ × In₁) :
    Out₂ × ProfiledGuardedFirstRightActiveReceiverControl A :=
  let result := stepProfiledGuardedFirstRightReceiverFor A firstBank
    receiver.1
    (profiledGuardedFirstRightOwnerControlFor A firstBank receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

noncomputable def continueProfiledGuardedFirstLeftReceiver
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (move : In₁ × In₂) :
    Out₁ × ProfiledGuardedFirstLeftActiveReceiverControl A :=
  let result := stepProfiledGuardedFirstLeftReceiverFor A firstBank
    receiver.1
    (profiledGuardedFirstLeftOwnerControlFor A firstBank receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem continueProfiledGuardedFirstRightReceiver_key
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (move : In₂ × In₁) :
    (continueProfiledGuardedFirstRightReceiver A firstBank receiver owner
      move).2.1 = receiver.1 := rfl

@[simp] theorem continueProfiledGuardedFirstLeftReceiver_key
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (move : In₁ × In₂) :
    (continueProfiledGuardedFirstLeftReceiver A firstBank receiver owner
      move).2.1 = receiver.1 := rfl

theorem continueProfiledGuardedFirstRightReceiver_of_key_eq
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (move : In₂ × In₁) (h : owner.1 = receiver.1) :
    continueProfiledGuardedFirstRightReceiver A firstBank receiver owner move =
      let result := stepProfiledGuardedFirstRightReceiverFor A firstBank
        receiver.1 (h ▸ owner.2) receiver.2.1 receiver.2.2.1 move
      (pairedRightInformedForRow receiver.2.1 result.1.physical,
        ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩) := by
  rw [continueProfiledGuardedFirstRightReceiver,
    profiledGuardedFirstRightOwnerControlFor_of_key_eq A firstBank receiver
      owner h]

theorem continueProfiledGuardedFirstLeftReceiver_of_key_eq
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (move : In₁ × In₂) (h : owner.1 = receiver.1) :
    continueProfiledGuardedFirstLeftReceiver A firstBank receiver owner move =
      let result := stepProfiledGuardedFirstLeftReceiverFor A firstBank
        receiver.1 (h ▸ owner.2) receiver.2.1 receiver.2.2.1 move
      (pairedLeftInformedForRow receiver.2.1 result.1.physical,
        ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩) := by
  rw [continueProfiledGuardedFirstLeftReceiver,
    profiledGuardedFirstLeftOwnerControlFor_of_key_eq A firstBank receiver
      owner h]

end

/-! ## Matched ordinary-bank lookup and readback -/

noncomputable def profiledBankRightOwnerControlFor
    (receiver : ProfiledBankRightReceiverControl A)
    (owner : ProfiledBankRightOwnerControl A) :
    (profiledBankRightController A receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (profiledBankRightController A receiver.1).initial

noncomputable def profiledBankLeftOwnerControlFor
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A) :
    (profiledBankLeftController A receiver.1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (profiledBankLeftController A receiver.1).initial

theorem profiledBankRightOwnerControlFor_of_key_eq
    (receiver : ProfiledBankRightReceiverControl A)
    (owner : ProfiledBankRightOwnerControl A) (h : owner.1 = receiver.1) :
    profiledBankRightOwnerControlFor A receiver owner = h ▸ owner.2 := by
  classical
  simp [profiledBankRightOwnerControlFor, h]

theorem profiledBankLeftOwnerControlFor_of_key_eq
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A) (h : owner.1 = receiver.1) :
    profiledBankLeftOwnerControlFor A receiver owner = h ▸ owner.2 := by
  classical
  simp [profiledBankLeftOwnerControlFor, h]

noncomputable def continueProfiledBankRightReceiver
    (receiver : ProfiledBankRightReceiverControl A)
    (owner : ProfiledBankRightOwnerControl A) (move : In₂ × In₁) :
    Out₂ × ProfiledBankRightReceiverControl A :=
  let result := stepProfiledBankRightReceiverFor A receiver.1
    (profiledBankRightOwnerControlFor A receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

noncomputable def continueProfiledBankLeftReceiver
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A) (move : In₁ × In₂) :
    Out₁ × ProfiledBankLeftReceiverControl A :=
  let result := stepProfiledBankLeftReceiverFor A receiver.1
    (profiledBankLeftOwnerControlFor A receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

@[simp] theorem continueProfiledBankRightReceiver_source
    (receiver : ProfiledBankRightReceiverControl A)
    (owner : ProfiledBankRightOwnerControl A) (move : In₂ × In₁) :
    (continueProfiledBankRightReceiver A receiver owner move).2.1 =
      receiver.1 := rfl

@[simp] theorem continueProfiledBankLeftReceiver_source
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A) (move : In₁ × In₂) :
    (continueProfiledBankLeftReceiver A receiver owner move).2.1 =
      receiver.1 := rfl

/-- On a matched right-bank pair, receiver readback uses exactly the owner's
dependent controller state. -/
theorem continueProfiledBankRightReceiver_of_key_eq
    (receiver : ProfiledBankRightReceiverControl A)
    (owner : ProfiledBankRightOwnerControl A) (move : In₂ × In₁)
    (h : owner.1 = receiver.1) :
    continueProfiledBankRightReceiver A receiver owner move =
      let result := stepProfiledBankRightReceiverFor A receiver.1
        (h ▸ owner.2) receiver.2.1 receiver.2.2.1 move
      (pairedRightInformedForRow receiver.2.1 result.1.physical,
        ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩) := by
  rw [continueProfiledBankRightReceiver,
    profiledBankRightOwnerControlFor_of_key_eq A receiver owner h]

/-- Left mirror. -/
theorem continueProfiledBankLeftReceiver_of_key_eq
    (receiver : ProfiledBankLeftReceiverControl A)
    (owner : ProfiledBankLeftOwnerControl A) (move : In₁ × In₂)
    (h : owner.1 = receiver.1) :
    continueProfiledBankLeftReceiver A receiver owner move =
      let result := stepProfiledBankLeftReceiverFor A receiver.1
        (h ▸ owner.2) receiver.2.1 receiver.2.2.1 move
      (pairedLeftInformedForRow receiver.2.1 result.1.physical,
        ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩) := by
  rw [continueProfiledBankLeftReceiver,
    profiledBankLeftOwnerControlFor_of_key_eq A receiver owner h]

end


end


end DetParityAutomaton

end DistributedSynthesis
