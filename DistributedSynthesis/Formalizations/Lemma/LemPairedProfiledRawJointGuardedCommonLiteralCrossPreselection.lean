/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLiteralPrefixDescriptor
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPointwiseChoice
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonExactUniformActivation

/-!
# Literal cross-table preselection at guarded common occurrences

At one semantic common occurrence, the exact right and left activations expose
finite target descriptors and literal blind senders.  We narrow each hidden
strict/common pair once, keeping the first two exact physical records in the
finite descriptor.  The resulting pair of table IDs is finite.

The IDs are then selected pointwise before the single common-tree
rationalization and retained as the finite decoration of the extracted common
policy.  Semantic worlds and histories occur only in the existence proof.
The executable policy state contains the finite table IDs; no graph,
orientation, leader bit, hidden member, or history is an argument of a runtime
transition.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

/-! ## Fixed finite table alphabets -/

/-- Right-oriented literal two-anchor table alphabet. -/
noncomputable abbrev ProfiledRawJointGuardedCommonRightLiteralCrossMove :=
  FiniteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false)

noncomputable instance
    profiledRawJointGuardedCommonRightLiteralCrossMoveFintype :
    Fintype (ProfiledRawJointGuardedCommonRightLiteralCrossMove A) := by
  infer_instance

/-- Left-oriented mirror. -/
noncomputable abbrev profiledRawJointGuardedCommonLeftLiteralCrossMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :=
  BlockRecordMonitor.raiseState.{u, v, max u v x y s, y,
    max u v y s, x}
    (profiledRawJointLeftPhysicalSiblingMonitor A descriptor false)

noncomputable abbrev ProfiledRawJointGuardedCommonLeftLiteralCrossMove :=
  FiniteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor)

noncomputable instance
    profiledRawJointGuardedCommonLeftLiteralCrossMoveFintype :
    Fintype (ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) := by
  infer_instance

/-- Both staged outgoing tables carried by one common-policy move. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossExtra :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A ×
    ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

noncomputable instance profiledRawJointGuardedCommonLiteralCrossExtraFintype :
    Fintype (ProfiledRawJointGuardedCommonLiteralCrossExtra A) := by
  infer_instance

/-! ## Pointwise construction at the literal occurrence -/

/-- The right exact activation narrowed once for the strict/common hidden
pair.  Both members use the same finite descriptor and start state; the
Boolean is retained only as a proof-side name for the two literal histories.
-/
noncomputable def profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint
    (point : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonRightLiteralCrossMove A := by
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  apply finiteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false)
    (fun _ ↦ descriptor)
    (fun _ ↦ monitor.initial)
    (fun _ ↦ profiledRawJointTargetRightReceiverStrategy A activation)
    (pairedRightSenderStrategy activation.lambda)
  intro anchor env
  simpa [monitor, descriptor] using
    (profiledRawJointHybridExactRightUniformMonitor_realizable A strategy hwin
      installed env)

/-- Left exact activation, symmetrically narrowed once for both hidden
interpretations. -/
noncomputable def profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint
    (point : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonLeftLiteralCrossMove A := by
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitor :=
    profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨activation.target .first [] default⟩
  apply finiteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor)
    (fun _ ↦ descriptor)
    (fun _ ↦ monitor.initial)
    (fun _ ↦ profiledRawJointTargetLeftReceiverStrategy A activation)
    (pairedLeftSenderStrategy activation.lambda)
  intro anchor env
  apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
  simpa [baseMonitor, descriptor] using
    (profiledRawJointHybridExactLeftUniformMonitor_realizable A strategy hwin
      installed env)

/-- The complete finite annotation selected at one literal occurrence. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossExtraOfPoint
    (point : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonLiteralCrossExtra A :=
  (profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy hwin
      point,
    profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy hwin
      point)

/-! ## Occurrence-sensitive validity and outer rationalization -/

/-- A finite table pair is valid at a code/move precisely when it was
extracted at one literal semantic occurrence having that exact code and
guarded pair.  The witness is proof-only and is erased by the decorated-policy
package. -/
def ProfiledRawJointGuardedCommonLiteralCrossExtraValid
    (code : CommonCode A)
    (pair : CommonPair A strategy hwin)
    (extra : ProfiledRawJointGuardedCommonLiteralCrossExtra A) : Prop :=
  ∃ point : CommonPoint A strategy,
    point.code A strategy = code ∧
      point.move A strategy hwin = pair ∧
        profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          point = extra

/-- Every literal semantic occurrence supplies its own finite two-table
annotation before any representative is chosen. -/
theorem exists_profiledRawJointGuardedCommonLiteralCrossExtra
    (point : CommonPoint A strategy) :
    ∃ extra : ProfiledRawJointGuardedCommonLiteralCrossExtra A,
      ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin
        (point.code A strategy) (point.move A strategy hwin) extra := by
  exact ⟨profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
    point, point, rfl, rfl, rfl⟩

/-- End-to-end positive handoff: one outer rationalization retains the two
literal cross-table IDs at every reachable common-policy state. -/
theorem
    nonempty_profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage
    (initial : CommonPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
        initial
        (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy
          hwin)) := by
  apply
    nonempty_profiledRawJointGuardedCommonDecoratedPolicyPackage_of_pointwise
      A strategy hwin initial
      (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin)
  exact exists_profiledRawJointGuardedCommonLiteralCrossExtra A strategy hwin

/-- Canonical operational package.  Its state and lookup tables are finite;
the literal occurrence witness does not occur in this data. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage
    (initial : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
      initial
      (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage
      A strategy hwin initial)

end

end DetParityAutomaton

end DistributedSynthesis
