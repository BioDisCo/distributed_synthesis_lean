/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootPairTest
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOverlapInvariant
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Finite local carriers for the profiled readback

These are the actual local state spaces used by the final summary automaton.
They contain the root, the two initial contingencies, the one-round root
hybrid, a single post-initial control, and two post-initial candidate
projections.  The Boolean attached to a candidate pair records which past
candidate supplied the latest refresh.  It is computed from local state and
receipt history; it is not the current graph or a strict-leader oracle.
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
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentProfiledGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)
  (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- Receiving initial-left state, including the possible exceptional key
staged by its preceding table lookup. -/
abbrev ProfiledOperationalInitialLeft :=
  ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers × Option (ProfiledGuardedFirstRightMacro A)

/-- Initial-right mirror. -/
abbrev ProfiledOperationalInitialRight :=
  ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers × Option (ProfiledGuardedFirstLeftMacro A)

/-- Two locally meaningful post-initial projections and the locally retained
past-anchor bit (`false` = right, `true` = left). -/
abbrev ProfiledOperationalOverlapOne :=
  Bool × (ProfiledPhaseOneControl A firstBank ×
    ProfiledPhaseOneControl A firstBank)

/-- Process-two mirror. -/
abbrev ProfiledOperationalOverlapTwo :=
  Bool × (ProfiledPhaseTwoControl A firstBank ×
    ProfiledPhaseTwoControl A firstBank)

/-- Initial-left anchor together with the freshly activated first-right
shadow.  This is retained by process one after a receive at the first seam;
the receive alone does not reveal whether the graph was `left` or `both`. -/
abbrev ProfiledOperationalInitialLeftSeamOne :=
  ProfiledOperationalInitialLeft A strategy hwin rightBasis leftBasis
      controllers ×
    (ProfiledGuardedFirstRightOwnerControl A firstBank ×
      ProfiledGuardedFirstRightActiveReceiverControl A)

/-- Process-two projection of the same seam. -/
abbrev ProfiledOperationalInitialLeftSeamTwo :=
  controllers.leftController.Control ×
    (ProfiledGuardedFirstRightOwnerControl A firstBank ×
      ProfiledGuardedFirstRightActiveReceiverControl A)

/-- Initial-right mirror at process one. -/
abbrev ProfiledOperationalInitialRightSeamOne :=
  controllers.rightController.Control ×
    (ProfiledGuardedFirstLeftOwnerControl A firstBank ×
      ProfiledGuardedFirstLeftActiveReceiverControl A)

/-- Initial-right mirror at process two. -/
abbrev ProfiledOperationalInitialRightSeamTwo :=
  ProfiledOperationalInitialRight A strategy hwin rightBasis leftBasis
      controllers ×
    (ProfiledGuardedFirstLeftOwnerControl A firstBank ×
      ProfiledGuardedFirstLeftActiveReceiverControl A)

/-- Process one's full finite control, with named constructors so the local
transition table can be audited without decoding nested sum injections. -/
inductive ProfiledOperationalOneControl where
  | root
      (marker : ProfiledOperationalInitialLeft A strategy hwin rightBasis
        leftBasis controllers)
  | initialLeft
      (state : ProfiledOperationalInitialLeft A strategy hwin rightBasis
        leftBasis controllers)
  | initialRightBlind (state : controllers.rightController.Control)
  | rootHybrid
      (state : ProfiledRootHybridOne A strategy hwin rightBasis leftBasis
        controllers)
  | initialLeftSeam
      (state : ProfiledOperationalInitialLeftSeamOne A strategy hwin
        rightBasis leftBasis controllers firstBank)
  | initialRightSeam
      (state : ProfiledOperationalInitialRightSeamOne A strategy hwin
        rightBasis leftBasis controllers firstBank)
  | post
      (marker : ProfiledOperationalInitialLeft A strategy hwin rightBasis
        leftBasis controllers)
      (state : ProfiledPhaseOneControl A firstBank)
  | overlap
      (marker : ProfiledOperationalInitialLeft A strategy hwin rightBasis
        leftBasis controllers)
      (state : ProfiledOperationalOverlapOne A firstBank)
  deriving Fintype

/-- Process-two mirror. -/
inductive ProfiledOperationalTwoControl where
  | root
      (marker : ProfiledOperationalInitialRight A strategy hwin rightBasis
        leftBasis controllers)
  | initialLeftBlind (state : controllers.leftController.Control)
  | initialRight
      (state : ProfiledOperationalInitialRight A strategy hwin rightBasis
        leftBasis controllers)
  | rootHybrid
      (state : ProfiledRootHybridTwo A strategy hwin rightBasis leftBasis
        controllers)
  | initialLeftSeam
      (state : ProfiledOperationalInitialLeftSeamTwo A strategy hwin
        rightBasis leftBasis controllers firstBank)
  | initialRightSeam
      (state : ProfiledOperationalInitialRightSeamTwo A strategy hwin
        rightBasis leftBasis controllers firstBank)
  | post
      (marker : ProfiledOperationalInitialRight A strategy hwin rightBasis
        leftBasis controllers)
      (state : ProfiledPhaseTwoControl A firstBank)
  | overlap
      (marker : ProfiledOperationalInitialRight A strategy hwin rightBasis
        leftBasis controllers)
      (state : ProfiledOperationalOverlapTwo A firstBank)
  deriving Fintype

noncomputable instance : Fintype
    (ProfiledOperationalInitialLeftSeamOne A strategy hwin rightBasis
      leftBasis controllers firstBank) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOperationalInitialLeftSeamTwo A strategy hwin rightBasis
      leftBasis controllers firstBank) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOperationalInitialRightSeamOne A strategy hwin rightBasis
      leftBasis controllers firstBank) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
noncomputable instance : Fintype
    (ProfiledOperationalInitialRightSeamTwo A strategy hwin rightBasis
      leftBasis controllers firstBank) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
noncomputable instance : Fintype
    (ProfiledOperationalInitialLeft A strategy hwin rightBasis leftBasis
      controllers) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOperationalInitialRight A strategy hwin rightBasis leftBasis
      controllers) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOperationalOverlapOne A firstBank) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOperationalOverlapTwo A firstBank) := by
  classical
  infer_instance

/-- Moore timing stores the output produced by the observation that reached
the control. -/
abbrev ProfiledOperationalOneSummary :=
  ProfiledOperationalOneControl A strategy hwin rightBasis leftBasis
      controllers firstBank × Out₁

/-- Process-two Moore summary. -/
abbrev ProfiledOperationalTwoSummary :=
  ProfiledOperationalTwoControl A strategy hwin rightBasis leftBasis
      controllers firstBank × Out₂

noncomputable instance : Fintype
    (ProfiledOperationalOneSummary A strategy hwin rightBasis leftBasis
      controllers firstBank) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOperationalTwoSummary A strategy hwin rightBasis leftBasis
      controllers firstBank) := by
  classical
  infer_instance

def initialProfiledOperationalOneControl :
    ProfiledOperationalOneControl A strategy hwin rightBasis leftBasis
      controllers firstBank :=
  .root
    (profiledGuardedInitialLeftFiniteReadbackInitial A strategy hwin rightBasis
      leftBasis controllers, none)

def initialProfiledOperationalTwoControl :
    ProfiledOperationalTwoControl A strategy hwin rightBasis leftBasis
      controllers firstBank :=
  .root
    (profiledGuardedInitialRightFiniteReadbackInitial A strategy hwin
      rightBasis leftBasis controllers, none)

noncomputable def initialProfiledOperationalOneSummary :
    ProfiledOperationalOneSummary A strategy hwin rightBasis leftBasis
      controllers firstBank :=
  (initialProfiledOperationalOneControl A strategy hwin rightBasis leftBasis
    controllers firstBank, default)

noncomputable def initialProfiledOperationalTwoSummary :
    ProfiledOperationalTwoSummary A strategy hwin rightBasis leftBasis
      controllers firstBank :=
  (initialProfiledOperationalTwoControl A strategy hwin rightBasis leftBasis
    controllers firstBank, default)

def profiledOperationalOutputOne
    (summary : ProfiledOperationalOneSummary A strategy hwin rightBasis
      leftBasis controllers firstBank) : Out₁ := summary.2

def profiledOperationalOutputTwo
    (summary : ProfiledOperationalTwoSummary A strategy hwin rightBasis
      leftBasis controllers firstBank) : Out₂ := summary.2

end

end


end DetParityAutomaton

end DistributedSynthesis
