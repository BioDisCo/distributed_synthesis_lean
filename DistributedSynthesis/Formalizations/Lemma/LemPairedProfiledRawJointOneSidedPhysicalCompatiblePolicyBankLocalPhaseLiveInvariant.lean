/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveController

/-!
# Dual matched-prefix invariant for the recurrent phase-live controller

A direction reversal promotes a dormant receiver/owner pair to the active
physical table.  Certifying only the active table is therefore not
inductive.  The invariant below certifies both orientations: the active pair
and the selected dormant pair, each at its own bank state and finite prefix.

A same-direction receive also refreshes the dormant orientation from the
latest resolved packet.  The fresh receiver is rooted in row `first`; its
owner and monitor are both initial, and the bank resolver supplies its exact
reachable successor, live root, and installed physical move.
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

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

/-! ## Both live orientations -/

/-- Regard the selected dormant left receiver and its matching owner as a
left-oriented boundary pair.  The active right receiver is retained as the
opposite dormant receiver. -/
noncomputable def
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) :
    ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
  (phaseData.2.1, ⟨phaseData.1.2.2, phaseData.2.2⟩,
    phaseData.1.receiver A strategy hwin)

/-- Mirrored dormant right pair. -/
noncomputable def
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) :
    ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
  (phaseData.2.1, ⟨phaseData.1.2.2, phaseData.2.2⟩,
    phaseData.1.receiver A strategy hwin)

/-- Active-right and dormant-left matched-prefix certificates. -/
def ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin phaseData.1 ∧
    ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
      (phaseData.dormantLeftData A strategy hwin)

/-- Active-left and dormant-right mirror. -/
def ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin phaseData.1 ∧
    ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
      (phaseData.dormantRightData A strategy hwin)

/-! ## Fresh dormant roots after a same-direction round -/

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) :
    ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
  (data.successor A strategy hwin input,
    ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
      (move.memberController A false).initial⟩,
    (data.step A strategy hwin input).receiver A strategy hwin)

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.freshLeftData
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
  data.freshLeftDataAt A strategy hwin input move .first

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) :
    ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
  (data.successor A strategy hwin input,
    ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
      (move.memberController A false).initial⟩,
    (data.step A strategy hwin input).receiver A strategy hwin)

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.freshRightData
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
  data.freshRightDataAt A strategy hwin input move .first

/-- A reachable right table refreshes a genuine left root at its emitted bank
successor. -/
theorem ProfiledRawJointRecurrentRightBoundaryInvariant.exists_freshLeftAt
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂)
    (row : PairedEntryRow) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (data.successor A strategy hwin input).2.1.2.2 = some move ∧
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (data.freshLeftDataAt A strategy hwin input move row) := by
  have hinvariantCopy := hinvariant
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hinvariantCopy
  rcases hinvariantCopy with
    ⟨currentCode, currentRoot, past, hreachable, hcurrentCode, hcurrentRoot,
      hcurrentMove, howner, hmonitor⟩
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy hwin
      data hinvariant) input
  let target := data.target A strategy hwin input
  let childCode :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy hwin
      data.1 target
  have hresolve :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec A strategy
      hwin data.1 hreachable target ⟨childCode, hrealizes⟩
  dsimp only at hresolve
  rcases hresolve with
    ⟨hbare, hrealizesResolved, _hindex, hsuccessorReachable⟩
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_leftMove_exists
      A strategy hwin data.1 target hrealizesResolved root hroot
  rcases hrealizesResolved with
    ⟨_realizingMove, _source, _actual, _hsourceCode, _hsourceMove,
      _hcompatible, _hchildren, _hchildCode, _hbare, hsuccessor⟩
  refine ⟨move, hmove, ?_⟩
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
    ProfiledRawJointRecurrentRightBoundaryData.freshLeftDataAt,
    ProfiledRawJointRecurrentLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentLeftBoundaryData.owner,
    initialProfiledRawJointLeftPhysicalSiblingReceiver]
  refine ⟨target, root, [], hsuccessorReachable, ?_, hroot, hmove, ?_, ?_⟩
  · dsimp only [ProfiledRawJointRecurrentRightBoundaryData.successor,
      profiledRawJointOneSidedPhysicalCompatibleBankSuccessor]
    rw [hsuccessor]
    exact hbare
  · rfl
  · rfl

theorem ProfiledRawJointRecurrentRightBoundaryInvariant.exists_freshLeft
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (data.successor A strategy hwin input).2.1.2.2 = some move ∧
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (data.freshLeftData A strategy hwin input move) := by
  simpa only [ProfiledRawJointRecurrentRightBoundaryData.freshLeftData] using
    hinvariant.exists_freshLeftAt A strategy hwin data input .first

/-- Mirrored reachable fresh-right root. -/
theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.exists_freshRightAt
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂)
    (row : PairedEntryRow) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (data.successor A strategy hwin input).2.1.2.1 = some move ∧
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (data.freshRightDataAt A strategy hwin input move row) := by
  have hinvariantCopy := hinvariant
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hinvariantCopy
  rcases hinvariantCopy with
    ⟨currentCode, currentRoot, past, hreachable, hcurrentCode, hcurrentRoot,
      hcurrentMove, howner, hmonitor⟩
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy hwin data
      hinvariant) input
  let target := data.target A strategy hwin input
  let childCode :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy hwin
      data.1 target
  have hresolve :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec A strategy
      hwin data.1 hreachable target ⟨childCode, hrealizes⟩
  dsimp only at hresolve
  rcases hresolve with
    ⟨hbare, hrealizesResolved, _hindex, hsuccessorReachable⟩
  obtain ⟨move, hmove⟩ :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket_rightMove_exists
      A strategy hwin data.1 target hrealizesResolved root hroot
  rcases hrealizesResolved with
    ⟨_realizingMove, _source, _actual, _hsourceCode, _hsourceMove,
      _hcompatible, _hchildren, _hchildCode, _hbare, hsuccessor⟩
  refine ⟨move, hmove, ?_⟩
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
    ProfiledRawJointRecurrentLeftBoundaryData.freshRightDataAt,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner,
    initialProfiledRawJointRightPhysicalSiblingReceiver]
  refine ⟨target, root, [], hsuccessorReachable, ?_, hroot, hmove, ?_, ?_⟩
  · dsimp only [ProfiledRawJointRecurrentLeftBoundaryData.successor,
      profiledRawJointOneSidedPhysicalCompatibleBankSuccessor]
    rw [hsuccessor]
    exact hbare
  · rfl
  · rfl

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.exists_freshRight
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (input : In₁ × In₂) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (data.successor A strategy hwin input).2.1.2.1 = some move ∧
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (data.freshRightData A strategy hwin input move) := by
  simpa only [ProfiledRawJointRecurrentLeftBoundaryData.freshRightData] using
    hinvariant.exists_freshRightAt A strategy hwin data input .first

end

end DetParityAutomaton

end DistributedSynthesis
