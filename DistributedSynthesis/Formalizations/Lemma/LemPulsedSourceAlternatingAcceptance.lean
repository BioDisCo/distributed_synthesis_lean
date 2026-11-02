/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPulsedSourceRenewalProgress

/-!
# Acceptance of the actual alternating owner run for the pulsed source

The hypotheses concern one initial staged installation and its fixed right
bank cell. They do not assume acceptance or a progress invariant for the
mixed execution. The proof derives recurring grants by the literal four-round
return cycle and the right/left progress disjunction.
-/

namespace DistributedSynthesis
namespace PulsedSourceInstallationAudit
open DetParityAutomaton TwoProcessNoResetReversalObstruction
open TwoProcessPhysicalTargetAudit (pulsedSource pulsedSource_wins)
open ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

noncomputable section
universe m
variable {Memory : Type m}

private abbrev Tables := ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
  (Memory := Memory) objective pulsedSource
private abbrev Controls :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) objective pulsedSource ×
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) objective pulsedSource

def alternatingGraph (n : Nat) : Graph := if n % 2 = 0 then .left else .right

def alternatingControlAt (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) : Nat → Controls (Memory := Memory)
  | 0 => initial
  | n + 1 => (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
      (alternatingControlAt tables initial n) ((), ()) (alternatingGraph n)).1

def alternatingOwnerWord (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) : Nat → RoundRecord Unit Unit Graph Bool Bool :=
  fun n ↦ tables.ownerFibreRoundRecord objective pulsedSource pulsedSource_wins
    (alternatingControlAt tables initial n) ((), ()) (alternatingGraph n)

theorem alternatingControlAt_four (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) (k : Nat) :
    alternatingControlAt tables initial (4 * k + 4) =
      ([Graph.left, .right, .left, .right].foldl
        (fun controls graph ↦ (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
          controls ((), ()) graph).1)
        (alternatingControlAt tables initial (4 * k))) := by
  simp [alternatingControlAt, alternatingGraph, Nat.add_mod, Nat.mul_mod]

theorem alternating_staged_at_four
    (tables : Tables (Memory := Memory))
    (initial : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (hready : RenewalReady tables initial) (k : Nat) :
    ∃ pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource,
      RenewalReady tables pair ∧
      alternatingControlAt tables (initial.controls objective pulsedSource) (4 * k) =
        pair.controls objective pulsedSource := by
  induction k with
  | zero => exact ⟨initial, hready, rfl⟩
  | succ k ih =>
    obtain ⟨pair, hp, hc⟩ := ih
    obtain ⟨move, hm⟩ := hp.installed
    refine ⟨pair.renew objective pulsedSource pulsedSource_wins tables move (fun _ ↦ ((), ())),
      hp.renew tables pair move, ?_⟩
    rw [Nat.mul_succ, alternatingControlAt_four, hc]
    exact pair.four_round_return objective pulsedSource pulsedSource_wins tables move hm
      (fun _ ↦ ((), ()))

theorem alternating_preRenewal_at_three
    (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) (k : Nat)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (hc : alternatingControlAt tables initial (4 * k) = pair.controls objective pulsedSource)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hm : pair.packet.successor.2.1.1.2.2 = some move) :
    alternatingControlAt tables initial (4 * k + 3) =
      (preRenewal tables pair move).controls objective pulsedSource := by
  simp only [alternatingControlAt]
  simp [alternatingGraph, Nat.add_mod, Nat.mul_mod, hc]
  rw [pair.round_left objective pulsedSource pulsedSource_wins tables move hm,
    InstalledLeftOwnerPair.round_right, OpenOwnerPair.round_left]
  unfold preRenewal
  rfl

theorem alternatingOwnerWord_grant (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) (n : Nat) :
    grant (alternatingOwnerWord tables initial n) =
      strictOutputGrant (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
        (alternatingControlAt tables initial n) ((), ()) (alternatingGraph n)).2 := by
  unfold alternatingOwnerWord
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRoundRecord
  unfold alternatingGraph
  split <;> rfl

/-- Every four-round cycle provides a grant at its last right round or at
the next cycle's first left round. This is a bound on literal owner outputs. -/
theorem alternating_cycle_grant
    (tables : Tables (Memory := Memory))
    (initial : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (hready : RenewalReady tables initial) (k : Nat) :
    grant (alternatingOwnerWord tables (initial.controls objective pulsedSource) (4 * k + 3)) = true ∨
    grant (alternatingOwnerWord tables (initial.controls objective pulsedSource) (4 * k + 4)) = true := by
  obtain ⟨pair, hp, hc⟩ := alternating_staged_at_four tables initial hready k
  obtain ⟨move, hm⟩ := hp.installed
  have hmid := alternating_preRenewal_at_three tables _ k pair hc move hm
  have hg := renewal_progress tables pair hp move
  have hnext : alternatingControlAt tables (initial.controls objective pulsedSource) (4 * k + 4) =
      (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
        ((preRenewal tables pair move).controls objective pulsedSource) ((), ()) .right).1 := by
    rw [show 4 * k + 4 = (4 * k + 3) + 1 by omega, alternatingControlAt, hmid]
    simp [alternatingGraph, Nat.add_mod, Nat.mul_mod]
  rw [alternatingOwnerWord_grant, alternatingOwnerWord_grant]
  rw [hmid, hnext]
  simpa [alternatingGraph, Nat.add_mod, Nat.mul_mod] using hg

/-- The pulsed-source owner stress test accepts the infinitely alternating
tail from every locally ready staged state. The automaton's initial state is
arbitrary because the recurring-grant argument is independent of it. -/
theorem alternating_owner_accepts_from
    (tables : Tables (Memory := Memory))
    (initial : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (hready : RenewalReady tables initial) (q : objective.State) :
    objective.AcceptsFrom q (alternatingOwnerWord tables
      (initial.controls objective pulsedSource)) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  intro N
  obtain hg | hg := alternating_cycle_grant tables initial hready N
  · refine ⟨4 * N + 4, by omega, ?_⟩
    rw [show 4 * N + 4 = (4 * N + 3) + 1 by omega, runFrom]
    change (if grant (alternatingOwnerWord tables
      (initial.controls objective pulsedSource) (4 * N + 3)) then 0 else 1) = 0
    rw [hg]
    rfl
  · refine ⟨4 * N + 5, by omega, ?_⟩
    rw [show 4 * N + 5 = (4 * N + 4) + 1 by omega, runFrom]
    change (if grant (alternatingOwnerWord tables
      (initial.controls objective pulsedSource) (4 * N + 4)) then 0 else 1) = 0
    rw [hg]
    rfl

private abbrev ExactMemory :=
  ProfiledRawJointOneSidedPhysicalExactCommonActionMemory objective pulsedSource

/-- The universal local resolver clause used above is already provided by
the exact-cell target-realization theorem. It is not a new global safety or
acceptance premise. The other hypotheses describe the initial staged state. -/
theorem RenewalReady.of_exact_cell
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey objective pulsedSource)
    (state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
      (Memory := ExactMemory) objective key.1.1)
    (haligned : ExactPolicyAligned objective pulsedSource key state)
    (pair : StagedRightOwnerPair (Memory := ExactMemory) objective pulsedSource)
    (hstate : pair.state = ⟨key, state⟩)
    (root : ProfiledRawJointThreadRoot objective)
    (hroot : profiledRawJointOneSidedCurrentSlots objective .right state.1.1.1 () = some root)
    (hmove : state.1.1.2.1 = some pair.right.1)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective pair.right)
    (hanchor : pair.twoCoordinates.1 = pair.state)
    (hinstalled : ∃ move : ProfiledRawJointLeftPhysicalSiblingMove objective,
      pair.packet.successor.2.1.1.2.2 = some move)
    (hsemantic : ∃
      (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := Unit) (In₂ := Unit))
      (member : ProcOnePairedEntryRep pulsedSource × objective.State),
      (family.semanticChild objective direction).right () = some member ∧
      pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf objective family direction member) :
    RenewalReady ((exactEffectTable objective pulsedSource pulsedSource_wins key).family
      objective pulsedSource key) pair := by
  refine ⟨hvalid, hanchor, hinstalled, hsemantic, ?_⟩
  intro target ht
  rw [hstate]
  exact haligned.resolveTarget_realizes_right objective pulsedSource pulsedSource_wins
    key state state.1.1.1 rfl root hroot pair.right.1 hmove target ht

end
end PulsedSourceInstallationAudit
end DistributedSynthesis
