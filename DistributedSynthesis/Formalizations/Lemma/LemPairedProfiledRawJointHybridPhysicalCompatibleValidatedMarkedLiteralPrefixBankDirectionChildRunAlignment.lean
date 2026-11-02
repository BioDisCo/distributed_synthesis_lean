/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankAuthorityPath
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeStrictAlternation
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Acceptance of the executable child-table run

The proof-side direction path and the retained controller's child-table run
were introduced through two interfaces.  Their legal moves need not be the
same representative, so a pointwise path equality would be unnecessarily
strong.  The child-table run is itself an allowed path of the same selected
policy and is therefore accepted directly.  This file gives the corresponding
hidden-root and physical block-pasting endpoint, without comparing the two
move choices and without a second rationalization.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev ChildRunPath
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath A strategy
    hwin control direction

private abbrev InitialBareCode
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridCode A :=
  .common
    ((profiledRawJointCommonWorldFamily A
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world).incidenceCode A)

private abbrev ChildRunBareCodeWord
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :=
  ((ChildRunPath A strategy hwin control direction).toExtraAllowedPath A
    strategy hwin).bareCodeWord A strategy hwin

/-- The executable child-table run is accepted directly because it is an
allowed path through the selected marked policy. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_bareCodeWord_accepts
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridCodeParityDPA A
      (InitialBareCode A strategy hwin control)).Accepts
        (ChildRunBareCodeWord A strategy hwin control direction) := by
  exact (ChildRunPath A strategy hwin control direction).bareCodeWord_accepts
    A strategy hwin

/-- Hidden roots exposed by successive executable child codes inherit parity
from the accepted child-table path. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_rootPriorities_minEven
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitial :
      profiledRawJointHybridCurrentSlots A (side 0)
          (InitialBareCode A strategy hwin control) () = some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          (ChildRunBareCodeWord A strategy hwin control direction n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other) :
    NatSeqMinEvenParity
      (fun n ↦ profiledRawJointThreadRootPriority A (root n)) := by
  let initialCode := InitialBareCode A strategy hwin control
  let word := ChildRunBareCodeWord A strategy hwin control direction
  have hcode :
      (profiledRawJointHybridCodeParityDPA A initialCode).Accepts word := by
    simpa [initialCode, word] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_bareCodeWord_accepts
        A strategy hwin control direction)
  have hall :=
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) word).mp hcode
  have hparity := hall (side 0) ()
  exact
    natSeqMinEvenParity_roots_of_codedAlternating_strictAlternation initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) word side () initialRoot root
      hinitial hroot halternates hparity

/-- Physical suffix blocks aligned with an arbitrary suffix of the executable
child-root stream are accepting. -/
theorem
    physicalPriorities_minEven_of_bankChildRun_rootSlots_from
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitial :
      profiledRawJointHybridCurrentSlots A (side 0)
          (InitialBareCode A strategy hwin control) () = some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          (ChildRunBareCodeWord A strategy hwin control direction n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (rootOffset : Nat)
    (physicalPriorities : Nat → Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (hblock : ∀ n : Nat,
      cutBlockMin physicalPriorities cuts n =
        profiledRawJointThreadRootPriority A (root (rootOffset + n))) :
    NatSeqMinEvenParity physicalPriorities := by
  have hroots :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_rootPriorities_minEven
      A strategy hwin control direction side initialRoot root hinitial hroot
        halternates
  have htail :
      NatSeqMinEvenParity (fun n ↦
        profiledRawJointThreadRootPriority A (root (rootOffset + n))) :=
    (natSeqMinEvenParity_shift
      (fun n ↦ profiledRawJointThreadRootPriority A (root n))
      rootOffset).mpr hroots
  have hblocks : NatSeqMinEvenParity (cutBlockMin physicalPriorities cuts) := by
    convert htail using 1
    funext n
    exact hblock n
  exact
    (natSeqMinEvenParity_cutBlockMin physicalPriorities cuts_strictMono
      cuts_zero).mp hblocks

/-- Root-slot equations can also be packaged in the precise physical-cut
alignment consumed by the existing marked-bank acceptance backend.  Monitor
time is one greater than child-code time, hence the canonical offset
`rootOffset + 1`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPhysicalCutAlignment_of_rootSlots
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitial :
      profiledRawJointHybridCurrentSlots A (side 0)
          (InitialBareCode A strategy hwin control) () = some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          (ChildRunBareCodeWord A strategy hwin control direction n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (rootOffset : Nat)
    (G : FiniteGlobalRoundMachine In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (hblock : ∀ n : Nat,
      cutBlockMin
          (fun k ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + k))) cuts n =
        profiledRawJointThreadRootPriority A (root (rootOffset + n))) :
    ProfiledRawJointHybridPhysicalCompatibleExtraPhysicalCutAlignment A
      strategy hwin
        ((ChildRunPath A strategy hwin control direction).toExtraAllowedPath A
          strategy hwin)
        G outputOne outputTwo env start cuts where
  cuts_strictMono := cuts_strictMono
  cuts_zero := cuts_zero
  initialSide := side 0
  offset := rootOffset + 1
  blockMin_eq_threadPriority := fun n ↦ by
    rw [hblock n]
    have halign :=
      codedAlternatingIndexedLineageCodeRun_priority_eq_of_strictAlternation
        (InitialBareCode A strategy hwin control)
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)
        (ChildRunBareCodeWord A strategy hwin control direction) side ()
        initialRoot root hinitial hroot halternates (rootOffset + n)
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      halign.symm

end

end DetParityAutomaton

end DistributedSynthesis
