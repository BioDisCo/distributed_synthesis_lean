/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyBankDirectionPath
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeStrictAlternation
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Strict alternating root parity of a marked-bank direction path

Every direction-driven path through a selected marked bank is accepted by the
existing code-only parity automaton.  This file combines that fact with the
generic strict-alternation indexing lemma: once operational cut packets show
that successive child codes expose the crossed physical roots, those roots
have min-even parity.  A final adapter pastes equal physical block minima.

Only proof-side sides, roots, and cuts occur below.  They are not controller
inputs and in particular do not reveal a strict leader to either process.
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

private abbrev Installed
    (control : CommonControl A strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
    hwin control

private abbrev DirectionPath
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
    strategy hwin control direction

private abbrev InitialBareCode
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridCode A :=
  .common
    ((profiledRawJointCommonWorldFamily A
      (Installed A strategy hwin control).world).incidenceCode A)

private abbrev DirectionBareCodeWord
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :=
  ((DirectionPath A strategy hwin control direction).toExtraAllowedPath A
    strategy hwin).bareCodeWord A strategy hwin

/-- If successive direction-path codes expose a crossed root on a proof-side
alternating side stream, the priorities of exactly those roots are min-even.
This consumes the bank path's already-proved code acceptance; it introduces no
new winning or rationalization premise. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_rootPriorities_minEven_of_strictAlternatingSlots
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitial :
      profiledRawJointHybridCurrentSlots A (side 0)
          (InitialBareCode A strategy hwin control) () =
        some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          (DirectionBareCodeWord A strategy hwin control direction n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other) :
    NatSeqMinEvenParity
      (fun n ↦ profiledRawJointThreadRootPriority A (root n)) := by
  let path := DirectionPath A strategy hwin control direction
  let initialCode := InitialBareCode A strategy hwin control
  let word := DirectionBareCodeWord A strategy hwin control direction
  have hcode :
      (profiledRawJointHybridCodeParityDPA A initialCode).Accepts word := by
    simpa [path, initialCode, word, InitialBareCode, DirectionBareCodeWord,
      DirectionPath, Installed] using
      (path.bareCodeWord_accepts A strategy hwin)
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

/-- Physical block minima equal to the crossed bank roots inherit min-even
parity directly.  This is the final omega-combinatorial consumer expected by
the operational cut packets. -/
theorem
    physicalPriorities_minEven_of_bankDirectionPath_strictAlternatingSlots
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitial :
      profiledRawJointHybridCurrentSlots A (side 0)
          (InitialBareCode A strategy hwin control) () =
        some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          (DirectionBareCodeWord A strategy hwin control direction n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (physicalPriorities : Nat → Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (hblock : ∀ n : Nat,
      cutBlockMin physicalPriorities cuts n =
        profiledRawJointThreadRootPriority A (root n)) :
    NatSeqMinEvenParity physicalPriorities := by
  have hroots :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_rootPriorities_minEven_of_strictAlternatingSlots
      A strategy hwin control direction side initialRoot root hinitial hroot
        halternates
  have hblocks : NatSeqMinEvenParity (cutBlockMin physicalPriorities cuts) := by
    convert hroots using 1
    funext n
    exact hblock n
  exact
    (natSeqMinEvenParity_cutBlockMin physicalPriorities cuts_strictMono
      cuts_zero).mp hblocks

/-- Suffix form used by a persistent-reversal execution.  The accepted bank
path and its hidden lineage start at the marked root, while physical block
pasting may discard an arbitrary finite number of bootstrap/cut packets.
Finite-prefix invariance is applied only in the proof; `rootOffset` is not an
executable controller input. -/
theorem
    physicalPriorities_minEven_of_bankDirectionPath_strictAlternatingSlots_from
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitial :
      profiledRawJointHybridCurrentSlots A (side 0)
          (InitialBareCode A strategy hwin control) () =
        some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          (DirectionBareCodeWord A strategy hwin control direction n) () =
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_rootPriorities_minEven_of_strictAlternatingSlots
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

end

end DetParityAutomaton

end DistributedSynthesis
