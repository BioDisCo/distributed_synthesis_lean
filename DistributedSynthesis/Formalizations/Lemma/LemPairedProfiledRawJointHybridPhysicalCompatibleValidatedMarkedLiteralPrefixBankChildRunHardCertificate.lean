/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionChildRunAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixOperationalAcceptance

/-!
# Hard certificates from the executable bank child run

This is the packaging boundary used by the linked controller.  An operational
trace that follows `BankChildren` already supplies an allowed accepted path;
the caller only identifies its alternating hidden slots with physical block
minima.  No equality with a separately chosen direction-path representative
is required.
-/

namespace DistributedSynthesis

universe u v x y s w

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

/-- Direct constructor for the existing marked-bank hard certificate from
the executable child-run root equations. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankHardCertificate_of_childRunRootSlots
    (controller : FinitePairedPhysicalController.{u, v, x, y, w, w}
      In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂)
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
    (start : Nat) (cuts : Nat → Nat)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (hblock : ∀ n : Nat,
      cutBlockMin
          (fun k ↦ A.priority
            (A.run
              (controller.globalMachine.globalMachineTraceWord
                controller.globalOutputOne controller.globalOutputTwo env)
              (start + k))) cuts n =
        profiledRawJointThreadRootPriority A (root (rootOffset + n))) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle
      A strategy hwin controller env :=
  ⟨control, ChildRunPath A strategy hwin control direction, start, cuts,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPhysicalCutAlignment_of_rootSlots
      A strategy hwin control direction side initialRoot root hinitial hroot
        halternates rootOffset controller.globalMachine
          controller.globalOutputOne controller.globalOutputTwo env start cuts
            cuts_strictMono cuts_zero hblock⟩

end

end DetParityAutomaton

end DistributedSynthesis
