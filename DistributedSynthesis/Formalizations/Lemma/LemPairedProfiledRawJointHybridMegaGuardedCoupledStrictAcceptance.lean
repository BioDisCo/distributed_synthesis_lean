/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedCoupledPersistentReversalAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedCoupledEventuallyFixedAcceptance

/-!
# Acceptance of every strict suffix from an aligned guarded coupled cut

Once simultaneous rounds have disappeared, the physical regime split leaves
only persistent strict reversal or eventual fixation in one strict direction.
The two guarded-coupled acceptance theorems therefore cover every such suffix.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev Mega (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

/-- Every all-strict continuation accepts from an aligned guarded coupled cut.
The regime split is proof-only and supplies either recurring reversals or a
permanently fixed strict direction. -/
theorem profiledRawJointHybridMegaGuarded_accepts_of_coupled_noBoth
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag
        ).globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentryRight :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hnoboth : ∀ k : Nat, (env (start + k)).graph ≠ .both) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hentryRight ⊢
  let tail : EnvironmentSequence In₁ In₂ := OmegaWord.drop env start
  rcases environment_physical_acceptance_regime tail with
      hboth | hstrict | hright | hleft
  · rcases hboth 0 with ⟨k, _hk, hkboth⟩
    exact False.elim (hnoboth k (by simpa [tail, OmegaWord.drop] using hkboth))
  · apply
      profiledRawJointHybridMegaGuarded_accepts_of_coupled_persistentReversal
        A strategy hwin controllers initialBank fallbackTag installation
          oldOutputOne oldOutputTwo env start hphysical hentryRight hnoboth
    simpa [tail, OmegaWord.drop] using hstrict.2
  · apply
      profiledRawJointHybridMegaGuarded_accepts_of_coupled_eventuallyFixed
        A strategy hwin controllers initialBank fallbackTag installation
          oldOutputOne oldOutputTwo env start hphysical hentryRight hnoboth
    exact Or.inl (by simpa [tail, OmegaWord.drop] using hright)
  · apply
      profiledRawJointHybridMegaGuarded_accepts_of_coupled_eventuallyFixed
        A strategy hwin controllers initialBank fallbackTag installation
          oldOutputOne oldOutputTwo env start hphysical hentryRight hnoboth
    exact Or.inr (by simpa [tail, OmegaWord.drop] using hleft)

end

end DetParityAutomaton

end DistributedSynthesis
