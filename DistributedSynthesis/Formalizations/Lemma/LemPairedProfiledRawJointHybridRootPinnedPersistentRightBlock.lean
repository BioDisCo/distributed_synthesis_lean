/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentPhysicalClose
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentRightBlock

/-!
# Right-block controllers below the exact guarded hybrid root

The target-parametric right monitor is instantiated with complete states of
the original root-pinned policy.  Every emitted close target is the exact
false/one-sided strict successor supplied by that policy.
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

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The guarded physical-close theorem packages as a target-parametric right
activation whose target alphabet is the complete guarded policy state. -/
theorem
    nonempty_profiledRawJointHybridInitialRootPinnedPersistentRightActivation
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {first : In₁ × In₂}
    {key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first}
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (source : ProfiledRawRightSlot A)
    (hsource : key.incidenceCode.family.right () = some source) :
    Nonempty
      (ProfiledRawJointTargetRightBlockActivation A
        (ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first)
        (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
        (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first key.state)
        source) := by
  classical
  have hvalid := installed.move_valid A
  rcases hvalid.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  refine ⟨{
    lambda := lambda
    initial_profile := hprofile
    forever := hforever
    target := fun row past input ↦
      (installed.strictSuccessorKey A
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)).state
    target_allowed := ?_
    target_state := ?_ }⟩
  · intro row past input
    exact installed.strict_allowedTarget A
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)
  · intro row past input
    rcases installed.unitRight_physicalClose A source hsource row past input
      with ⟨lambda', hlambda', _hprofile', _hforever', hslot, _⟩
    have hlambdaEq : lambda' = lambda := by
      exact Option.some.inj (hlambda'.symm.trans hlambda)
    subst lambda'
    let targetKey := installed.strictSuccessorKey A
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)
    exact
      profiledRawJointHybridInitialRootPinnedRightTargetProfiledState_eq A
        targetKey.state targetKey.incidenceCode
        (profiledRawRightChildSlot A source lambda row past input)
        targetKey.state_code hslot

/-- Every guarded right-live key therefore admits a finite controller whose
certified close targets remain states of that same guarded policy. -/
theorem
    exists_profiledRawJointHybridInitialRootPinnedPersistentRightController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {first : In₁ × In₂}
    {key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first}
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (source : ProfiledRawRightSlot A)
    (hsource : key.incidenceCode.family.right () = some source) :
    let Target :=
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first
    let targetState :=
      profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A
    let Allowed :=
      ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first key.state
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointTargetRightReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂) Target)
          Out₁
          (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
            source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source) controller.labeledTree := by
  dsimp only
  let activation := Classical.choice
    (nonempty_profiledRawJointHybridInitialRootPinnedPersistentRightActivation
      A installed source hsource)
  exact exists_profiledRawJointTargetRightController A
    (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
    (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      key.state)
    source activation

end


end DetParityAutomaton

end DistributedSynthesis
