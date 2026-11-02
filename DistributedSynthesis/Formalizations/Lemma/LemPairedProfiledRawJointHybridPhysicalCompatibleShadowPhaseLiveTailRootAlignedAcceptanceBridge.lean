/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailResolvedCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRootAlignedPath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLivePhysicalAcceptance

/-!
# Root-aligned tail traces imply physical acceptance

The resolved-cut layer produces, at every physical close, an allowed exact
tail transition whose target root carries the physical block minimum.  The
root-aligned-path layer proves that the same target root is the hidden
lineage state two code steps later.  This file is the generic adapter between
those two facts and the final physical-acceptance certificate.

The only controller-specific residual is deliberately small:

* a decoding of finite controller states into tail states;
* equality of that decoding with one root-aligned path at every close cut;
* the physical block-minimum equation supplied by the resolved cuts.

In particular, the lineage offset is not an input.  It is proved to be `2`:
one step enters the literal tagged child and the next enters the first
root-aligned tail target.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-- Exact trace data left after the literal-prefix and resolved-cut theorems
have been applied at every close.  All roots and sides are proof-side data of
`path`; they are not inputs to the finite controller. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  /-- Total controller-state decoding.  Only its values at close cuts matter. -/
  closeState : G.State → TailState A strategy hwin tag
  /-- The root-aligned branch selected by the exact close transitions. -/
  path :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin tag
  /-- Controller trace states at cuts decode to the selected branch. -/
  closeState_eq_path : ∀ n : Nat,
    closeState (G.globalStateTrace env (start + cuts n)) = path.state n
  /-- Output of the per-cut resolved-cut calculation, with the target move
  source rewritten to the root retained in `path.transition k`. -/
  blockMin_eq_rootPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      profiledRawJointThreadRootPriority A (path.rootAt k)

namespace
  ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping

/-- The code word read from controller close states is exactly the bare code
word of the root-aligned path. -/
theorem closeCodeWord_eq_pathCodeWord
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping
        A strategy hwin tag G outputOne outputTwo env start cuts) :
    profiledRawJointHybridFirstChildCodeWord A
        (tag.childCode A strategy hwin).1
        (fun n ↦
          (bookkeeping.closeState
            (G.globalStateTrace env (start + cuts (n + 1)))).1.1) =
      bookkeeping.path.codeWord A strategy hwin := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [profiledRawJointHybridFirstChildCodeWord_succ,
        ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath.codeWord_succ]
      rw [bookkeeping.closeState_eq_path (n + 1)]

/-- Root alignment fixes the complete hard-regime acceptance certificate.
The offset is definitionally `2`, rather than an additional scheduling
hypothesis. -/
noncomputable def physicalAcceptanceCertificate
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping
        A strategy hwin tag G outputOne outputTwo env start cuts) :
    ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate A
      strategy hwin tag G outputOne outputTwo env start cuts := by
  refine {
    cuts_strictMono := bookkeeping.cuts_strictMono
    cuts_zero := bookkeeping.cuts_zero
    closeState := bookkeeping.closeState
    close_zero := ?_
    close_step := ?_
    initialSide := bookkeeping.path.initialSide
    offset := 2
    blockMin_eq_threadPriority := ?_ }
  · rw [bookkeeping.closeState_eq_path 0]
    exact bookkeeping.path.state_zero
  · intro n
    rw [bookkeeping.closeState_eq_path n,
      bookkeeping.closeState_eq_path (n + 1)]
    exact bookkeeping.path.allowed A strategy hwin n
  · intro k
    dsimp only
    rw [bookkeeping.closeCodeWord_eq_pathCodeWord A strategy hwin]
    have hthread :=
      bookkeeping.path.threadPriority_eq_rootPriority A strategy hwin k
    exact bookkeeping.blockMin_eq_rootPriority k |>.trans (by
      simpa only [Nat.add_comm] using hthread.symm)

/-- Direct acceptance corollary for the actual finite-controller trace. -/
theorem accepts
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (bookkeeping :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping
        A strategy hwin tag G outputOne outputTwo env start cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (bookkeeping.physicalAcceptanceCertificate A strategy hwin).accepts A
    strategy hwin

end
  ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping

end

end DetParityAutomaton

end DistributedSynthesis
