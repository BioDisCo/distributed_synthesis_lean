/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLivePhysicalTargetCutPriority

/-!
# Acceptance of a coherent compatible-table target path

This file is the direct parity consumer for the anti-mosaic carrier.  A path
of physical table targets stays inside one compatible rational policy; hence
its positive-time bare-code word is accepted by the hybrid code DPA.  The
literal target-lineage theorem then identifies the shifted hidden-thread
priority sequence with the priorities of the physical target roots.

The final alignment has one model-specific field only: the root produced by
the actual physical table block is the root stored by the corresponding
compatible-policy transition.  It neither reselects a semantic source nor
compares independently rationalized policies.
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

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatiblePath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin policy

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := PhysicalAnnotation A)

namespace ProfiledRawJointHybridPhysicalCompatibleTargetPath

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}

/-- The positive-time bare-code word of a coherent compatible path is
accepted by the hybrid code DPA. -/
theorem codeWord_accepts
    (path : CompatiblePath A strategy hwin policy) :
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
        A))).Accepts (path.codeWord A strategy hwin) := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let linkedDPA := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointHybridCodeParityDPA A initialCode)
  let linkedInitial : LinkedCode A :=
    (initialCode, profiledRawJointHybridInitialPhysicalAnnotation A)
  let linkedValid := sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy hwin)
  let linkedRawNext :
      SourceFreeBeliefParentLinkedCode
          (BeliefCode := ProfiledRawJointHybridCode A)
          (Annotation := PhysicalAnnotation A) →
        SourceFreeBeliefParentLinkedMove
          (Direction := ProfiledRawJointHybridDirection
            (In₁ := In₁) (In₂ := In₂))
          (Move := ProfiledRawJointHybridMove A)
          (Annotation := PhysicalAnnotation A) →
        ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂) →
        SourceFreeBeliefParentLinkedCode
          (BeliefCode := ProfiledRawJointHybridCode A)
          (Annotation := PhysicalAnnotation A) :=
    sourceFreeBeliefParentLinkedNext (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridNext A)
  let linkedNext := sourceFreeBeliefFiniteCodeNext linkedRawNext
  let finitePath : SourceFreeBeliefCodeParityPolicyPath linkedDPA linkedInitial
      linkedValid linkedNext policy :=
    { state := path.state
      direction := path.codeBranch A strategy hwin
      initial := path.initial_state
      successor := fun n => (path.transition n).successor }
  have hlinked := finitePath.accepts linkedDPA linkedInitial linkedValid
    linkedNext policy
  change
    ((profiledRawJointHybridCodeParityDPA A initialCode).comap Prod.fst
      ).Accepts _ at hlinked
  rw [DetParityAutomaton.comap_accepts_iff] at hlinked
  simpa only [finitePath, initialCode,
    SourceFreeBeliefCodeParityPolicyPath.childCodeWord,
    ProfiledRawJointHybridPhysicalCompatibleTargetPath.codeWord] using hlinked

/-- Every initially selected hidden lineage along the coherent compatible
path has min-even parity. -/
theorem threadPriority_parity
    (path : CompatiblePath A strategy hwin policy)
    (initialSide : IndexedLineageSide) :
    NatSeqMinEvenParity (fun n =>
      (codedAlternatingIndexedLineageCodeThreadSystem
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A))
          (profiledRawJointHybridCurrentSlots A)
          (path.codeWord A strategy hwin) initialSide () n)) := by
  have haccepts := path.codeWord_accepts A strategy hwin
  have hcoded :
      (codedAlternatingIndexedLineageCodeDPA
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).Accepts
          (path.codeWord A strategy hwin) := by
    simpa only [profiledRawJointHybridCodeParityDPA] using haccepts
  exact
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)
      (path.codeWord A strategy hwin)).mp hcoded initialSide ()

end ProfiledRawJointHybridPhysicalCompatibleTargetPath

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev HybridInitial :
    ProfiledRawJointCommonBaseWorld A strategy :=
  initial.world A strategy

/-- Exact physical-to-compatible-path seam.  The cuts and sides are
proof-side; the sole cross-construction equation is `physical_root_eq`. -/
structure LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (policy : CompatiblePolicy A strategy hwin
      (HybridInitial A strategy (initial := initial)))
    (path : CompatiblePath A strategy hwin policy) where
  base : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  physical :
    LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily A strategy hwin
      package env base cuts
  physical_root_eq : ∀ k : Nat, physical.rootAt k = path.rootAt k

namespace LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment

variable
  {package : Package A strategy hwin (initial := initial)}
  {env : EnvironmentSequence In₁ In₂}
  {policy : CompatiblePolicy A strategy hwin
    (HybridInitial A strategy (initial := initial))}
  {path : CompatiblePath A strategy hwin policy}

/-- The exact root alignment turns compatible-path parity into the ordinary
physical epoch coupling consumed by block pasting. -/
noncomputable def epochCoupling
    (alignment :
      LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment A strategy
        hwin package env policy path) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.FiniteGlobalMachineEpochCoupling controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A
      (HybridInitial A strategy (initial := initial))).incidenceCode A)
  let priorities := fun n =>
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A)
        (path.codeWord A strategy hwin) path.initialSide () n)
  let epochPriority := fun k =>
    profiledRawJointThreadRootPriority A (path.rootAt k)
  have hfull : NatSeqMinEvenParity priorities := by
    simpa only [priorities, initialCode] using
      path.threadPriority_parity A strategy hwin path.initialSide
  have hshift : NatSeqMinEvenParity (fun k => priorities (1 + k)) :=
    (natSeqMinEvenParity_shift priorities 1).mpr hfull
  have hepoch : NatSeqMinEvenParity epochPriority := by
    convert hshift using 1
    funext k
    have hlive := path.lineage_live_at_target A strategy hwin k
    simp only [priorities, initialCode]
    rw [show 1 + k = k + 1 by omega, hlive]
    rfl
  exact {
    start := alignment.base
    cuts := alignment.cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    epochPriority := epochPriority
    epochParity := hepoch
    blockMin_eq_epochPriority := fun k => by
      calc
        _ = profiledRawJointThreadRootPriority A
              (alignment.physical.rootAt k) :=
          alignment.physical.blockMin_eq_targetPriority A strategy hwin k
        _ = epochPriority k := by
          exact congrArg (profiledRawJointThreadRootPriority A)
            (alignment.physical_root_eq k) }

/-- Productive block pasting now proves acceptance of the actual fixed
phase-live controller word. -/
theorem actualWord_accepts
    (alignment :
      LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment A strategy
        hwin package env policy path) :
    A.Accepts
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env) := by
  let controller :=
    package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy hwin
  simpa [literalCombinedFreshPhaseLiveActualWord, controller] using
    A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling
      controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env
        (alignment.epochCoupling A strategy hwin)

end LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment

/-! ## Standard four-regime acceptance from compatible paths -/

/-- Availability of one coherent compatible path in each of the two hard
graph regimes.  The selected path is proof-side and may depend on the
environment; the finite policy and executable controller remain fixed. -/
structure LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (policy : CompatiblePolicy A strategy hwin
      (HybridInitial A strategy (initial := initial))) : Prop where
  recurrent : GraphBothRecurrent (fun n => (env n).graph) →
    Nonempty (Σ path : CompatiblePath A strategy hwin policy,
      LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment A strategy
        hwin package env policy path)
  reversal : PersistentStrictReversalTail (fun n => (env n).graph) →
    Nonempty (Σ path : CompatiblePath A strategy hwin policy,
      LiteralCombinedFreshPhaseLivePhysicalCompatiblePathAlignment A strategy
        hwin package env policy path)

namespace LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments

variable
  {package : Package A strategy hwin (initial := initial)}
  {env : EnvironmentSequence In₁ In₂}
  {policy : CompatiblePolicy A strategy hwin
    (HybridInitial A strategy (initial := initial))}

/-- The recurrent-`.both` branch directly supplies the epoch coupling used by
the standard physical-acceptance record. -/
noncomputable def recurrentEpochCoupling
    (alignments :
      LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments A strategy
        hwin package env policy)
    (hboth : GraphBothRecurrent (fun n => (env n).graph)) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.FiniteGlobalMachineEpochCoupling controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let selected := Classical.choice (alignments.recurrent hboth)
  exact selected.2.epochCoupling A strategy hwin

/-- A persistent-reversal compatible alignment proves parity of the entire
actual word, hence the required tail property with start zero. -/
theorem reversalTailParity
    (alignments :
      LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments A strategy
        hwin package env policy)
    (hreversal : PersistentStrictReversalTail (fun n => (env n).graph)) :
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n => A.priority
        (A.run
          (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env)
          (start + n))) := by
  let selected := Classical.choice (alignments.reversal hreversal)
  refine ⟨0, ?_⟩
  have haccepts := selected.2.actualWord_accepts A strategy hwin
  have hparity :=
    (A.accepts_iff_natSeqMinEvenParity
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env)).mp
      haccepts
  simpa using hparity

/-- Add the independent eventually-fixed tails and expose the repository's
ordinary four-regime physical-acceptance package. -/
noncomputable def physicalAcceptance
    (alignments :
      LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments A strategy
        hwin package env policy)
    (fixedRight :
      EventuallyStrictRight (fun n => (env n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n => A.priority
            (A.run
              (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
                env) (start + n))))
    (fixedLeft :
      EventuallyStrictLeft (fun n => (env n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n => A.priority
            (A.run
              (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
                env) (start + n)))) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  dsimp only
  exact {
    recurrent := alignments.recurrentEpochCoupling A strategy hwin
    alternatingTail := by
      intro hreversal
      simpa [literalCombinedFreshPhaseLiveActualWord] using
        alignments.reversalTailParity A strategy hwin hreversal
    strictRightTail := by
      simpa [literalCombinedFreshPhaseLiveActualWord] using fixedRight
    strictLeftTail := by
      simpa [literalCombinedFreshPhaseLiveActualWord] using fixedLeft }

end LiteralCombinedFreshPhaseLivePhysicalCompatibleHardAlignments

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
