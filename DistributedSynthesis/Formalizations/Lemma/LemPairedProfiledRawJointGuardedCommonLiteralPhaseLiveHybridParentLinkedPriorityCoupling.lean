/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCarriedParentLinkedAnnotation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLivePhysicalTargetCutPriority

/-!
# Phase-live acceptance from one outer hybrid parent-linked run

The local table invariant produces a finite stage package at every physical
block boundary.  Those packages must not be interpreted as roots of freshly
and independently selected ordinary policies: such a mosaic has no global
parity argument.

This file gives the correct composition interface.  One rational policy is
selected on the whole-block hybrid semantic tree.  A proof-side branch of
that single policy follows simultaneous rounds or complete strict blocks.
Its finite linked-code component contains the annotation installed by the
parent move.  The only occurrence-sensitive handoff is therefore equality of
the physical stage package with that annotation component.  Consecutive
packages are related by the successor table of the same outer policy.

The remaining two equalities are local priority readings: the exact physical
block minimum is the priority recorded by its retained stage package, and
the outer hybrid monitor reads the same priority from its installed package.
Parity shift and block pasting then prove acceptance of the actual phase-live
controller word.

All branches, cuts, offsets, packages, and equalities below are proof-side.
No executable endpoint receives a graph, an orientation, a hierarchy side,
a strict-leader bit, a semantic state, or a policy identifier.
-/

namespace DistributedSynthesis

universe u v x y s b

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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}
variable {Annotation : Type b} [Fintype Annotation]

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev HybridInitial :
    ProfiledRawJointCommonBaseWorld A strategy :=
  initial.world A strategy

private abbrev ParentPolicy
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation) :=
  ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
    (HybridInitial A strategy (initial := initial)) initialAnnotation advance

private abbrev ParentCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := Annotation)

private abbrev HybridInitialCode : ProfiledRawJointHybridCode A :=
  .common ((profiledRawJointCommonWorldFamily A
    (HybridInitial A strategy (initial := initial))).incidenceCode A)

private abbrev HybridThreadSystem :=
  codedAlternatingIndexedLineageCodeThreadSystem
    (HybridInitialCode A strategy (initial := initial))
    (profiledRawJointHybridCurrentSlots A)
    (profiledRawJointThreadRootPriority A)

/-- Annotation component installed at depth `n` of one branch of the single
outer parent-linked policy. -/
noncomputable def literalPhaseLiveHybridParentLinkedAnnotationAt
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance)
    (codeBranch : Nat → ParentCode A (Annotation := Annotation))
    (n : Nat) : Annotation :=
  (policy.run (branchNode codeBranch n)).1.2

/-- Priority of one fixed indexed alternating lineage in the exact hybrid
code word of the outer policy path.  This is deliberately not the priority
of the universal-run DPA state: universal determinization preserves
acceptance but need not preserve any one thread priority pointwise. -/
noncomputable def literalPhaseLiveHybridParentLinkedThreadPriorityAt
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance)
    (codeBranch : Nat → ParentCode A (Annotation := Annotation))
    (initialSide : IndexedLineageSide)
    (n : Nat) : Nat :=
  (HybridThreadSystem A strategy (initial := initial)).priority
    (codedAlternatingIndexedLineageCodeRun
      (HybridInitialCode A strategy (initial := initial))
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointHybridCarriedPolicyCodeWord A strategy
        (HybridInitial A strategy (initial := initial)) initialAnnotation
          advance policy codeBranch)
      initialSide () n)

/-! ## The exact acceptance interface

The physical proof does not consume a retained package, a package-priority
reader, or a pointwise explanation of how that reader selected a lane.  It
consumes one equality only: the minimum priority of physical block `k` is the
priority of the indexed lineage at depth `offset + k` of one carried policy
branch.  Keeping that equality as the primary interface avoids accidentally
strengthening the model-specific theorem back into a fixed-policy or
orientation oracle.
-/

/-- Minimal coupling between physical blocks and one accepted carried hybrid
branch.  Every field is proof-side.  In particular `initialSide` is the index
of the lineage whose priorities are compared; it is not revealed to either
finite-state endpoint. -/
structure LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  codeBranch : Nat → ParentCode A (Annotation := Annotation)
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
              env)
            (start + n)))
        cuts k =
      literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
        initialAnnotation advance policy codeBranch initialSide (offset + k)

namespace LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment

/-- The selected lineage has min-even parity because it is one lineage of
the accepted code word of the carried policy. -/
theorem threadPriority_parity
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment A
        strategy hwin package env initialAnnotation advance policy) :
    NatSeqMinEvenParity
      (fun n ↦
        literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
          initialAnnotation advance policy alignment.codeBranch
            alignment.initialSide n) := by
  simpa [literalPhaseLiveHybridParentLinkedThreadPriorityAt] using
    profiledRawJointHybridCarriedPolicyThreadParity A strategy
      (HybridInitial A strategy (initial := initial)) initialAnnotation
        advance policy alignment.codeBranch alignment.initialSide

/-- The minimal alignment is already exactly an ordinary physical epoch
coupling. -/
noncomputable def epochCoupling
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment A
        strategy hwin package env initialAnnotation advance policy) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.FiniteGlobalMachineEpochCoupling controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  dsimp only
  exact {
    start := alignment.start
    cuts := alignment.cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    epochPriority := fun k ↦
      literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
        initialAnnotation advance policy alignment.codeBranch
          alignment.initialSide (alignment.offset + k)
    epochParity := by
      exact
        (natSeqMinEvenParity_shift
          (fun n ↦
            literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
              initialAnnotation advance policy alignment.codeBranch
                alignment.initialSide n)
          alignment.offset).mpr
          (alignment.threadPriority_parity A strategy)
    blockMin_eq_epochPriority := by
      intro k
      simpa [literalCombinedFreshPhaseLiveActualWord] using
        alignment.blockMin_eq_threadPriority k }

/-- Productive block pasting transfers parity of the one carried branch to
the actual controller word. -/
theorem actualWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment A
        strategy hwin package env initialAnnotation advance policy) :
    A.Accepts
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env) := by
  let controller :=
    package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy hwin
  simpa [literalCombinedFreshPhaseLiveActualWord, controller] using
    A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling
      controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env (alignment.epochCoupling A strategy hwin)

end LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment

/-! ## Anchor-free physical targets into the carried lineage -/

/-- The exact seam between the already proved physical target-cut family and
one carried policy branch.  The physical half supplies the target root and
its actual block-minimum equation.  The only remaining model-specific field
says that this target-root priority is the priority read by the same indexed
lineage of the carried code branch.

This is intentionally weaker than equality of semantic representatives,
annotations, tables, or policies. -/
structure LiteralCombinedFreshPhaseLivePhysicalTargetLineageAlignment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance) where
  base : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  physical :
    LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily A strategy hwin
      package env base cuts
  codeBranch : Nat → ParentCode A (Annotation := Annotation)
  initialSide : IndexedLineageSide
  offset : Nat
  targetPriority_eq_threadPriority : ∀ k : Nat,
    profiledRawJointThreadRootPriority A (physical.rootAt k) =
      literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
        initialAnnotation advance policy codeBranch initialSide (offset + k)

namespace LiteralCombinedFreshPhaseLivePhysicalTargetLineageAlignment

/-- Compose the anchor-free physical theorem with the one-lineage root
equality.  This is the complete recurrent/reversal acceptance coupling. -/
noncomputable def epochAlignment
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLivePhysicalTargetLineageAlignment A strategy
        hwin package env initialAnnotation advance policy) :
    LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment A strategy
      hwin package env initialAnnotation advance policy :=
  { start := alignment.base
    cuts := alignment.cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    codeBranch := alignment.codeBranch
    initialSide := alignment.initialSide
    offset := alignment.offset
    blockMin_eq_threadPriority := fun k ↦
      (alignment.physical.blockMin_eq_targetPriority A strategy hwin k).trans
        (alignment.targetPriority_eq_threadPriority k) }

/-- Direct acceptance consequence of the composed anchor-free seam. -/
theorem actualWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLivePhysicalTargetLineageAlignment A strategy
        hwin package env initialAnnotation advance policy) :
    A.Accepts
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env) :=
  (alignment.epochAlignment A strategy hwin).actualWord_accepts A strategy

end LiteralCombinedFreshPhaseLivePhysicalTargetLineageAlignment

/-- Provenance-guarded version of the preceding seam.  At every physical
cut, the target root must occur literally as the live root of the selected
carried code run.  A concrete proof of `lineage_live_at_target` must retain
the predecessor move which installed the current physical table; reinverting
the current finite state and selecting an unrelated semantic source is not
enough.

The existential `side` and `code` are proof-side observations of the monitor
state.  Neither is controller input. -/
structure LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance) where
  base : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  physical :
    LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily A strategy hwin
      package env base cuts
  codeBranch : Nat → ParentCode A (Annotation := Annotation)
  initialSide : IndexedLineageSide
  offset : Nat
  lineage_live_at_target : ∀ k : Nat,
    ∃ side : IndexedLineageSide,
      ∃ code : ProfiledRawJointHybridCode A,
        codedAlternatingIndexedLineageCodeRun
            (HybridInitialCode A strategy (initial := initial))
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointHybridCarriedPolicyCodeWord A strategy
              (HybridInitial A strategy (initial := initial))
              initialAnnotation advance policy codeBranch)
            initialSide () (offset + k) =
          (code, .live side () (physical.rootAt k))

namespace LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment

/-- Instantiate the guarded alignment on the canonical *graph-only*
operational close cuts.  Unlike the retired canonical-policy schedule, these
cuts depend solely on the physical graph trace and a proof of termination of
strict runs. -/
noncomputable def ofOperationalCloseCuts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base))
    (physical :
      LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily A strategy hwin
        package env base
          (operationalCloseCuts
            (profiledRawJointPhysicalGraphTail env base) hterm))
    (codeBranch : Nat → ParentCode A (Annotation := Annotation))
    (initialSide : IndexedLineageSide)
    (offset : Nat)
    (lineage_live_at_target : ∀ k : Nat,
      ∃ side : IndexedLineageSide,
        ∃ code : ProfiledRawJointHybridCode A,
          codedAlternatingIndexedLineageCodeRun
              (HybridInitialCode A strategy (initial := initial))
              (profiledRawJointHybridCurrentSlots A)
              (profiledRawJointHybridCarriedPolicyCodeWord A strategy
                (HybridInitial A strategy (initial := initial))
                initialAnnotation advance policy codeBranch)
              initialSide () (offset + k) =
            (code, .live side () (physical.rootAt k))) :
    LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment A strategy
      hwin package env initialAnnotation advance policy :=
  { base := base
    cuts := operationalCloseCuts
      (profiledRawJointPhysicalGraphTail env base) hterm
    cuts_strictMono := operationalCloseCuts_strictMono
      (profiledRawJointPhysicalGraphTail env base) hterm
    cuts_zero := operationalCloseCuts_zero
      (profiledRawJointPhysicalGraphTail env base) hterm
    physical := physical
    codeBranch := codeBranch
    initialSide := initialSide
    offset := offset
    lineage_live_at_target := lineage_live_at_target }

/-- Literal live-root alignment supplies the priority-only seam, with no
universal-DPA state-priority identification. -/
noncomputable def toTargetLineageAlignment
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment A strategy
        hwin package env initialAnnotation advance policy) :
    LiteralCombinedFreshPhaseLivePhysicalTargetLineageAlignment A strategy
      hwin package env initialAnnotation advance policy :=
  { base := alignment.base
    cuts := alignment.cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    physical := alignment.physical
    codeBranch := alignment.codeBranch
    initialSide := alignment.initialSide
    offset := alignment.offset
    targetPriority_eq_threadPriority := fun k ↦ by
      obtain ⟨side, code, hlive⟩ := alignment.lineage_live_at_target k
      unfold literalPhaseLiveHybridParentLinkedThreadPriorityAt
      rw [hlive]
      rfl }

/-- The provenance-guarded alignment already closes acceptance. -/
theorem actualWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (alignment :
      LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment A strategy
        hwin package env initialAnnotation advance policy) :
    A.Accepts
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env) :=
  (alignment.toTargetLineageAlignment A strategy hwin).actualWord_accepts A
    strategy

end LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment

/-- Exact composition data between the physical phase-live block cuts and
one accepted parent-linked hybrid policy branch.

`stagePackage_eq_parentAnnotation` is the unique cross-construction socket:
it says that the stage retained by the physical table is the package selected
by the same outer run.  Since all right-hand annotations are read from one
`policy.run`, their successor lineage is already the policy's parent-selected
whole-block advance, rather than a sequence of unrelated ordinary policies.
-/
structure LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  /-- Finite child-code tags of the one selected outer run.  The semantic
  carrier constructs each tag from one simultaneous or whole-strict-block
  advance before it is placed here. -/
  codeBranch : Nat → ParentCode A (Annotation := Annotation)
  initialSide : IndexedLineageSide
  offset : Nat
  stagePackage : Nat → Annotation
  /-- Proof-side priority reader at epoch `k`.  The epoch argument may select
  the live lane from an annotation which stores both sibling tables.  It is
  not executable controller data and gives neither process an orientation or
  strict-leader signal. -/
  stagePriority : Nat → Annotation → Nat
  stagePackage_eq_parentAnnotation : ∀ k : Nat,
    stagePackage k =
      literalPhaseLiveHybridParentLinkedAnnotationAt A strategy
        initialAnnotation advance policy codeBranch (offset + k)
  blockMin_eq_stagePackagePriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
              env)
            (start + n)))
        cuts k = stagePriority k (stagePackage k)
  threadPriority_eq_packagePriority : ∀ k : Nat,
    literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
        initialAnnotation advance policy codeBranch initialSide (offset + k) =
      stagePriority k
        (literalPhaseLiveHybridParentLinkedAnnotationAt A strategy
          initialAnnotation advance policy codeBranch (offset + k))

namespace LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling

/-- Eliminate the retained stage package: each actual block minimum is the
priority of the chosen indexed lineage of the one outer hybrid policy path. -/
theorem blockMin_eq_threadPriority
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (coupling :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling A
        strategy hwin package env initialAnnotation advance policy)
    (k : Nat) :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
              env)
            (coupling.start + n)))
        coupling.cuts k =
      literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
        initialAnnotation advance policy coupling.codeBranch
          coupling.initialSide (coupling.offset + k) := by
  rw [coupling.blockMin_eq_stagePackagePriority,
    coupling.stagePackage_eq_parentAnnotation,
    ← coupling.threadPriority_eq_packagePriority]

/-- Forget the optional package-level explanation and retain exactly the
direct equality consumed by acceptance. -/
noncomputable def epochAlignment
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (coupling :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling A
        strategy hwin package env initialAnnotation advance policy) :
    LiteralCombinedFreshPhaseLiveHybridParentLinkedEpochAlignment A strategy
      hwin package env initialAnnotation advance policy :=
  { start := coupling.start
    cuts := coupling.cuts
    cuts_strictMono := coupling.cuts_strictMono
    cuts_zero := coupling.cuts_zero
    codeBranch := coupling.codeBranch
    initialSide := coupling.initialSide
    offset := coupling.offset
    blockMin_eq_threadPriority :=
      coupling.blockMin_eq_threadPriority A strategy hwin }

/-- Every indexed lineage of the accepted hybrid code word has min-even
parity; specialize this universal fact to the side retained by the physical
coupling. -/
theorem threadPriority_parity
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (coupling :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling A
        strategy hwin package env initialAnnotation advance policy) :
    NatSeqMinEvenParity
      (fun n ↦
        literalPhaseLiveHybridParentLinkedThreadPriorityAt A strategy
          initialAnnotation advance policy coupling.codeBranch
            coupling.initialSide n) := by
  simpa [literalPhaseLiveHybridParentLinkedThreadPriorityAt] using
    profiledRawJointHybridCarriedPolicyThreadParity A strategy
      (HybridInitial A strategy (initial := initial)) initialAnnotation
        advance policy coupling.codeBranch coupling.initialSide

/-- Package the one-run priority alignment directly as the repository's
ordinary physical epoch coupling.  This is the final generic seam needed by
the recurrent physical-acceptance interface: every epoch priority is read
from the same carried parent-linked run, and the only concrete obligation
remains `stagePackage_eq_parentAnnotation` inside `coupling`. -/
noncomputable def epochCoupling
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (coupling :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling A
        strategy hwin package env initialAnnotation advance policy) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.FiniteGlobalMachineEpochCoupling controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  exact (coupling.epochAlignment A strategy hwin).epochCoupling A strategy hwin

/-- Parity shift plus productive block pasting transfers the accepted outer
hybrid run to the actual word emitted by the phase-live controller. -/
theorem actualWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (coupling :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling A
        strategy hwin package env initialAnnotation advance policy) :
    A.Accepts
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env) := by
  exact (coupling.epochAlignment A strategy hwin).actualWord_accepts A strategy

/-- The preceding theorem stated directly at the existing finite physical
controller interface. -/
theorem rootTraceWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (coupling :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling A
        strategy hwin package env initialAnnotation advance policy) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  exact coupling.actualWord_accepts A strategy

end LiteralCombinedFreshPhaseLiveHybridParentLinkedPriorityCoupling

/-! ## The two hard graph regimes through the one carried policy -/

/-- Proof-side availability of the exact carried-policy coupling in the two
nontrapped physical regimes.  Both fields use the same finite annotation,
advance law, and outer rational policy; only the environment-dependent cuts
and selected indexed lineage may differ.

The graph hypotheses select proof objects only.  They are not inputs of the
finite controller or of either local endpoint. -/
structure LiteralCombinedFreshPhaseLiveHybridParentLinkedHardCouplings
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance) : Prop where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      Nonempty
        (LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment A
          strategy hwin package env initialAnnotation advance policy)
  reversal :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      Nonempty
        (LiteralCombinedFreshPhaseLivePhysicalTargetCodeRunAlignment A
          strategy hwin package env initialAnnotation advance policy)

namespace LiteralCombinedFreshPhaseLiveHybridParentLinkedHardCouplings

/-- Recurrent `.both` field at the generic physical-acceptance interface. -/
noncomputable def recurrentEpochCoupling
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (couplings :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedHardCouplings A strategy
        hwin package env initialAnnotation advance policy)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.FiniteGlobalMachineEpochCoupling controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env := by
  let coupling := Classical.choice (couplings.recurrent hboth)
  exact
    (coupling.toTargetLineageAlignment A strategy hwin).epochAlignment A
      strategy hwin |>.epochCoupling A strategy hwin

/-- A persistent reversal coupling already proves parity of the whole actual
word, hence supplies the alternating-tail field with tail start zero. -/
noncomputable def reversalTailParity
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (couplings :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedHardCouplings A strategy
        hwin package env initialAnnotation advance policy)
    (hreversal : PersistentStrictReversalTail
      (fun n ↦ (env n).graph)) :
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.run
          (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env)
          (start + n))) := by
  let coupling := Classical.choice (couplings.reversal hreversal)
  refine ⟨0, ?_⟩
  have haccepts := coupling.actualWord_accepts A strategy hwin
  have hparity :=
    (A.accepts_iff_natSeqMinEvenParity
      (literalCombinedFreshPhaseLiveActualWord A strategy hwin package env)).mp
      haccepts
  simpa using hparity

/-- Add the two already separate eventually-fixed tail obligations and expose
the standard four-regime physical-acceptance package consumed by readback. -/
noncomputable def physicalAcceptance
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    {initialAnnotation : Annotation}
    {advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation}
    {policy : ParentPolicy A strategy (initial := initial) initialAnnotation
      advance}
    (couplings :
      LiteralCombinedFreshPhaseLiveHybridParentLinkedHardCouplings A strategy
        hwin package env initialAnnotation advance policy)
    (fixedRight :
      EventuallyStrictRight (fun n ↦ (env n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n ↦ A.priority
            (A.run
              (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
                env) (start + n))))
    (fixedLeft :
      EventuallyStrictLeft (fun n ↦ (env n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n ↦ A.priority
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
    recurrent := couplings.recurrentEpochCoupling A strategy hwin
    alternatingTail := by
      intro hreversal
      simpa [literalCombinedFreshPhaseLiveActualWord] using
        couplings.reversalTailParity A strategy hwin hreversal
    strictRightTail := by
      simpa [literalCombinedFreshPhaseLiveActualWord] using fixedRight
    strictLeftTail := by
      simpa [literalCombinedFreshPhaseLiveActualWord] using fixedLeft }

end LiteralCombinedFreshPhaseLiveHybridParentLinkedHardCouplings

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
