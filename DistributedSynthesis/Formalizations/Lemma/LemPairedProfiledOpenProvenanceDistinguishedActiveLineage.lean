/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenActivePivotFromProvenance
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeLiveness

/-!
# A persistent lineage in the accepted distinguished provenance stream

The finite distinguished stream already follows the selected provenance code
policy and is accepted.  This file couples that stream to the active-lineage
persistence theorem.

The only query-side premise is literal activity of the pivot selected on the
proof-side current orientation.  Provenance validity supplies
row-functionality and semantic reflexivity.  The side is not observed by a
process: it is the hidden side coordinate already carried by the witnessed
query.  The result selects one fixed lineage which is active both at every
source code and at the cross-swapped target of every transition.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable
  (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev ActiveLineageQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev ActiveLineageState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

/-- The finite distinguished state at one query index. -/
private noncomputable abbrev activeLineageStateAt
    (query : Nat → ActiveLineageQuery A initialCode) (n : Nat) :
    ActiveLineageState A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package :=
  profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package query n

/-- Its actual finite base descriptor. -/
private noncomputable abbrev activeLineageDescriptorAt
    (query : Nat → ActiveLineageQuery A initialCode) (n : Nat) :
    ProfiledOpenWitnessedTableBaseDescriptor A initialCode :=
  profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package
      (activeLineageStateAt A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query n)

/-- Public indexed code at one distinguished stream position. -/
private noncomputable abbrev activeLineageCodeAt
    (query : Nat → ActiveLineageQuery A initialCode) (n : Nat) :
    ProfiledOpenIndexedBiBeliefCode A (I := I) :=
  (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package query n).code

/-- Positive-time code word read by the code-only lineage monitor. -/
private noncomputable abbrev activeLineageCodeWord
    (query : Nat → ActiveLineageQuery A initialCode) :
    OmegaWord (ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  fun n ↦ activeLineageCodeAt A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package query (n + 1)

/-- The hidden side named by one witnessed query. -/
private abbrev activeLineageSideAt
    (query : Nat → ActiveLineageQuery A initialCode) (n : Nat) :
    IndexedLineageSide :=
  (query n).1.1.1

/-- The raw representative selected by the query's finite direction tag at
the actual current descriptor. -/
private noncomputable abbrev activeLineageDirectionAt
    (query : Nat → ActiveLineageQuery A initialCode) (n : Nat) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  profiledOpenIndexedRawDirectionOfFiniteTag A
    (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query n).code
    (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query n).moveIdentity
    (query n).1.2

/-- Literal activity of the query-selected pivot on its proof-side source
orientation.  This is strictly weaker than the reflexive-pivot condition:
the missing semantic facts are recovered from provenance validity. -/
def ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive
    (query : Nat → ActiveLineageQuery A initialCode) : Prop :=
  ∀ n,
    let descriptor := activeLineageDescriptorAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query n
    let direction := activeLineageDirectionAt A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query n
    match activeLineageSideAt A initialCode query n with
    | .right => descriptor.code.rightSlots direction.rightPivot.1 ≠ none
    | .left => descriptor.code.leftSlots direction.leftPivot.1 ≠ none

/-- The delayed physical recut alternates the hidden source orientation from
one completed query to the next. -/
def ProfiledOpenProvenancePolicyDistinguishedQueryAlternates
    (query : Nat → ActiveLineageQuery A initialCode) : Prop :=
  ∀ n, activeLineageSideAt A initialCode query (n + 1) =
    (activeLineageSideAt A initialCode query n).other

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Generic external-side adapter.  If a physical recut branch proves that
query `n` carries its proof-side `side n`, ordinary side alternation gives the
exact query alternation premise used below. -/
theorem
    profiledOpenProvenancePolicyDistinguishedQueryAlternates_of_side
    (query : Nat → ActiveLineageQuery A initialCode)
    (side : Nat → IndexedLineageSide)
    (hquerySide : ∀ n,
      activeLineageSideAt A initialCode query n = side n)
    (halternates : ∀ n, side (n + 1) = (side n).other) :
    ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
      query := by
  intro n
  rw [hquerySide (n + 1), hquerySide n]
  exact halternates n

/-- The descriptor code follows the finite-tag successor selected by the
query.  This is extracted from the distinguished policy successor and the
source endpoint's move-realization certificate. -/
theorem profiledOpenProvenancePolicyDistinguishedDescriptorAt_code_succ
    (query : Nat → ActiveLineageQuery A initialCode) (n : Nat) :
    (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query (n + 1)).code =
      profiledOpenIndexedBiBeliefNextFiniteTag A
        (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n).code
        (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n).moveIdentity
        (query n).1.2 := by
  have hsuccessor :=
    profiledOpenProvenancePolicyDistinguishedStateAt_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query n
  have hrealizes :=
    (profiledOpenProvenancePolicyDistinguishedStateAt_moveRealizes A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query n).1
  have htag := hrealizes.2 (query n).1.2
  calc
    (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query (n + 1)).code =
        (codePolicy.successor
          (activeLineageDescriptorAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query n).1
          (query n).1.2).1 := congrArg Prod.fst hsuccessor
    _ = profiledOpenIndexedBiBeliefNextFiniteTag A
          (activeLineageDescriptorAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query n).code
          (activeLineageDescriptorAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query n
            ).moveIdentity
          (query n).1.2 := congrArg Prod.fst htag

/-- The actual distinguished query stream, packaged for the generic
finite-tag persistence theorem. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedActiveTagStream
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ProfiledOpenIndexedAlternatingActiveFiniteTagStream A (I := I)
      (In₁ := In₁) (In₂ := In₂) where
  code := fun n ↦
    (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query n).code
  move := fun n ↦
    (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query n).moveIdentity
  tag := fun n ↦ (query n).1.2
  side := fun n ↦ activeLineageSideAt A initialCode query n
  next := profiledOpenProvenancePolicyDistinguishedDescriptorAt_code_succ A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package query
  alternates := halternates
  active := by
    intro n
    have hrealizes :=
      (profiledOpenProvenancePolicyDistinguishedStateAt_moveRealizes A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        query n).1
    exact profiledOpenIndexedProvenanceValid_activeReflexivePivot A strategy
      hwin basis _ _ _ (activeLineageSideAt A initialCode query n)
        hrealizes.1 (hactive n)

/-- One fixed lineage is active at every source position of the actual
distinguished stream. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_lineage_active_forever
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ∃ lineage, ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageDescriptorAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n).code lineage ≠ none :=
  (profiledOpenProvenancePolicyDistinguishedActiveTagStream A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package query
      halternates hactive).exists_lineage_active_forever A

/-- Exact source/target slot form consumed by the epoch-priority coupling.
The same lineage is active before every query and in the cross-swapped target
code immediately after it. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_lineage_source_target
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ∃ lineage,
      (∀ n,
        profiledOpenIndexedBiBeliefCurrentSlots A
          (activeLineageSideAt A initialCode query n)
          (activeLineageDescriptorAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query n).code
          lineage ≠ none) ∧
      (∀ n,
        profiledOpenIndexedBiBeliefCurrentSlots A
          (activeLineageSideAt A initialCode query n).other
          (activeLineageDescriptorAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query (n + 1)).code
          lineage ≠ none) := by
  obtain ⟨lineage, hlineage⟩ :=
    exists_profiledOpenProvenancePolicyDistinguished_lineage_active_forever A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates hactive
  refine ⟨lineage, hlineage, fun n ↦ ?_⟩
  rw [← halternates n]
  exact hlineage (n + 1)

/-- External-side form for a physical recut branch.  It keeps the exact same
distinguished state/code stream and fixed lineage; only the proof-side query
side is rewritten to the branch's independently supplied `side` sequence. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_lineage_for_side
    (query : Nat → ActiveLineageQuery A initialCode)
    (side : Nat → IndexedLineageSide)
    (hquerySide : ∀ n,
      activeLineageSideAt A initialCode query n = side n)
    (halternates : ∀ n, side (n + 1) = (side n).other)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ∃ lineage,
      (∀ n,
        profiledOpenIndexedBiBeliefCurrentSlots A (side n)
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query n) lineage ≠ none) ∧
      (∀ n,
        profiledOpenIndexedBiBeliefCurrentSlots A (side n).other
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query (n + 1)) lineage ≠
          none) := by
  let hqueryAlternates :=
    profiledOpenProvenancePolicyDistinguishedQueryAlternates_of_side A
      initialCode query side hquerySide halternates
  obtain ⟨lineage, hsource, htarget⟩ :=
    exists_profiledOpenProvenancePolicyDistinguished_lineage_source_target A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query hqueryAlternates hactive
  refine ⟨lineage, ?_, ?_⟩
  · intro n
    rw [← hquerySide n]
    exact hsource n
  · intro n
    rw [← hquerySide n]
    exact htarget n

/-! ## The code-only monitor is literally live -/

/-- Source-slot activity of one fixed lineage determines the exact live state
of its code-only alternating monitor at every positive time.  In particular,
this theorem supplies the `never dead` premise expected by the existing
code-liveness and semantic-parity adapters; it is not an additional
assumption. -/
theorem
    profiledOpenProvenancePolicyDistinguished_codeRun_live_of_active_lineage
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none) :
    ∀ n, ∃ root,
      codedAlternatingIndexedLineageCodeRun
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query 0)
          (profiledOpenIndexedBiBeliefCurrentSlots A)
          (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query)
          (activeLineageSideAt A initialCode query 0) lineage (n + 1) =
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query (n + 1),
          .live (activeLineageSideAt A initialCode query (n + 1)) lineage
            root) ∧
      profiledOpenIndexedBiBeliefCurrentSlots A
          (activeLineageSideAt A initialCode query (n + 1))
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query (n + 1)) lineage =
        some root := by
  intro n
  induction n with
  | zero =>
      obtain ⟨sourceRoot, hsourceRoot⟩ :=
        Option.ne_none_iff_exists'.mp (hlineage 0)
      obtain ⟨childRoot, hchildRootAt⟩ :=
        Option.ne_none_iff_exists'.mp (hlineage 1)
      have hchildRoot :
          profiledOpenIndexedBiBeliefCurrentSlots A
              (activeLineageSideAt A initialCode query 0).other
              (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query 1) lineage =
            some childRoot := by
        rw [← halternates 0]
        exact hchildRootAt
      refine ⟨childRoot, ?_, hchildRootAt⟩
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) nextCode ↦ nextCode)
            (profiledOpenIndexedBiBeliefCurrentSlots A)
            (codedAlternatingIndexedLineageCodeChild
              (profiledOpenIndexedBiBeliefCurrentSlots A))
            (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query 0,
              .initial)
            (Unit.unit,
              activeLineageCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query 1)
            (activeLineageSideAt A initialCode query 0, lineage) = _
      rw [codedAlternatingIndexedLineageCodeStep_initial_of
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 1)
        (activeLineageSideAt A initialCode query 0) lineage sourceRoot childRoot
        hsourceRoot hchildRoot]
      rw [halternates 0]
  | succ n ih =>
      obtain ⟨currentRoot, hrun, hcurrentRoot⟩ := ih
      obtain ⟨childRoot, hchildRootAt⟩ :=
        Option.ne_none_iff_exists'.mp (hlineage (n + 2))
      have hchildRoot :
          profiledOpenIndexedBiBeliefCurrentSlots A
              (activeLineageSideAt A initialCode query (n + 1)).other
              (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query (n + 2)) lineage =
            some childRoot := by
        rw [← halternates (n + 1)]
        exact hchildRootAt
      refine ⟨childRoot, ?_, hchildRootAt⟩
      rw [show n + 2 = (n + 1) + 1 by omega]
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) nextCode ↦ nextCode)
            (profiledOpenIndexedBiBeliefCurrentSlots A)
            (codedAlternatingIndexedLineageCodeChild
              (profiledOpenIndexedBiBeliefCurrentSlots A))
            (codedAlternatingIndexedLineageCodeRun
              (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query 0)
              (profiledOpenIndexedBiBeliefCurrentSlots A)
              (activeLineageCodeWord A strategy hwin basis initialCode
                codePolicy fixedPolicy point initialRoot package query)
              (activeLineageSideAt A initialCode query 0) lineage (n + 1))
            (Unit.unit,
              activeLineageCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query (n + 2))
            (activeLineageSideAt A initialCode query 0, lineage) = _
      rw [hrun]
      rw [codedAlternatingIndexedLineageCodeStep_live_of
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query (n + 1))
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query (n + 2))
        (activeLineageSideAt A initialCode query (n + 1)) lineage currentRoot
        childRoot (activeLineageSideAt A initialCode query 0, lineage)
        hcurrentRoot hchildRoot]
      rw [halternates (n + 1)]

/-- The fixed lineage extracted from the distinguished stream has a
never-dead code-only monitor run. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_lineage_neverDead
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ∃ lineage, ∀ n,
      (codedAlternatingIndexedLineageCodeRun
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query 0)
          (profiledOpenIndexedBiBeliefCurrentSlots A)
          (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query)
          (activeLineageSideAt A initialCode query 0) lineage (n + 1)).2 ≠
        .dead := by
  obtain ⟨lineage, hlineage⟩ :=
    exists_profiledOpenProvenancePolicyDistinguished_lineage_active_forever A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates hactive
  refine ⟨lineage, fun n hdead ↦ ?_⟩
  obtain ⟨root, hrun, hslot⟩ :=
    profiledOpenProvenancePolicyDistinguished_codeRun_live_of_active_lineage A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates lineage hlineage n
  rw [hrun] at hdead
  cases hdead

/-! ## Exact positive-time root priorities -/

/-- The unique root stored for the persistent lineage at positive code time
`n + 1`.  This is also the target slot of completed query `n` after using
side alternation. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedTargetRootAt
    (query : Nat → ActiveLineageQuery A initialCode)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none)
    (n : Nat) : ProfiledOpenClassifiedAnchor A :=
  Classical.choose (Option.ne_none_iff_exists'.mp (hlineage (n + 1)))

/-- Literal source-side slot equation defining the selected positive-time
root. -/
theorem profiledOpenProvenancePolicyDistinguishedTargetRootAt_slot
    (query : Nat → ActiveLineageQuery A initialCode)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none)
    (n : Nat) :
    profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query (n + 1))
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query (n + 1)) lineage =
      some
        (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query lineage hlineage n) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp (hlineage (n + 1)))

/-- The same chosen root in the exact cross-swapped target-side form consumed
by the one-epoch semantic priority bridge. -/
theorem profiledOpenProvenancePolicyDistinguishedTargetRootAt_targetSlot
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none)
    (n : Nat) :
    profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n).other
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query (n + 1)) lineage =
      some
        (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query lineage hlineage n) := by
  rw [← halternates n]
  exact profiledOpenProvenancePolicyDistinguishedTargetRootAt_slot A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query lineage hlineage n

/-- The exact code-only monitor state at positive time `n + 1`, now using the
chosen target-slot root rather than an existential root. -/
theorem profiledOpenProvenancePolicyDistinguished_codeRun_eq_live_targetRoot
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none)
    (n : Nat) :
    codedAlternatingIndexedLineageCodeRun
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query)
        (activeLineageSideAt A initialCode query 0) lineage (n + 1) =
      (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query (n + 1),
        .live (activeLineageSideAt A initialCode query (n + 1)) lineage
          (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy
            hwin basis initialCode codePolicy fixedPolicy point initialRoot
            package query lineage hlineage n)) := by
  obtain ⟨root, hrun, hslot⟩ :=
    profiledOpenProvenancePolicyDistinguished_codeRun_live_of_active_lineage A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates lineage hlineage n
  have hchosen :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_slot A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
        lineage hlineage n
  have hroot : root =
      profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n := by
    apply Option.some.inj
    exact hslot.symm.trans hchosen
  simpa [hroot] using hrun

/-- At positive code time `n + 1`, the monitor priority is exactly the
priority of the unique persistent-lineage target root at stream state
`n + 1`. -/
theorem
    profiledOpenProvenancePolicyDistinguished_codeRunPriority_eq_targetRoot
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none)
    (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query 0)
          (profiledOpenIndexedBiBeliefCurrentSlots A)
          (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query)
          (activeLineageSideAt A initialCode query 0) lineage (n + 1)) =
      profiledOpenIndexedRootPriority A
        (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query lineage hlineage n) := by
  rw [profiledOpenProvenancePolicyDistinguished_codeRun_eq_live_targetRoot A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package query halternates lineage hlineage n]
  rfl

/-- Acceptance of the code word transfers, after the explicit one-state
shift, to min-even parity of the exact positive-time target roots on the
fixed live lineage. -/
theorem profiledOpenProvenancePolicyDistinguished_targetRootParity
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A
        (activeLineageSideAt A initialCode query n)
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query n) lineage ≠ none)
    (haccept :
      (profiledOpenIndexedBiBeliefCodeParityDPA A
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0)).Accepts
        (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query)) :
    NatSeqMinEvenParity (fun n ↦
      profiledOpenIndexedRootPriority A
        (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query lineage hlineage n)) := by
  let priorities := fun k ↦
    (codedAlternatingIndexedLineageCodeThreadSystem
      (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query 0)
      (profiledOpenIndexedBiBeliefCurrentSlots A)
      (profiledOpenIndexedRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun
        (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query)
        (activeLineageSideAt A initialCode query 0) lineage k)
  have hfull : NatSeqMinEvenParity priorities :=
    (profiledOpenIndexedBiBeliefCodeParityDPA_accepts_iff A
      (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query 0)
      (activeLineageCodeWord A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query)).mp haccept
      (activeLineageSideAt A initialCode query 0) lineage
  have hshift : NatSeqMinEvenParity (fun n ↦ priorities (1 + n)) :=
    (natSeqMinEvenParity_shift priorities 1).mpr hfull
  have heq : (fun n ↦ priorities (1 + n)) = fun n ↦
      profiledOpenIndexedRootPriority A
        (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query lineage hlineage n) := by
    funext n
    rw [Nat.add_comm]
    exact
      profiledOpenProvenancePolicyDistinguished_codeRunPriority_eq_targetRoot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates lineage hlineage n
  rw [heq] at hshift
  exact hshift

/-- Root-created accepted stream endpoint for the fixed lineage: the same
lineage has exact target slots, a literally live code run, and a min-even
sequence of target-root priorities. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_targetRootParity
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ∃ lineage,
      ∃ hlineage : ∀ n,
        profiledOpenIndexedBiBeliefCurrentSlots A
          (activeLineageSideAt A initialCode query n)
          (activeLineageCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query n) lineage ≠ none,
        NatSeqMinEvenParity (fun n ↦
          profiledOpenIndexedRootPriority A
            (profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy
              hwin basis initialCode codePolicy fixedPolicy point initialRoot
              package query lineage hlineage n)) := by
  obtain ⟨lineage, hlineage⟩ :=
    exists_profiledOpenProvenancePolicyDistinguished_lineage_active_forever A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates hactive
  refine ⟨lineage, hlineage, ?_⟩
  apply profiledOpenProvenancePolicyDistinguished_targetRootParity A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query halternates lineage hlineage
  have hcode0 :
      activeLineageCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0 = initialCode := by
    change
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1.1 = initialCode
    have hrootCode := congrArg Prod.fst hroot
    rw [profiledOpenIndexedProvenanceCodePolicy_run_nil A strategy hwin basis
      initialCode codePolicy] at hrootCode
    exact hrootCode
  rw [hcode0]
  exact profiledOpenProvenancePolicyDistinguishedStream_accepts A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package hroot
      query

/-- Accepted-stream coupling: under the explicit root equation, the same
finite distinguished recurrence is accepted and carries one fixed active
source/target lineage. -/
theorem profiledOpenProvenancePolicyDistinguished_accepts_and_lineage
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → ActiveLineageQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
        (fun n ↦
          (activeLineageDescriptorAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query (n + 1)
            ).code) ∧
      ∃ lineage,
        (∀ n,
          profiledOpenIndexedBiBeliefCurrentSlots A
            (activeLineageSideAt A initialCode query n)
            (activeLineageDescriptorAt A strategy hwin basis initialCode
              codePolicy fixedPolicy point initialRoot package query n).code
            lineage ≠ none) ∧
        (∀ n,
          profiledOpenIndexedBiBeliefCurrentSlots A
            (activeLineageSideAt A initialCode query n).other
            (activeLineageDescriptorAt A strategy hwin basis initialCode
              codePolicy fixedPolicy point initialRoot package query (n + 1)
              ).code lineage ≠ none) := by
  constructor
  · exact profiledOpenProvenancePolicyDistinguishedStream_accepts A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        hroot query
  · exact
      exists_profiledOpenProvenancePolicyDistinguished_lineage_source_target A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates hactive

end

end DetParityAutomaton

end DistributedSynthesis
