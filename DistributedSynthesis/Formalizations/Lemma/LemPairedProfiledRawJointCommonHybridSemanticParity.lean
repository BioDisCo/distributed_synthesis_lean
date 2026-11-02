/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonHybridSemanticTree
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeLiveness
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Code parity for the common-prefix/one-sided raw tree

The finite monitor sees only tagged child incidence codes.  A common code
exposes both lanes, a one-sided code exposes its surviving lane, and the dead
completion exposes no lane.  A hidden objective thread alternates lanes after
every compressed direction.

There is no separate all-`both` argument.  On every never-dead branch, the
live slot at each positive depth names one literal `PairedStrategyMemory`.
A simultaneous common step and a strict actual step both advance that memory
by one genuine compressed direction.  The original winning strategy therefore
supplies parity through `PairedStrategyMemory.switchingAccepts_of_winning`.

The policy validity used below also retains semantic provenance.  This is
stronger than raw move validity and lets later policy inversion recover the
literal common/one-sided source.  The hidden side remains an objective
coordinate; it is never an observation or leader bit supplied to a process.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-! ## Tagged finite objective -/

/-- The exact live slots visible in a tagged hybrid code. -/
def profiledRawJointHybridCurrentSlots
    (side : IndexedLineageSide) (code : ProfiledRawJointHybridCode A) :
    Unit → Option (ProfiledRawJointThreadRoot A) :=
  match code with
  | .common code => profiledRawJointOneSidedCurrentSlots A side code
  | .oneSided code => profiledRawJointOneSidedCurrentSlots A side code
  | .dead => fun _ => none

/-- Deterministic parity monitor over successive tagged child codes. -/
noncomputable def profiledRawJointHybridCodeParityDPA
    (initialCode : ProfiledRawJointHybridCode A) :
    DetParityAutomaton (ProfiledRawJointHybridCode A) :=
  codedAlternatingIndexedLineageCodeDPA initialCode
    (profiledRawJointHybridCurrentSlots A)
    (profiledRawJointThreadRootPriority A)

/-! ## Source provenance retained by the rational policy -/

/-- A finite move has a literal semantic source of exactly the advertised
tagged code. -/
def ProfiledRawJointHybridProvenanceValid
    (code : ProfiledRawJointHybridCode A)
    (move : ProfiledRawJointHybridMove A) : Prop :=
  ∃ source : ProfiledRawJointHybridSemanticState A strategy,
    source.code A = code ∧ source.move A = move

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The semantic unfolding carries its own provenance witness. -/
theorem ProfiledRawJointHybridSemanticState.provenanceValid
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    ProfiledRawJointHybridProvenanceValid A strategy (state.code A)
      (state.move A) :=
  ⟨state, rfl, rfl⟩

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Under the original winner, provenance implies the ordinary raw validity
law as well. -/
theorem ProfiledRawJointHybridProvenanceValid.moveValid_of_winning
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    {code : ProfiledRawJointHybridCode A}
    {move : ProfiledRawJointHybridMove A}
    (hvalid : ProfiledRawJointHybridProvenanceValid A strategy code move) :
    ProfiledRawJointHybridMoveValid A code move := by
  rcases hvalid with ⟨source, rfl, rfl⟩
  exact source.move_valid_of_winning A hwin

/-! ## Exact positive-depth states and live packages -/

/-- Literal process-one family carried by a live hybrid state. -/
def ProfiledRawJointHybridSemanticState.rightFamily
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    Unit → Option (ProcOnePairedEntryRep strategy × A.State) :=
  match state with
  | .common world => (profiledRawJointCommonWorldFamily A world).right
  | .oneSided state => state.family.right
  | .dead => fun _ => none

/-- Literal process-two family carried by a live hybrid state. -/
def ProfiledRawJointHybridSemanticState.leftFamily
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    Unit → Option (ProcTwoPairedEntryRep strategy × A.State) :=
  match state with
  | .common world => (profiledRawJointCommonWorldFamily A world).left
  | .oneSided state => state.family.left
  | .dead => fun _ => none

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- A tagged right slot is exactly the finite erasure of the literal right
semantic member. -/
theorem ProfiledRawJointHybridSemanticState.currentSlot_right
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    profiledRawJointHybridCurrentSlots A .right (state.code A) () =
      (state.rightFamily A strategy ()).map fun member =>
        Sum.inl (((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)) := by
  cases state <;>
    simp [profiledRawJointHybridCurrentSlots,
      ProfiledRawJointHybridSemanticState.code,
      ProfiledRawJointHybridSemanticState.rightFamily,
      ProfiledRawJointOneSidedSemanticState.code,
      profiledRawJointOneSidedCurrentSlots,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code, Function.comp_def]

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left-slot mirror. -/
theorem ProfiledRawJointHybridSemanticState.currentSlot_left
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    profiledRawJointHybridCurrentSlots A .left (state.code A) () =
      (state.leftFamily A strategy ()).map fun member =>
        Sum.inr (((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)) := by
  cases state <;>
    simp [profiledRawJointHybridCurrentSlots,
      ProfiledRawJointHybridSemanticState.code,
      ProfiledRawJointHybridSemanticState.leftFamily,
      ProfiledRawJointOneSidedSemanticState.code,
      profiledRawJointOneSidedCurrentSlots,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code, Function.comp_def]

/-- Exact semantic state at positive depth `n + 1`. -/
def profiledRawJointHybridPositiveBranchState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) (n : Nat) :=
  (profiledRawJointHybridSemanticTree A initial).stateAt
    (branchNode branch (n + 1))

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Consecutive positive-depth states are literal hybrid steps. -/
theorem profiledRawJointHybridPositiveBranchState_succ
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) (n : Nat) :
    profiledRawJointHybridPositiveBranchState A strategy initial branch
        (n + 1) =
      (profiledRawJointHybridPositiveBranchState A strategy initial branch n
        ).step A (branch (n + 1)) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  change raw.stateAt (branchNode branch (n + 2)) =
    raw.step (raw.stateAt (branchNode branch (n + 1))) (branch (n + 1))
  rw [show branchNode branch (n + 2) =
      branchNode branch (n + 1) ++ [branch (n + 1)] by rfl,
    raw.stateAt_append]

/-- Canonical positive-time live monitor record. -/
noncomputable def profiledRawJointHybridBranchLiveAt
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :=
  codedAlternatingIndexedLineageCodeLiveAtOfNeverDead
    (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
    (profiledRawJointHybridCurrentSlots A)
    ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
    initialSide () hnever n

/-- A live finite slot together with its literal semantic member. -/
inductive ProfiledRawJointHybridBranchMemoryPackage
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) : Type _ where
  | right
      (member : ProcOnePairedEntryRep strategy × A.State)
      (hmember : (profiledRawJointHybridPositiveBranchState A strategy
          initial branch n).rightFamily A strategy () = some member)
      (hroot :
        (profiledRawJointHybridBranchLiveAt A strategy initial branch
          initialSide hnever n).side = .right ∧
        (profiledRawJointHybridBranchLiveAt A strategy initial branch
          initialSide hnever n).root =
          Sum.inl (((member.1.code, member.2),
            rightInitialFirstProfile member.1.lambdaOfStrategy)))
  | left
      (member : ProcTwoPairedEntryRep strategy × A.State)
      (hmember : (profiledRawJointHybridPositiveBranchState A strategy
          initial branch n).leftFamily A strategy () = some member)
      (hroot :
        (profiledRawJointHybridBranchLiveAt A strategy initial branch
          initialSide hnever n).side = .left ∧
        (profiledRawJointHybridBranchLiveAt A strategy initial branch
          initialSide hnever n).root =
          Sum.inr (((member.1.code, member.2),
            leftInitialFirstProfile member.1.lambdaOfStrategy)))

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Every never-dead finite slot is the erasure of one literal semantic
memory, in either the common or one-sided mode. -/
theorem exists_profiledRawJointHybridBranchMemoryPackage
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :
    Nonempty (ProfiledRawJointHybridBranchMemoryPackage A strategy initial
      branch initialSide hnever n) := by
  classical
  let state := profiledRawJointHybridPositiveBranchState A strategy initial
    branch n
  let live := profiledRawJointHybridBranchLiveAt A strategy initial branch
    initialSide hnever n
  have hslot := live.slot
  change profiledRawJointHybridCurrentSlots A live.side (state.code A) () =
    some live.root at hslot
  cases hside : live.side with
  | right =>
      rw [hside] at hslot
      rw [state.currentSlot_right A strategy] at hslot
      cases hmember : state.rightFamily A strategy () with
      | none => simp [hmember] at hslot
      | some member =>
          have hroot : live.root =
              Sum.inl (((member.1.code, member.2),
                rightInitialFirstProfile member.1.lambdaOfStrategy)) := by
            simpa [hmember] using hslot.symm
          exact ⟨ProfiledRawJointHybridBranchMemoryPackage.right member
            hmember ⟨hside, hroot⟩⟩
  | left =>
      rw [hside] at hslot
      rw [state.currentSlot_left A strategy] at hslot
      cases hmember : state.leftFamily A strategy () with
      | none => simp [hmember] at hslot
      | some member =>
          have hroot : live.root =
              Sum.inr (((member.1.code, member.2),
                leftInitialFirstProfile member.1.lambdaOfStrategy)) := by
            simpa [hmember] using hslot.symm
          exact ⟨ProfiledRawJointHybridBranchMemoryPackage.left member
            hmember ⟨hside, hroot⟩⟩

/-- Canonically select the semantic member named at a live slot. -/
noncomputable def profiledRawJointHybridBranchMemoryPackage
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :
    ProfiledRawJointHybridBranchMemoryPackage A strategy initial branch
      initialSide hnever n :=
  Classical.choice (exists_profiledRawJointHybridBranchMemoryPackage A
    strategy initial branch initialSide hnever n)

/-- Literal paired-strategy memory at positive monitor time. -/
noncomputable def profiledRawJointHybridBranchMemory
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) : PairedStrategyMemory A strategy :=
  match profiledRawJointHybridBranchMemoryPackage A strategy initial branch
      initialSide hnever n with
  | .right member _ _ => .processOne member.1 member.2
  | .left member _ _ => .processTwo member.1 member.2

/-! ## Literal memory steps in every live hybrid mode -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- A live right-to-left hybrid transition is one literal process-one memory
step.  This includes a common simultaneous round, a common strict exit, and
an ordinary one-sided strict continuation. -/
theorem exists_profiledRawJointHybrid_right_to_left_memory_step
    (state : ProfiledRawJointHybridSemanticState A strategy)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (source : ProcOnePairedEntryRep strategy × A.State)
    (target : ProcTwoPairedEntryRep strategy × A.State)
    (hsource : state.rightFamily A strategy () = some source)
    (htarget : (state.step A direction).leftFamily A strategy () =
      some target) :
    ∃ actual : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      PairedStrategyMemory.processTwo target.1 target.2 =
        (PairedStrategyMemory.processOne source.1 source.2).step
          (A := A) actual := by
  classical
  cases state with
  | common world =>
      have hsource' : world.procOneMember A = source :=
        Option.some.inj hsource
      subst source
      cases direction with
      | simultaneous input =>
          have htarget' :
              (profiledRawJointCommonWorldAfterBoth A world input
                ).procTwoMember A = target :=
            Option.some.inj htarget
          subst target
          refine ⟨.fromOne .both [] (input.2, input.1), ?_⟩
          exact (profiledRawRightSemanticChildMemory_eq_processTwo A
            (world.procOneMember A) .both [] (input.2, input.1)).symm
      | strict actual =>
          cases hside : actual.side with
          | left =>
              simp [ProfiledRawJointHybridSemanticState.step,
                profiledRawJointCommonExitState,
                profiledRawJointCommonActualDirection, hside,
                ProfiledRawJointHybridSemanticState.leftFamily,
                ProfiledRawJointSemanticFamily.leftActualChild] at htarget
          | right =>
              have hselected :
                  (profiledRawJointCommonWorldFamily A world
                    ).rightSelectedChild A
                      (profiledRawJointCommonActualDirection actual).direction
                      () = some target := by
                simpa [ProfiledRawJointHybridSemanticState.step,
                  profiledRawJointCommonExitState, hside,
                  ProfiledRawJointHybridSemanticState.leftFamily,
                  ProfiledRawJointSemanticFamily.rightActualChild] using
                  htarget
              rcases (profiledRawJointCommonWorldFamily A world
                ).rightSelectedChild_eq_some_source A
                  (profiledRawJointCommonActualDirection actual).direction ()
                  target hselected with
                ⟨old, row, hold, _hpattern, htargetEq⟩
              have holdEq : old = world.procOneMember A :=
                Option.some.inj (hold.symm.trans (by rfl))
              subst old
              subst target
              refine ⟨.fromOne row
                (profiledRawJointCommonActualDirection actual
                  ).direction.rightPhysicalPast
                (profiledRawJointCommonActualDirection actual
                  ).direction.rightInput, ?_⟩
              exact (profiledRawRightSemanticChildMemory_eq_processTwo A
                (world.procOneMember A) row
                (profiledRawJointCommonActualDirection actual
                  ).direction.rightPhysicalPast
                (profiledRawJointCommonActualDirection actual
                  ).direction.rightInput).symm
  | oneSided oldState =>
      cases direction with
      | simultaneous input =>
          simp [ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointHybridSemanticState.leftFamily] at htarget
      | strict actual =>
          cases hside : actual.side with
          | left =>
              simp [ProfiledRawJointHybridSemanticState.step,
                ProfiledRawJointOneSidedSemanticState.step, hside,
                ProfiledRawJointHybridSemanticState.leftFamily,
                ProfiledRawJointSemanticFamily.leftActualChild] at htarget
          | right =>
              have hselected : oldState.family.rightSelectedChild A
                  actual.direction () = some target := by
                simpa [ProfiledRawJointHybridSemanticState.step,
                  ProfiledRawJointOneSidedSemanticState.step, hside,
                  ProfiledRawJointHybridSemanticState.leftFamily,
                  ProfiledRawJointSemanticFamily.rightActualChild] using
                  htarget
              rcases oldState.family.rightSelectedChild_eq_some_source A
                  actual.direction () target hselected with
                ⟨old, row, hold, _hpattern, htargetEq⟩
              have holdEq : old = source :=
                Option.some.inj (hold.symm.trans hsource)
              subst old
              subst target
              refine ⟨.fromOne row actual.direction.rightPhysicalPast
                actual.direction.rightInput, ?_⟩
              exact (profiledRawRightSemanticChildMemory_eq_processTwo A
                source row actual.direction.rightPhysicalPast
                actual.direction.rightInput).symm
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.rightFamily] at hsource

/-- Left-to-right mirror. -/
theorem exists_profiledRawJointHybrid_left_to_right_memory_step
    (state : ProfiledRawJointHybridSemanticState A strategy)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (source : ProcTwoPairedEntryRep strategy × A.State)
    (target : ProcOnePairedEntryRep strategy × A.State)
    (hsource : state.leftFamily A strategy () = some source)
    (htarget : (state.step A direction).rightFamily A strategy () =
      some target) :
    ∃ actual : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      PairedStrategyMemory.processOne target.1 target.2 =
        (PairedStrategyMemory.processTwo source.1 source.2).step
          (A := A) actual := by
  classical
  cases state with
  | common world =>
      have hsource' : world.procTwoMember A = source :=
        Option.some.inj hsource
      subst source
      cases direction with
      | simultaneous input =>
          have htarget' :
              (profiledRawJointCommonWorldAfterBoth A world input
                ).procOneMember A = target :=
            Option.some.inj htarget
          subst target
          refine ⟨.fromTwo .both [] input, ?_⟩
          rw [profiledRawJointCommonWorldAfterBoth_eq_left A world input]
          exact (profiledRawLeftSemanticChildMemory_eq_processOne A
            (world.procTwoMember A) .both [] input).symm
      | strict actual =>
          cases hside : actual.side with
          | right =>
              simp [ProfiledRawJointHybridSemanticState.step,
                profiledRawJointCommonExitState,
                profiledRawJointCommonActualDirection, hside,
                ProfiledRawJointHybridSemanticState.rightFamily,
                ProfiledRawJointSemanticFamily.rightActualChild] at htarget
          | left =>
              have hselected :
                  (profiledRawJointCommonWorldFamily A world
                    ).leftSelectedChild A
                      (profiledRawJointCommonActualDirection actual).direction
                      () = some target := by
                simpa [ProfiledRawJointHybridSemanticState.step,
                  profiledRawJointCommonExitState, hside,
                  ProfiledRawJointHybridSemanticState.rightFamily,
                  ProfiledRawJointSemanticFamily.leftActualChild] using
                  htarget
              rcases (profiledRawJointCommonWorldFamily A world
                ).leftSelectedChild_eq_some_source A
                  (profiledRawJointCommonActualDirection actual).direction ()
                  target hselected with
                ⟨old, row, hold, _hpattern, htargetEq⟩
              have holdEq : old = world.procTwoMember A :=
                Option.some.inj (hold.symm.trans (by rfl))
              subst old
              subst target
              refine ⟨.fromTwo row
                (profiledRawJointCommonActualDirection actual
                  ).direction.leftPhysicalPast
                (profiledRawJointCommonActualDirection actual
                  ).direction.leftInput, ?_⟩
              exact (profiledRawLeftSemanticChildMemory_eq_processOne A
                (world.procTwoMember A) row
                (profiledRawJointCommonActualDirection actual
                  ).direction.leftPhysicalPast
                (profiledRawJointCommonActualDirection actual
                  ).direction.leftInput).symm
  | oneSided oldState =>
      cases direction with
      | simultaneous input =>
          simp [ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointHybridSemanticState.rightFamily] at htarget
      | strict actual =>
          cases hside : actual.side with
          | right =>
              simp [ProfiledRawJointHybridSemanticState.step,
                ProfiledRawJointOneSidedSemanticState.step, hside,
                ProfiledRawJointHybridSemanticState.rightFamily,
                ProfiledRawJointSemanticFamily.rightActualChild] at htarget
          | left =>
              have hselected : oldState.family.leftSelectedChild A
                  actual.direction () = some target := by
                simpa [ProfiledRawJointHybridSemanticState.step,
                  ProfiledRawJointOneSidedSemanticState.step, hside,
                  ProfiledRawJointHybridSemanticState.rightFamily,
                  ProfiledRawJointSemanticFamily.leftActualChild] using
                  htarget
              rcases oldState.family.leftSelectedChild_eq_some_source A
                  actual.direction () target hselected with
                ⟨old, row, hold, _hpattern, htargetEq⟩
              have holdEq : old = source :=
                Option.some.inj (hold.symm.trans hsource)
              subst old
              subst target
              refine ⟨.fromTwo row actual.direction.leftPhysicalPast
                actual.direction.leftInput, ?_⟩
              exact (profiledRawLeftSemanticChildMemory_eq_processOne A
                source row actual.direction.leftPhysicalPast
                actual.direction.leftInput).symm
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.leftFamily] at hsource

/-- Consecutive never-dead packages are related by one genuine compressed
memory step. -/
theorem exists_profiledRawJointHybridBranchMemory_step
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :
    ∃ actual : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      profiledRawJointHybridBranchMemory A strategy initial branch initialSide
          hnever (n + 1) =
        (profiledRawJointHybridBranchMemory A strategy initial branch
          initialSide hnever n).step (A := A) actual := by
  classical
  have hflip :=
    codedAlternatingIndexedLineageCodeLiveAtOfNeverDead_side_succ
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      (profiledRawJointHybridCurrentSlots A)
      ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
      initialSide () hnever n
  change
    (profiledRawJointHybridBranchLiveAt A strategy initial branch initialSide
      hnever (n + 1)).side =
      (profiledRawJointHybridBranchLiveAt A strategy initial branch initialSide
        hnever n).side.other at hflip
  let pState := profiledRawJointHybridPositiveBranchState A strategy initial
    branch n
  let qState := profiledRawJointHybridPositiveBranchState A strategy initial
    branch (n + 1)
  have hstate : qState = pState.step A (branch (n + 1)) :=
    profiledRawJointHybridPositiveBranchState_succ A strategy initial branch n
  cases hpkg : profiledRawJointHybridBranchMemoryPackage A strategy initial
      branch initialSide hnever n with
  | right pMember hpMember hpRoot =>
      rcases hpRoot with ⟨hpSide, hpRoot⟩
      change pState.rightFamily A strategy () = some pMember at hpMember
      cases qpkg : profiledRawJointHybridBranchMemoryPackage A strategy initial
          branch initialSide hnever (n + 1) with
      | right qMember hqMember hqRoot =>
          rcases hqRoot with ⟨hqSide, hqRoot⟩
          rw [hpSide, hqSide] at hflip
          cases hflip
      | left qMember hqMember hqRoot =>
          change qState.leftFamily A strategy () = some qMember at hqMember
          rw [hstate] at hqMember
          rcases exists_profiledRawJointHybrid_right_to_left_memory_step A
              strategy pState (branch (n + 1)) pMember qMember hpMember
              hqMember with ⟨actual, hmemory⟩
          refine ⟨actual, ?_⟩
          simpa only [profiledRawJointHybridBranchMemory, hpkg, qpkg] using
            hmemory
  | left pMember hpMember hpRoot =>
      rcases hpRoot with ⟨hpSide, hpRoot⟩
      change pState.leftFamily A strategy () = some pMember at hpMember
      cases qpkg : profiledRawJointHybridBranchMemoryPackage A strategy initial
          branch initialSide hnever (n + 1) with
      | left qMember hqMember hqRoot =>
          rcases hqRoot with ⟨hqSide, hqRoot⟩
          rw [hpSide, hqSide] at hflip
          cases hflip
      | right qMember hqMember hqRoot =>
          change qState.rightFamily A strategy () = some qMember at hqMember
          rw [hstate] at hqMember
          rcases exists_profiledRawJointHybrid_left_to_right_memory_step A
              strategy pState (branch (n + 1)) pMember qMember hpMember
              hqMember with ⟨actual, hmemory⟩
          refine ⟨actual, ?_⟩
          simpa only [profiledRawJointHybridBranchMemory, hpkg, qpkg] using
            hmemory

end

/-- Canonically chosen compressed direction between adjacent packages. -/
noncomputable def profiledRawJointHybridBranchMemoryDirection
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
  Classical.choose (exists_profiledRawJointHybridBranchMemory_step A strategy
    initial branch initialSide hnever n)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Specification of the chosen compressed direction. -/
theorem profiledRawJointHybridBranchMemory_step
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :
    profiledRawJointHybridBranchMemory A strategy initial branch initialSide
        hnever (n + 1) =
      (profiledRawJointHybridBranchMemory A strategy initial branch initialSide
        hnever n).step (A := A)
        (profiledRawJointHybridBranchMemoryDirection A strategy initial branch
          initialSide hnever n) :=
  Classical.choose_spec
    (exists_profiledRawJointHybridBranchMemory_step A strategy initial branch
      initialSide hnever n)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The selected memory is exactly the operational fold of the recovered
compressed directions. -/
theorem profiledRawJointHybridBranchMemory_eq_atNode
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :
    profiledRawJointHybridBranchMemory A strategy initial branch initialSide
        hnever n =
      PairedStrategyMemory.atNode (A := A)
        (profiledRawJointHybridBranchMemory A strategy initial branch
          initialSide hnever 0)
        (branchNode (profiledRawJointHybridBranchMemoryDirection A strategy
          initial branch initialSide hnever) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointHybridBranchMemory_step A strategy initial branch
        initialSide hnever n, ih]
      rw [show branchNode
          (profiledRawJointHybridBranchMemoryDirection A strategy initial
            branch initialSide hnever) (n + 1) =
        branchNode
            (profiledRawJointHybridBranchMemoryDirection A strategy initial
              branch initialSide hnever) n ++
          [profiledRawJointHybridBranchMemoryDirection A strategy initial
            branch initialSide hnever n] by rfl,
        PairedStrategyMemory.atNode_append]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At positive monitor time, the code priority is exactly the priority of
the literal memory named by the live slot. -/
theorem profiledRawJointHybridBranch_live_priority
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead)
    (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)) =
      pairedEntryPriority A
        (profiledRawJointHybridBranchMemory A strategy initial branch
          initialSide hnever n).toTreeState := by
  let live := profiledRawJointHybridBranchLiveAt A strategy initial branch
    initialSide hnever n
  rw [live.run_eq]
  change profiledRawJointThreadRootPriority A live.root = _
  cases hpkg : profiledRawJointHybridBranchMemoryPackage A strategy initial
      branch initialSide hnever n with
  | right member hmember hroot =>
      rcases hroot with ⟨hside, hroot⟩
      simp only [profiledRawJointHybridBranchMemory, hpkg]
      rw [hroot]
      rfl
  | left member hmember hroot =>
      rcases hroot with ⟨hside, hroot⟩
      simp only [profiledRawJointHybridBranchMemory, hpkg]
      rw [hroot]
      rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Every never-dead hybrid lineage has min-even parity. -/
theorem profiledRawJointHybridBranchMemory_minEven
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (profiledRawJointHybridCurrentSlots A)
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord branch)
        initialSide () (n + 1)).2 ≠ .dead) :
    NatSeqMinEvenParity (fun n =>
      pairedEntryPriority A
        (profiledRawJointHybridBranchMemory A strategy initial branch
          initialSide hnever n).toTreeState) := by
  let memory := profiledRawJointHybridBranchMemory A strategy initial branch
    initialSide hnever
  let directions := profiledRawJointHybridBranchMemoryDirection A strategy
    initial branch initialSide hnever
  have hparity := PairedStrategyMemory.switchingAccepts_of_winning
    (A := A) hwin (memory 0) directions
  convert hparity using 1
  funext n
  change pairedEntryPriority A (memory n).toTreeState = _
  have hmemory : memory n = PairedStrategyMemory.atNode (A := A) (memory 0)
      (branchNode directions n) :=
    profiledRawJointHybridBranchMemory_eq_atNode A strategy initial branch
      initialSide hnever n
  rw [hmemory]
  rfl

/-! ## Unconditional hybrid acceptance and certificate -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Every branch of the common-prefix/one-sided semantic tree is accepted by
the finite tagged-code objective.  Forever-simultaneous branches are covered
by the same literal-memory argument as branches that eventually exit. -/
theorem profiledRawJointHybridSemanticTree_accepts
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (branch : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      ).Accepts
        ((profiledRawJointHybridSemanticTree A initial).childCodeWord
          branch) := by
  classical
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let word :=
    (profiledRawJointHybridSemanticTree A initial).childCodeWord branch
  rw [profiledRawJointHybridCodeParityDPA,
    codedAlternatingIndexedLineageCodeDPA_accepts_iff]
  intro initialSide lineage
  by_cases hdead : ∃ n,
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A) word initialSide lineage n).2 =
          .dead
  · rcases hdead with ⟨n, hdead⟩
    have hparity := codedAlternatingIndexedLineageRun_minEven_of_eventually_dead
      initialCode
      (fun _ (_ : Unit) childCode => childCode)
      (profiledRawJointHybridCurrentSlots A)
      (codedAlternatingIndexedLineageCodeChild
        (profiledRawJointHybridCurrentSlots A))
      (profiledRawJointThreadRootPriority A)
      (fun k => (Unit.unit, word k)) initialSide lineage hdead
    simpa [codedAlternatingIndexedLineageCodeThreadSystem,
      codedAlternatingIndexedLineageCodeRun] using hparity
  · have hnever : ∀ n,
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointHybridCurrentSlots A) word initialSide lineage
          (n + 1)).2 ≠ .dead := by
      intro n hnow
      exact hdead ⟨n + 1, hnow⟩
    cases lineage
    let priorities := fun n =>
      (codedAlternatingIndexedLineageCodeThreadSystem initialCode
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointHybridCurrentSlots A) word initialSide () n)
    have hsemantic := profiledRawJointHybridBranchMemory_minEven A strategy
      hwin initial branch initialSide hnever
    have htail : NatSeqMinEvenParity (fun n => priorities (1 + n)) := by
      convert hsemantic using 1
      funext n
      simpa [priorities, word, initialCode, Nat.add_comm] using
        profiledRawJointHybridBranch_live_priority A strategy initial branch
          initialSide hnever n
    exact (natSeqMinEvenParity_shift priorities 1).mp htail

/-- Complete source-free code-parity certificate with semantic provenance in
the transition predicate. -/
theorem profiledRawJointHybridSemanticTree_codeParityCertificate
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    let raw := profiledRawJointHybridSemanticTree A initial
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointHybridCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridNext A)
      raw := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact (raw.stateAt node).provenanceValid A strategy
  · intro node direction
    exact profiledRawJointHybridSemanticTree_next_code A initial node direction
  · intro branch
    exact profiledRawJointHybridSemanticTree_accepts A strategy hwin initial
      branch

/-- One named input-free basis call yields the finite provenance-retaining
hybrid policy. -/
theorem nonempty_profiledRawJointHybridCodeParityRationalPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (basis :
      (sourceFreeBeliefCodeParityRunAutomaton
        (profiledRawJointHybridCodeParityDPA A
          (.common ((profiledRawJointCommonWorldFamily A initial
            ).incidenceCode A)))
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (profiledRawJointHybridNext A)).RationalRunBasis) :
    Nonempty (SourceFreeBeliefCodeParityRationalPolicy
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridNext A)) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
    (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    raw
    (profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial)
    basis

end

end

end DetParityAutomaton

end DistributedSynthesis
