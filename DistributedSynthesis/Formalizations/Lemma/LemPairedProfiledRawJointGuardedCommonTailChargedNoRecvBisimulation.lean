/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailChargedShadowNoRecv
import DistributedSynthesis.Formalizations.Lemma.LemPendingBitResolution

/-!
# A finite one-bit bisimulation carrier for charged non-receives

Unfolding the two honest interpretations of a charged cross shadow does not
make their finite rational-controller states definitionally equal.  The
correct graph-blind closure is instead a two-candidate no-receive
bisimulation.  Its candidate family is indexed by one `Bool`; one local
non-receive advances both candidates pointwise, emits their common output,
and preserves the same all-future-no-receive compatibility invariant.

Consequently the old ambiguity is *replaced*, never multiplied: the successor
still has a `Bool → OldControl` interpretation map, not a
`Bool × Bool → OldControl` map.  At the next receive the delivered partner
control can resolve this old bit before the current round installs a fresh
one, exactly as proved semantically by `LemPendingBitResolution`.

The last section names the sole model-facing input.  An overlap realization
identifies, at every finite no-receive suffix, the two controller outputs with
two original-strategy histories satisfying `ProcOnePendingOverlap` (or its
mirror).  The pending-bit theorem then derives the entire bisimulation
compatibility law.  Thus this module separates the finite executable closure
from the remaining rational-controller-to-history trace alignment.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev OldOne :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)

private abbrev OldTwo :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)

private abbrev RightShadow :=
  ProfiledRawJointGuardedCommonTailRightChargedCrossShadow A strategy hwin

private abbrev LeftShadow :=
  ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow A strategy hwin

private noncomputable def oldKernel (root : CommonControl A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank root

/-! ## Iterating the old graph-blind local maps -/

/-- Old process-one control after a finite own-input-only suffix. -/
noncomputable def profiledRawJointGuardedCommonTailOldNoRecvOneAdvance
    (root : CommonControl A strategy hwin)
    (control : OldOne A strategy hwin initialBank) (past : List In₁) :
    OldOne A strategy hwin initialBank :=
  past.foldl
    (fun state input ↦
      ((oldKernel A strategy hwin initialBank root).noRecvOne state input).2)
    control

/-- Process-two mirror. -/
noncomputable def profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance
    (root : CommonControl A strategy hwin)
    (control : OldTwo A strategy hwin initialBank) (past : List In₂) :
    OldTwo A strategy hwin initialBank :=
  past.foldl
    (fun state input ↦
      ((oldKernel A strategy hwin initialBank root).noRecvTwo state input).2)
    control

@[simp] theorem profiledRawJointGuardedCommonTailOldNoRecvOneAdvance_nil
    (root : CommonControl A strategy hwin)
    (control : OldOne A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
        initialBank root control [] = control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance_nil
    (root : CommonControl A strategy hwin)
    (control : OldTwo A strategy hwin initialBank) :
    profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
        initialBank root control [] = control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailOldNoRecvOneAdvance_cons
    (root : CommonControl A strategy hwin)
    (control : OldOne A strategy hwin initialBank) (input : In₁)
    (past : List In₁) :
    profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
        initialBank root control (input :: past) =
      profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
        initialBank root
        ((oldKernel A strategy hwin initialBank root).noRecvOne control
          input).2 past :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance_cons
    (root : CommonControl A strategy hwin)
    (control : OldTwo A strategy hwin initialBank) (input : In₂)
    (past : List In₂) :
    profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
        initialBank root control (input :: past) =
      profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
        initialBank root
        ((oldKernel A strategy hwin initialBank root).noRecvTwo control
          input).2 past :=
  rfl

/-! ## The all-future compatibility relations -/

/-- The two process-one interpretations emit the same output after every
finite no-receive suffix and on every next own input. -/
def ProfiledRawJointGuardedCommonTailNoRecvOneCompatible
    (root : CommonControl A strategy hwin)
    (candidate : Bool → OldOne A strategy hwin initialBank) : Prop :=
  ∀ (past : List In₁) (input : In₁),
    ((oldKernel A strategy hwin initialBank root).noRecvOne
      (profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
        initialBank root (candidate false) past) input).1 =
    ((oldKernel A strategy hwin initialBank root).noRecvOne
      (profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
        initialBank root (candidate true) past) input).1

/-- Process-two mirror. -/
def ProfiledRawJointGuardedCommonTailNoRecvTwoCompatible
    (root : CommonControl A strategy hwin)
    (candidate : Bool → OldTwo A strategy hwin initialBank) : Prop :=
  ∀ (past : List In₂) (input : In₂),
    ((oldKernel A strategy hwin initialBank root).noRecvTwo
      (profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
        initialBank root (candidate false) past) input).1 =
    ((oldKernel A strategy hwin initialBank root).noRecvTwo
      (profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
        initialBank root (candidate true) past) input).1

/-! ## Finite one-bit replacement states -/

structure ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation where
  root : CommonControl A strategy hwin
  candidate : Bool → OldOne A strategy hwin initialBank
  compatible : ProfiledRawJointGuardedCommonTailNoRecvOneCompatible A strategy
    hwin initialBank root candidate

structure ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation where
  root : CommonControl A strategy hwin
  candidate : Bool → OldTwo A strategy hwin initialBank
  compatible : ProfiledRawJointGuardedCommonTailNoRecvTwoCompatible A strategy
    hwin initialBank root candidate

noncomputable instance
    profiledRawJointGuardedCommonTailChargedNoRecvOneBisimulationFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank) := by
  classical
  let encode := fun state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank ↦ (state.root, state.candidate)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

noncomputable instance
    profiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulationFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank) := by
  classical
  let encode := fun state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank ↦ (state.root, state.candidate)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

namespace ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation

/-- Graph-blind local update.  The false candidate selects the output; the
compatibility proof below shows that either honest interpretation emits it. -/
noncomputable def step
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank)
    (input : In₁) : Out₁ ×
      ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank :=
  let table := fun bit ↦
    (oldKernel A strategy hwin initialBank state.root).noRecvOne
      (state.candidate bit) input
  ( (table false).1,
    { root := state.root
      candidate := fun bit ↦ (table bit).2
      compatible := by
        intro past nextInput
        exact state.compatible (input :: past) nextInput } )

/-- Either old interpretation emits the unique executable output. -/
theorem step_output_eq_candidate
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank)
    (input : In₁) (bit : Bool) :
    (state.step A strategy hwin initialBank input).1 =
      ((oldKernel A strategy hwin initialBank state.root).noRecvOne
        (state.candidate bit) input).1 := by
  cases bit with
  | false => rfl
  | true =>
      exact state.compatible [] input

/-- The successor interpretation is pointwise the old candidate's honest
non-receive successor. -/
@[simp] theorem step_candidate
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank)
    (input : In₁) (bit : Bool) :
    (state.step A strategy hwin initialBank input).2.candidate bit =
      ((oldKernel A strategy hwin initialBank state.root).noRecvOne
        (state.candidate bit) input).2 :=
  rfl

/-- No second ambiguity coordinate is introduced: successor meanings are
still the image of the same single Boolean index. -/
theorem step_exists_old_candidate
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank)
    (input : In₁)
    (control : OldOne A strategy hwin initialBank)
    (hcontrol : ∃ bit,
      control = (state.step A strategy hwin initialBank input).2.candidate bit) :
    ∃ bit,
      control =
        ((oldKernel A strategy hwin initialBank state.root).noRecvOne
          (state.candidate bit) input).2 := by
  rcases hcontrol with ⟨bit, rfl⟩
  exact ⟨bit, (step_candidate A strategy hwin initialBank state input bit).symm⟩

end ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation

namespace ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation

noncomputable def step
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank)
    (input : In₂) : Out₂ ×
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank :=
  let table := fun bit ↦
    (oldKernel A strategy hwin initialBank state.root).noRecvTwo
      (state.candidate bit) input
  ( (table false).1,
    { root := state.root
      candidate := fun bit ↦ (table bit).2
      compatible := by
        intro past nextInput
        exact state.compatible (input :: past) nextInput } )

theorem step_output_eq_candidate
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank)
    (input : In₂) (bit : Bool) :
    (state.step A strategy hwin initialBank input).1 =
      ((oldKernel A strategy hwin initialBank state.root).noRecvTwo
        (state.candidate bit) input).1 := by
  cases bit with
  | false => rfl
  | true =>
      exact state.compatible [] input

@[simp] theorem step_candidate
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank)
    (input : In₂) (bit : Bool) :
    (state.step A strategy hwin initialBank input).2.candidate bit =
      ((oldKernel A strategy hwin initialBank state.root).noRecvTwo
        (state.candidate bit) input).2 :=
  rfl

theorem step_exists_old_candidate
    (state :
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank)
    (input : In₂)
    (control : OldTwo A strategy hwin initialBank)
    (hcontrol : ∃ bit,
      control = (state.step A strategy hwin initialBank input).2.candidate bit) :
    ∃ bit,
      control =
        ((oldKernel A strategy hwin initialBank state.root).noRecvTwo
          (state.candidate bit) input).2 := by
  rcases hcontrol with ⟨bit, rfl⟩
  exact ⟨bit, (step_candidate A strategy hwin initialBank state input bit).symm⟩

end ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation

/-! ## The exact semantic trace invariant which supplies compatibility -/

/-- Pointwise semantic realization of the process-one candidate table.  The
two histories may vary with the finite no-receive suffix; only their pending
overlap and their literal controller-output readback matter. -/
def ProfiledRawJointGuardedCommonTailNoRecvOneOverlapRealization
    (root : CommonControl A strategy hwin)
    (candidate : Bool → OldOne A strategy hwin initialBank) : Prop :=
  ∀ (past : List In₁) (input : In₁),
    ∃ historyFalse historyTrue :
        History In₁ In₂ Graph Out₁ Out₂,
      ProcOnePendingOverlap historyFalse historyTrue ∧
      ((oldKernel A strategy hwin initialBank root).noRecvOne
        (profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
          initialBank root (candidate false) past) input).1 =
        strategy.one (currentView Proc.one historyFalse) ∧
      ((oldKernel A strategy hwin initialBank root).noRecvOne
        (profiledRawJointGuardedCommonTailOldNoRecvOneAdvance A strategy hwin
          initialBank root (candidate true) past) input).1 =
        strategy.one (currentView Proc.one historyTrue)

/-- Process-two mirror. -/
def ProfiledRawJointGuardedCommonTailNoRecvTwoOverlapRealization
    (root : CommonControl A strategy hwin)
    (candidate : Bool → OldTwo A strategy hwin initialBank) : Prop :=
  ∀ (past : List In₂) (input : In₂),
    ∃ historyFalse historyTrue :
        History In₁ In₂ Graph Out₁ Out₂,
      ProcTwoPendingOverlap historyFalse historyTrue ∧
      ((oldKernel A strategy hwin initialBank root).noRecvTwo
        (profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
          initialBank root (candidate false) past) input).1 =
        strategy.two (currentView Proc.two historyFalse) ∧
      ((oldKernel A strategy hwin initialBank root).noRecvTwo
        (profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance A strategy hwin
          initialBank root (candidate true) past) input).1 =
        strategy.two (currentView Proc.two historyTrue)

/-- `LemPendingBitResolution` turns semantic overlap realization into the
complete all-future process-one no-receive compatibility law. -/
theorem profiledRawJointGuardedCommonTailNoRecvOneCompatible_of_overlap
    {root : CommonControl A strategy hwin}
    {candidate : Bool → OldOne A strategy hwin initialBank}
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvOneOverlapRealization A strategy
        hwin initialBank root candidate) :
    ProfiledRawJointGuardedCommonTailNoRecvOneCompatible A strategy hwin
      initialBank root candidate := by
  intro past input
  rcases realizes past input with
    ⟨historyFalse, historyTrue, hoverlap, hfalse, htrue⟩
  rw [hfalse, htrue]
  exact hoverlap.strategy_output_eq strategy

/-- Mirror. -/
theorem profiledRawJointGuardedCommonTailNoRecvTwoCompatible_of_overlap
    {root : CommonControl A strategy hwin}
    {candidate : Bool → OldTwo A strategy hwin initialBank}
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvTwoOverlapRealization A strategy
        hwin initialBank root candidate) :
    ProfiledRawJointGuardedCommonTailNoRecvTwoCompatible A strategy hwin
      initialBank root candidate := by
  intro past input
  rcases realizes past input with
    ⟨historyFalse, historyTrue, hoverlap, hfalse, htrue⟩
  rw [hfalse, htrue]
  exact hoverlap.strategy_output_eq strategy

/-! ## A transition-equality shortcut

If the two initial interpretations have equal complete non-receive results
for every input, then the all-future compatibility condition follows without
constructing semantic histories.  After the first input of a nonempty suffix
the two old controls are literally equal, so every later fold is shared. -/

theorem profiledRawJointGuardedCommonTailNoRecvOneCompatible_of_step_eq
    {root : CommonControl A strategy hwin}
    {candidate : Bool → OldOne A strategy hwin initialBank}
    (hstep : ∀ input : In₁,
      (oldKernel A strategy hwin initialBank root).noRecvOne
          (candidate false) input =
        (oldKernel A strategy hwin initialBank root).noRecvOne
          (candidate true) input) :
    ProfiledRawJointGuardedCommonTailNoRecvOneCompatible A strategy hwin
      initialBank root candidate := by
  intro past input
  cases past with
  | nil =>
      exact congrArg Prod.fst (hstep input)
  | cons first rest =>
      simp only [profiledRawJointGuardedCommonTailOldNoRecvOneAdvance_cons]
      rw [hstep first]

/-- Process-two mirror of the transition-equality shortcut. -/
theorem profiledRawJointGuardedCommonTailNoRecvTwoCompatible_of_step_eq
    {root : CommonControl A strategy hwin}
    {candidate : Bool → OldTwo A strategy hwin initialBank}
    (hstep : ∀ input : In₂,
      (oldKernel A strategy hwin initialBank root).noRecvTwo
          (candidate false) input =
        (oldKernel A strategy hwin initialBank root).noRecvTwo
          (candidate true) input) :
    ProfiledRawJointGuardedCommonTailNoRecvTwoCompatible A strategy hwin
      initialBank root candidate := by
  intro past input
  cases past with
  | nil =>
      exact congrArg Prod.fst (hstep input)
  | cons first rest =>
      simp only [profiledRawJointGuardedCommonTailOldNoRecvTwoAdvance_cons]
      rw [hstep first]

/-! ## The two easy charged coordinates collapse after one step -/

/-- On the process-two coordinate of a right-charged shadow, the strict and
closed interpretations install the same staged left owner.  This is stronger
than output compatibility: the whole old transition result is equal. -/
theorem
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.noRecvTwo_candidates_eq
    (state : RightShadow A strategy hwin) (input : In₂) :
    (oldKernel A strategy hwin initialBank state.pending.receiver.control
        ).noRecvTwo (state.twoCandidate A strategy hwin initialBank false)
          input =
      (oldKernel A strategy hwin initialBank state.pending.receiver.control
        ).noRecvTwo (state.twoCandidate A strategy hwin initialBank true)
          input := by
  exact state.noRecvTwo_eq A strategy hwin initialBank input

/-- Left mirror: process one installs the same staged right owner under both
interpretations. -/
theorem
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.noRecvOne_candidates_eq
    (state : LeftShadow A strategy hwin) (input : In₁) :
    (oldKernel A strategy hwin initialBank state.pending.receiver.control
        ).noRecvOne (state.oneCandidate A strategy hwin initialBank false)
          input =
      (oldKernel A strategy hwin initialBank state.pending.receiver.control
        ).noRecvOne (state.oneCandidate A strategy hwin initialBank true)
          input := by
  exact state.noRecvOne_eq A strategy hwin initialBank input

/-- The process-two coordinate of a right charged shadow therefore supplies
its bisimulation state with no model-facing realization hypothesis. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoBisimulationDirect
    (state : RightShadow A strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
      hwin initialBank where
  root := state.pending.receiver.control
  candidate := state.twoCandidate A strategy hwin initialBank
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvTwoCompatible_of_step_eq A strategy
      hwin initialBank fun input ↦
        state.noRecvTwo_candidates_eq A strategy hwin initialBank input

/-- The process-one coordinate of a left charged shadow is the symmetric
directly closed bisimulation state. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneBisimulationDirect
    (state : LeftShadow A strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
      hwin initialBank where
  root := state.pending.receiver.control
  candidate := state.oneCandidate A strategy hwin initialBank
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvOneCompatible_of_step_eq A strategy
      hwin initialBank fun input ↦
        state.noRecvOne_candidates_eq A strategy hwin initialBank input

/-! ## Instantiation sockets for the four original charged shadows -/

noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.oneBisimulation
    (state : RightShadow A strategy hwin)
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvOneOverlapRealization A strategy
        hwin initialBank state.pending.receiver.control
        (state.oneCandidate A strategy hwin initialBank)) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
      hwin initialBank where
  root := state.pending.receiver.control
  candidate := state.oneCandidate A strategy hwin initialBank
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvOneCompatible_of_overlap A strategy
      hwin initialBank realizes

noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.twoBisimulation
    (state : RightShadow A strategy hwin)
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvTwoOverlapRealization A strategy
        hwin initialBank state.pending.receiver.control
        (state.twoCandidate A strategy hwin initialBank)) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
      hwin initialBank where
  root := state.pending.receiver.control
  candidate := state.twoCandidate A strategy hwin initialBank
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvTwoCompatible_of_overlap A strategy
      hwin initialBank realizes

noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.oneBisimulation
    (state : LeftShadow A strategy hwin)
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvOneOverlapRealization A strategy
        hwin initialBank state.pending.receiver.control
        (state.oneCandidate A strategy hwin initialBank)) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
      hwin initialBank where
  root := state.pending.receiver.control
  candidate := state.oneCandidate A strategy hwin initialBank
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvOneCompatible_of_overlap A strategy
      hwin initialBank realizes

noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.twoBisimulation
    (state : LeftShadow A strategy hwin)
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvTwoOverlapRealization A strategy
        hwin initialBank state.pending.receiver.control
        (state.twoCandidate A strategy hwin initialBank)) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
      hwin initialBank where
  root := state.pending.receiver.control
  candidate := state.twoCandidate A strategy hwin initialBank
  compatible :=
    profiledRawJointGuardedCommonTailNoRecvTwoCompatible_of_overlap A strategy
      hwin initialBank realizes

/-! ## The exact two-field charged coherence boundary -/

/-- All model-facing output coherence needed by the charged cross carrier.

The two omitted coordinates are not assumptions: right/process-two and
left/process-one collapse after one old transition and are discharged by
`twoBisimulationDirect` and `oneBisimulationDirect`, respectively.  Keeping
only these two genuinely non-definitional fields prevents downstream
controller code from accidentally asking for four independent overlap
realizations. -/
structure ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations :
    Prop where
  rightOne : ∀ state : RightShadow A strategy hwin,
    ProfiledRawJointGuardedCommonTailNoRecvOneOverlapRealization A strategy
      hwin initialBank state.pending.receiver.control
        (state.oneCandidate A strategy hwin initialBank)
  leftTwo : ∀ state : LeftShadow A strategy hwin,
    ProfiledRawJointGuardedCommonTailNoRecvTwoOverlapRealization A strategy
      hwin initialBank state.pending.receiver.control
        (state.twoCandidate A strategy hwin initialBank)

/-- The right-charged shadow supplies both executable no-receive
bisimulations from only its genuinely difficult process-one realization. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailRightChargedCrossShadow.bisimulations
    (state : RightShadow A strategy hwin)
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvOneOverlapRealization A strategy
        hwin initialBank state.pending.receiver.control
          (state.oneCandidate A strategy hwin initialBank)) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank ×
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank :=
  (state.oneBisimulation A strategy hwin initialBank realizes,
    state.twoBisimulationDirect A strategy hwin initialBank)

/-- Left mirror: the directly collapsing process-one coordinate and the one
genuinely difficult process-two realization give the complete pair. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailLeftChargedCrossShadow.bisimulations
    (state : LeftShadow A strategy hwin)
    (realizes :
      ProfiledRawJointGuardedCommonTailNoRecvTwoOverlapRealization A strategy
        hwin initialBank state.pending.receiver.control
          (state.twoCandidate A strategy hwin initialBank)) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank ×
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank :=
  (state.oneBisimulationDirect A strategy hwin initialBank,
    state.twoBisimulation A strategy hwin initialBank realizes)

/-- Uniform downstream constructor: a proof of the two hard overlap laws
installs both local finite bisimulations at every right-charged shadow. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations.rightBisimulations
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (state : RightShadow A strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank ×
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank :=
  state.bisimulations A strategy hwin initialBank (realizations.rightOne state)

/-- Uniform left-shadow constructor from the same two-field package. -/
noncomputable def
    ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations.leftBisimulations
    (realizations :
      ProfiledRawJointGuardedCommonTailChargedHardOverlapRealizations A
        strategy hwin initialBank)
    (state : LeftShadow A strategy hwin) :
    ProfiledRawJointGuardedCommonTailChargedNoRecvOneBisimulation A strategy
        hwin initialBank ×
      ProfiledRawJointGuardedCommonTailChargedNoRecvTwoBisimulation A strategy
        hwin initialBank :=
  state.bisimulations A strategy hwin initialBank (realizations.leftTwo state)

end


end DetParityAutomaton

end DistributedSynthesis
