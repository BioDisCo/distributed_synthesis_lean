/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedInitialCommonPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonPolicyLocalAdapter
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# Forever-common acceptance of the guarded occurrence-sensitive policy

This file follows the single common policy selected after two simultaneous
rounds.  Each reachable policy state chooses one jointly represented guarded
pair, and every next input pair follows that policy's complete successor
table.  Semantic points are reselected only to prove the finite incidence and
physical-state equations; they are not controller state.
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
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## One coherent finite-policy path -/

private def guardedForeverCommonSeed (inputs : Nat → In₁ × In₂) :=
  (inputs 0, inputs 1)

private abbrev InitialPoint (inputs : Nat → In₁ × In₂) :=
  profiledRawJointGuardedInitialCommonPoint A strategy
    (guardedForeverCommonSeed inputs)

private abbrev InitialPackage (inputs : Nat → In₁ × In₂) :=
  profiledRawJointGuardedInitialCommonPackage A strategy hwin
    (guardedForeverCommonSeed inputs)

private abbrev CommonKey (inputs : Nat → In₁ × In₂) :=
  ProfiledRawJointGuardedCommonPolicyKey A strategy hwin
    (InitialPoint A strategy inputs)
    (InitialPackage A strategy hwin inputs).policy

/-- Fixed-bank key trace; keeping the seed outside the recursion makes the
dependent policy type definitionally constant. -/
noncomputable def profiledRawJointGuardedForeverCommonKeyTrace
    (inputs : Nat → In₁ × In₂) : Nat → CommonKey A strategy hwin inputs
  | 0 => ProfiledRawJointGuardedCommonPolicyKey.root A strategy hwin
      (InitialPoint A strategy inputs)
      (InitialPackage A strategy hwin inputs).policy
  | n + 1 =>
      (profiledRawJointGuardedForeverCommonKeyTrace inputs n).next A strategy
        hwin (inputs (n + 2))

/-- Common control before physical round `n + 2`; the first two rounds form
the finite initial seed. -/
noncomputable def profiledRawJointGuardedForeverCommonControlTrace
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    CommonControl A strategy hwin :=
  ⟨guardedForeverCommonSeed inputs,
    profiledRawJointGuardedForeverCommonKeyTrace A strategy hwin inputs n⟩

@[simp] theorem profiledRawJointGuardedForeverCommonControlTrace_zero
    (inputs : Nat → In₁ × In₂) :
    profiledRawJointGuardedForeverCommonControlTrace A strategy hwin inputs 0 =
      profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
        (guardedForeverCommonSeed inputs) :=
  rfl

theorem profiledRawJointGuardedForeverCommonControlTrace_succ
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointGuardedForeverCommonControlTrace A strategy hwin inputs
        (n + 1) =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin
        (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs n) (inputs (n + 2)) :=
  rfl

/-- The control trace is literally a path of the one selected rational
policy. -/
noncomputable def profiledRawJointGuardedForeverCommonPolicyPath
    (inputs : Nat → In₁ × In₂) :
    SourceFreeBeliefCodeParityPolicyPath
      (profiledRawJointGuardedCommonCodeParityDPA A
        ((InitialPoint A strategy inputs).code A strategy))
      ((InitialPoint A strategy inputs).code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)
      (InitialPackage A strategy hwin inputs).policy where
  state := fun n ↦
    (profiledRawJointGuardedForeverCommonKeyTrace A strategy hwin inputs n
      ).state
  direction := fun n ↦ inputs (n + 2)
  initial := rfl
  successor := by
    intro n
    rfl

/-- Positive-time incidence-code word read by the checked common objective. -/
noncomputable def profiledRawJointGuardedForeverCommonCodeWord
    (inputs : Nat → In₁ × In₂) :
    OmegaWord (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  (profiledRawJointGuardedForeverCommonPolicyPath A strategy hwin inputs
    ).childCodeWord
      (profiledRawJointGuardedCommonCodeParityDPA A
        ((InitialPoint A strategy inputs).code A strategy))
      ((InitialPoint A strategy inputs).code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)
      (InitialPackage A strategy hwin inputs).policy

/-- The `n`-th code letter is exactly the incidence code stored by the next
reachable bank control. -/
theorem profiledRawJointGuardedForeverCommonCodeWord_eq_control
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointGuardedForeverCommonCodeWord A strategy hwin inputs n =
      (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin inputs
        (n + 1)).2.state.1 :=
  rfl

/-- The successive common incidence codes of this path satisfy the checked
common-code objective. -/
theorem profiledRawJointGuardedForeverCommon_childCode_accepts
    (inputs : Nat → In₁ × In₂) :
    (profiledRawJointGuardedCommonCodeParityDPA A
      ((InitialPoint A strategy inputs).code A strategy)).Accepts
      ((profiledRawJointGuardedForeverCommonPolicyPath A strategy hwin inputs
        ).childCodeWord
          (profiledRawJointGuardedCommonCodeParityDPA A
            ((InitialPoint A strategy inputs).code A strategy))
          ((InitialPoint A strategy inputs).code A strategy)
          (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
          (profiledRawJointGuardedCommonNext A strategy hwin)
          (InitialPackage A strategy hwin inputs).policy) :=
  (profiledRawJointGuardedForeverCommonPolicyPath A strategy hwin inputs
    ).accepts
      (profiledRawJointGuardedCommonCodeParityDPA A
        ((InitialPoint A strategy inputs).code A strategy))
      ((InitialPoint A strategy inputs).code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)
      (InitialPackage A strategy hwin inputs).policy

/-- Named form of the same theorem for the explicit positive-time code
word. -/
theorem profiledRawJointGuardedForeverCommonCodeWord_accepts
    (inputs : Nat → In₁ × In₂) :
    (profiledRawJointGuardedCommonCodeParityDPA A
      ((InitialPoint A strategy inputs).code A strategy)).Accepts
        (profiledRawJointGuardedForeverCommonCodeWord A strategy hwin
          inputs) :=
  profiledRawJointGuardedForeverCommon_childCode_accepts A strategy hwin
    inputs

/-! ## Proof-only semantic points selected at finite controls -/

/-- Select the semantic point witnessing validity of the finite guarded pair
at a reachable bank control. -/
noncomputable def profiledRawJointGuardedCommonControlPoint
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  Classical.choose
    (profiledRawJointGuardedInitialCommonControlPair_valid A strategy hwin
      control)

theorem profiledRawJointGuardedCommonControlPoint_code
    (control : CommonControl A strategy hwin) :
    (profiledRawJointGuardedCommonControlPoint A strategy hwin control).code A
        strategy = control.2.state.1 :=
  (Classical.choose_spec
    (profiledRawJointGuardedInitialCommonControlPair_valid A strategy hwin
      control)).1

theorem profiledRawJointGuardedCommonControlPoint_move
    (control : CommonControl A strategy hwin) :
    (profiledRawJointGuardedCommonControlPoint A strategy hwin control).move A
        strategy hwin =
      profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        control :=
  (Classical.choose_spec
    (profiledRawJointGuardedInitialCommonControlPair_valid A strategy hwin
      control)).2

/-- Consecutively selected proof points have the exact literal common-child
incidence, although their hidden histories need not agree. -/
theorem profiledRawJointGuardedCommonControlPoint_next_code
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonControlPoint A strategy hwin
        (profiledRawJointGuardedInitialCommonControlNext A strategy hwin
          control input)).code A strategy =
      ((profiledRawJointGuardedCommonControlPoint A strategy hwin control
        ).step A strategy input).code A strategy := by
  calc
    _ = (profiledRawJointGuardedInitialCommonControlNext A strategy hwin
          control input).2.state.1 :=
      profiledRawJointGuardedCommonControlPoint_code A strategy hwin _
    _ = (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control).bothNextCode A strategy hwin input :=
      profiledRawJointGuardedInitialCommonControlNext_code A strategy hwin
        control input
    _ = ((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).move A strategy hwin).bothNextCode A strategy hwin input := by
      rw [profiledRawJointGuardedCommonControlPoint_move A strategy hwin]
    _ = _ :=
      (ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
        (profiledRawJointGuardedCommonControlPoint A strategy hwin control)
        input).symm

/-- The process-one finite slot of a selected successor point is the slot of
the literal simultaneous child of the current point. -/
theorem profiledRawJointGuardedCommonControlPoint_next_procOneSlot
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input)).world A strategy).procOneSlot A =
      (profiledRawJointCommonWorldAfterBoth A
        ((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).world A strategy) input).procOneSlot A := by
  have hcode := profiledRawJointGuardedCommonControlPoint_next_code A strategy
    hwin control input
  have hright := congrArg
    (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      code.family.right ()) hcode
  exact Option.some.inj (by
    simpa [ProfiledRawJointGuardedCommonSemanticPoint.code,
      ProfiledRawJointGuardedCommonSemanticPoint.step,
      ProfiledRawJointGuardedCommonSemanticPoint.world,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procOneSlot,
      profiledRawRightSlotOfSemanticPair] using hright)

/-- Process-two mirror: the complete finite left slot selected at the next
common-policy control is exactly the left slot of the literal simultaneous
child.  In particular, this transports the initial action profile consumed
by the delayed-overlap theorem; no hidden history or orientation is exposed
to either local process. -/
theorem profiledRawJointGuardedCommonControlPoint_next_procTwoSlot
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input)).world A strategy).procTwoSlot A =
      (profiledRawJointCommonWorldAfterBoth A
        ((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).world A strategy) input).procTwoSlot A := by
  have hcode := profiledRawJointGuardedCommonControlPoint_next_code A strategy
    hwin control input
  have hleft := congrArg
    (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      code.family.left ()) hcode
  exact Option.some.inj (by
    simpa [ProfiledRawJointGuardedCommonSemanticPoint.code,
      ProfiledRawJointGuardedCommonSemanticPoint.step,
      ProfiledRawJointGuardedCommonSemanticPoint.world,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procTwoSlot,
      profiledRawLeftSlotOfSemanticPair] using hleft)

/-! ## Literal physical output of the guarded pair -/

/-- Physical simultaneous output selected by one guarded pair. -/
noncomputable def profiledRawJointGuardedCommonPairBothOutput
    (pair : CommonPair A strategy hwin) (input : In₁ × In₂) :
    Out₁ × Out₂ :=
  ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
    (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth)

/-- At a reachable control, the selected guarded output is one literal
original-strategy simultaneous round of its proof-only semantic point. -/
theorem profiledRawJointGuardedCommonControlPair_bothOutput_literal
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control) input =
      let point :=
        profiledRawJointGuardedCommonControlPoint A strategy hwin control
      let round := nextRound strategy (point.world A strategy).procOne.bothHistory
        ⟨input.1, input.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  let point :=
    profiledRawJointGuardedCommonControlPoint A strategy hwin control
  have hmove :=
    profiledRawJointGuardedCommonControlPoint_move A strategy hwin control
  rw [← hmove]
  have hclosing :
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
          (point.move A strategy hwin) input =
        (pairedLeftInformedForRow .both
            ((point.move A strategy hwin).leftRootRecord A strategy hwin input
              ).2.1.physical,
          pairedRightInformedForRow .both
            ((point.move A strategy hwin).rightRootRecord A strategy hwin input
              ).2.1.physical) := by
    apply Prod.ext
    · exact (point.move A strategy hwin).root_outputOne A strategy hwin input
    · exact (point.move A strategy hwin).root_outputTwo A strategy hwin input
  rw [hclosing]
  let family := profiledRawJointCommonWorldFamily A point.parent
  let direction := profiledRawJointBothRestartDirection point.incoming
  have hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A (point.world A strategy) :=
    profiledRawJointCommonWorld_semanticChild_eq_bothRestart A point.parent
      point.incoming
  simpa [point, family, direction,
    ProfiledRawJointGuardedCommonSemanticPoint.move,
    profiledRawJointGuardedCommonPairOfWorld,
    profiledRawJointGuardedCommonRightMoveOfWorld,
    profiledRawJointGuardedCommonLeftMoveOfWorld,
    ProfiledRawJointGuardedCommonPair.rightRootRecord,
    ProfiledRawJointGuardedCommonPair.leftRootRecord] using
      (profiledRawJointGuardedSiblingControllerRootRecords_bothOutput_eq_literal
        A hwin family direction (point.world A strategy) hchild false false
          input)

/-! ## Consecutive DPA-state equations -/

/-- The next selected occurrence starts at the current occurrence's exact
post-entry DPA state. -/
theorem profiledRawJointGuardedCommonControlPoint_next_root
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input)).world A strategy).root =
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin control
        ).world A strategy).procOne A).code.2 := by
  have hslot :=
    profiledRawJointGuardedCommonControlPoint_next_procOneSlot A strategy hwin
      control input
  exact congrArg (fun slot : ProfiledRawRightSlot A ↦ slot.1.2) hslot

/-- Its `.both` entry state is the literal deterministic DPA step generated
by the current guarded physical output. -/
theorem profiledRawJointGuardedCommonControlPoint_next_bothState
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (((profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input)).world A strategy).procOne A).code.2 =
      A.step
        ((((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).world A strategy).procOne A).code.2)
        (bothRoundRecord input
          (profiledRawJointGuardedCommonPairBothOutput A strategy hwin
            (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
              control) input).1
          (profiledRawJointGuardedCommonPairBothOutput A strategy hwin
            (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
              control) input).2) := by
  have hslot :=
    profiledRawJointGuardedCommonControlPoint_next_procOneSlot A strategy hwin
      control input
  have hcode := congrArg
    (fun slot : ProfiledRawRightSlot A ↦ slot.1.1.2) hslot
  change
    (((profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input)).world A strategy).procOne A).code.2 =
      (((profiledRawJointCommonWorldAfterBoth A
        ((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).world A strategy) input).procOne A).code.2) at hcode
  rw [hcode]
  rw [profiledRawJointGuardedCommonControlPair_bothOutput_literal A strategy
    hwin control input]
  simp [profiledRawJointCommonWorldAfterBoth,
    profiledRawRightCommonBaseWorld,
    ProfiledRawJointCommonBaseWorld.procOne,
    ProfiledRawJointCommonBaseWorld.procOneMember,
    profiledRawProcOneRowHistory, procOneFreshPair,
    ProcOnePairedEntryRep.code, entryState, History.append,
    List.foldl_append, bothRoundRecord, nextRound]

/-! ## Literal forever-common physical word -/

/-- The selected root representative advertises exactly the literal
two-round seed code. -/
theorem profiledRawJointGuardedForeverCommonControlPoint_zero_code
    (inputs : Nat → In₁ × In₂) :
    (profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
        inputs 0)).code A strategy =
      (InitialPoint A strategy inputs).code A strategy := by
  calc
    _ = (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs 0).2.state.1 :=
      profiledRawJointGuardedCommonControlPoint_code A strategy hwin _
    _ = _ := congrArg Prod.fst
      (InitialPackage A strategy hwin inputs).policy.accepts.1.1

/-- At the root of the selected bank, the proof-only representative has
exactly the complete process-one slot of the literal world reached by the
first two simultaneous rounds. -/
theorem profiledRawJointGuardedForeverCommonControlPoint_zero_procOneSlot
    (inputs : Nat → In₁ × In₂) :
    ((profiledRawJointGuardedCommonControlPoint A strategy hwin
      (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
        inputs 0)).world A strategy).procOneSlot A =
      ((InitialPoint A strategy inputs).world A strategy).procOneSlot A := by
  have hcode :=
    profiledRawJointGuardedForeverCommonControlPoint_zero_code A strategy hwin
      inputs
  have hright := congrArg
    (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      code.family.right ()) hcode
  exact Option.some.inj (by
    simpa [ProfiledRawJointGuardedCommonSemanticPoint.code,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procOneSlot,
      profiledRawRightSlotOfSemanticPair] using hright)

/-- Literal first simultaneous round of the original winning strategy. -/
def profiledRawJointGuardedForeverCommonFirstRound
    (inputs : Nat → In₁ × In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  nextRound strategy []
    ⟨(inputs 0).1, (inputs 0).2, Graph.both⟩

/-- Literal second simultaneous round, after which the finite common-policy
bank is selected. -/
def profiledRawJointGuardedForeverCommonSecondRound
    (inputs : Nat → In₁ × In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let world := profiledRawJointInitialCommonBaseWorld A strategy
    (inputs 0).1 (inputs 0).2
  nextRound strategy (world.procOne A).bothHistory
    ⟨(inputs 1).1, (inputs 1).2, Graph.both⟩

/-- All later simultaneous rounds use the one occurrence-sensitive rational
policy selected by the two-round seed. -/
noncomputable def profiledRawJointGuardedForeverCommonTailWord
    (inputs : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    let control :=
      profiledRawJointGuardedForeverCommonControlTrace A strategy hwin inputs n
    let output := profiledRawJointGuardedCommonPairBothOutput A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
      (inputs (n + 2))
    bothRoundRecord (inputs (n + 2)) output.1 output.2

/-- Complete physical all-receive execution: two literal seed rounds followed
by the outputs of the finite guarded common bank. -/
noncomputable def profiledRawJointGuardedForeverCommonPhysicalWord
    (inputs : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  OmegaWord.prependList
    [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
      profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
    (profiledRawJointGuardedForeverCommonTailWord A strategy hwin inputs)

/-- After the two literal seed rounds, the physical DPA run is exactly the
`.both` state stored by the representative selected at the root bank key. -/
theorem profiledRawJointGuardedForeverCommon_run_two
    (inputs : Nat → In₁ × In₂) :
    A.run (profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
        inputs) 2 =
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin
        (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs 0)).world A strategy).procOne A).code.2 := by
  have hslot :=
    profiledRawJointGuardedForeverCommonControlPoint_zero_procOneSlot A
      strategy hwin inputs
  have hboth := congrArg
    (fun slot : ProfiledRawRightSlot A ↦ slot.1.1.2) hslot
  rw [show 2 = 1 + 1 by omega, A.run_succ, A.run_succ]
  simpa [profiledRawJointGuardedForeverCommonPhysicalWord,
    profiledRawJointGuardedForeverCommonFirstRound,
    profiledRawJointGuardedForeverCommonSecondRound,
    ProfiledRawJointGuardedCommonSemanticPoint.world,
    profiledRawJointCommonWorldAfterBoth,
    profiledRawRightCommonBaseWorld,
    ProfiledRawJointCommonBaseWorld.procOneSlot,
    profiledRawRightSlotOfSemanticPair,
    ProfiledRawJointCommonBaseWorld.procOneMember,
    ProfiledRawJointCommonBaseWorld.procOne,
    profiledRawProcOneRowHistory, procOneFreshPair,
    ProcOnePairedEntryRep.code, entryState, History.append,
    List.foldl_append] using hboth.symm

/-- At every later physical time, the deterministic run is the `.both` state
of the proof-only point selected at the corresponding finite bank control.
Only complete finite slots are coupled between consecutive representatives. -/
theorem profiledRawJointGuardedForeverCommon_run_add_two
    (inputs : Nat → In₁ × In₂) : ∀ n,
    A.run (profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
        inputs) (n + 2) =
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin
        (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs n)).world A strategy).procOne A).code.2 := by
  intro n
  induction n with
  | zero =>
      exact profiledRawJointGuardedForeverCommon_run_two A strategy hwin inputs
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, A.run_succ, ih]
      rw [profiledRawJointGuardedForeverCommonControlTrace_succ A strategy
        hwin inputs n]
      have hnext :=
        profiledRawJointGuardedCommonControlPoint_next_bothState A strategy hwin
          (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
            inputs n) (inputs (n + 2))
      simp [profiledRawJointGuardedForeverCommonPhysicalWord,
        profiledRawJointGuardedForeverCommonTailWord]
      exact hnext.symm

/-! ## Canonical hidden-thread alignment -/

/-- Tagged form of the bare common-code word, exposing the existing hybrid
hidden-lineage monitor without changing the finite controller state. -/
noncomputable def profiledRawJointGuardedForeverCommonTaggedCodeWord
    (inputs : Nat → In₁ × In₂) :
    OmegaWord (ProfiledRawJointHybridCode A) :=
  OmegaWord.map ProfiledRawJointHybridCode.common
    (profiledRawJointGuardedForeverCommonCodeWord A strategy hwin inputs)

/-- One finite objective root exposed by a selected semantic point.  The
side is proof-only and is never an observation of either local process. -/
def profiledRawJointGuardedForeverCommonThreadRoot
    (control : CommonControl A strategy hwin) :
    IndexedLineageSide → ProfiledRawJointThreadRoot A
  | .right => .inl
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin control
        ).world A strategy).procOneSlot A)
  | .left => .inr
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin control
        ).world A strategy).procTwoSlot A)

/-- Both common slots carry the priority of the point's epoch root. -/
theorem profiledRawJointGuardedForeverCommonThreadRoot_priority
    (control : CommonControl A strategy hwin) (side : IndexedLineageSide) :
    profiledRawJointThreadRootPriority A
        (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
          control side) =
      A.priority
        ((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).world A strategy).root := by
  cases side <;> rfl

/-- Alternating hidden side at positive monitor time. -/
def profiledRawJointGuardedForeverCommonPositiveSide :
    Nat → IndexedLineageSide
  | 0 => .left
  | n + 1 => (profiledRawJointGuardedForeverCommonPositiveSide n).other

@[simp] theorem profiledRawJointGuardedForeverCommonPositiveSide_succ
    (n : Nat) :
    profiledRawJointGuardedForeverCommonPositiveSide (n + 1) =
      (profiledRawJointGuardedForeverCommonPositiveSide n).other :=
  rfl

/-- Every side of the literal initial common code exposes the corresponding
slot of the representative selected at the root control. -/
theorem profiledRawJointGuardedForeverCommon_initialSlot
    (inputs : Nat → In₁ × In₂) (side : IndexedLineageSide) :
    profiledRawJointHybridCurrentSlots A side
        (.common ((InitialPoint A strategy inputs).code A strategy)) () =
      some (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
        (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs 0) side) := by
  rw [← profiledRawJointGuardedForeverCommonControlPoint_zero_code A strategy
    hwin inputs]
  cases side <;>
    simp [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots,
      profiledRawJointGuardedForeverCommonThreadRoot,
      ProfiledRawJointGuardedCommonSemanticPoint.code,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procOneSlot,
      ProfiledRawJointCommonBaseWorld.procTwoSlot,
      profiledRawRightSlotOfSemanticPair,
      profiledRawLeftSlotOfSemanticPair]

/-- Every positive code letter exposes the two slots of the representative
selected at the corresponding next finite control. -/
theorem profiledRawJointGuardedForeverCommon_codeSlot
    (inputs : Nat → In₁ × In₂) (n : Nat)
    (side : IndexedLineageSide) :
    profiledRawJointHybridCurrentSlots A side
        (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs n) () =
      some (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
        (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs (n + 1)) side) := by
  change profiledRawJointHybridCurrentSlots A side
      (.common (profiledRawJointGuardedForeverCommonCodeWord A strategy hwin
        inputs n)) () = _
  rw [profiledRawJointGuardedForeverCommonCodeWord_eq_control A strategy hwin
    inputs n]
  rw [← profiledRawJointGuardedCommonControlPoint_code A strategy hwin
    (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin inputs
      (n + 1))]
  cases side <;>
    simp [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots,
      profiledRawJointGuardedForeverCommonThreadRoot,
      ProfiledRawJointGuardedCommonSemanticPoint.code,
      ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procOneSlot,
      ProfiledRawJointCommonBaseWorld.procTwoSlot,
      profiledRawRightSlotOfSemanticPair,
      profiledRawLeftSlotOfSemanticPair]

/-- The canonical `.right`-resolved code thread remains live forever.  At
positive time `n+1` it names the root of the next selected finite control. -/
theorem profiledRawJointGuardedForeverCommon_codeRun_succ
    (inputs : Nat → In₁ × In₂) : ∀ n,
    codedAlternatingIndexedLineageCodeRun
        (.common ((InitialPoint A strategy inputs).code A strategy))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs)
        .right () (n + 1) =
      (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs n,
        .live (profiledRawJointGuardedForeverCommonPositiveSide n) ()
          (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
            (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
              inputs (n + 1))
            (profiledRawJointGuardedForeverCommonPositiveSide n))) := by
  intro n
  induction n with
  | zero =>
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      change codedAlternatingIndexedLineageStep
          (fun _ (_ : Unit) nextCode ↦ nextCode)
          (profiledRawJointHybridCurrentSlots A)
          (codedAlternatingIndexedLineageCodeChild
            (profiledRawJointHybridCurrentSlots A))
          ((.common ((InitialPoint A strategy inputs).code A strategy)),
            .initial)
          (Unit.unit,
            profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
              inputs 0)
          (.right, ()) = _
      apply codedAlternatingIndexedLineageCodeStep_initial_of
        (profiledRawJointHybridCurrentSlots A)
        (.common ((InitialPoint A strategy inputs).code A strategy))
        (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs 0)
        .right ()
        (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
          (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
            inputs 0) .right)
        (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
          (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
            inputs 1) .left)
      · exact profiledRawJointGuardedForeverCommon_initialSlot A strategy hwin
          inputs .right
      · exact profiledRawJointGuardedForeverCommon_codeSlot A strategy hwin
          inputs 0 .left
  | succ n ih =>
      unfold codedAlternatingIndexedLineageCodeRun at ih ⊢
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        codedAlternatingIndexedLineageRun_succ, ih]
      apply codedAlternatingIndexedLineageCodeStep_live_of
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs n)
        (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs (n + 1))
        (profiledRawJointGuardedForeverCommonPositiveSide n) ()
        (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
          (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
            inputs (n + 1))
          (profiledRawJointGuardedForeverCommonPositiveSide n))
        (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
          (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
            inputs (n + 2))
          (profiledRawJointGuardedForeverCommonPositiveSide (n + 1)))
        (.right, ())
      · exact profiledRawJointGuardedForeverCommon_codeSlot A strategy hwin
          inputs n (profiledRawJointGuardedForeverCommonPositiveSide n)
      · rw [profiledRawJointGuardedForeverCommonPositiveSide_succ]
        exact profiledRawJointGuardedForeverCommon_codeSlot A strategy hwin
          inputs (n + 1)
          (profiledRawJointGuardedForeverCommonPositiveSide n).other

/-- Priority sequence of the canonical hidden code thread. -/
noncomputable def profiledRawJointGuardedForeverCommonCodePriorities
    (inputs : Nat → In₁ × In₂) : Nat → Nat :=
  fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem
      (.common ((InitialPoint A strategy inputs).code A strategy))
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun
        (.common ((InitialPoint A strategy inputs).code A strategy))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin
          inputs)
        .right () n)

/-- Positive hidden-code priorities are exactly the original DPA priorities
of the concrete physical word, with the expected two-round seed offset. -/
theorem profiledRawJointGuardedForeverCommonCodePriorities_succ
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointGuardedForeverCommonCodePriorities A strategy hwin inputs
        (n + 1) =
      A.priority
        (A.run (profiledRawJointGuardedForeverCommonPhysicalWord A strategy
          hwin inputs) (n + 2)) := by
  rw [profiledRawJointGuardedForeverCommonCodePriorities,
    profiledRawJointGuardedForeverCommon_codeRun_succ A strategy hwin inputs n]
  change profiledRawJointThreadRootPriority A
      (profiledRawJointGuardedForeverCommonThreadRoot A strategy hwin
        (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          inputs (n + 1))
        (profiledRawJointGuardedForeverCommonPositiveSide n)) = _
  rw [profiledRawJointGuardedForeverCommonThreadRoot_priority A strategy hwin]
  apply congrArg A.priority
  have hroot :=
    profiledRawJointGuardedCommonControlPoint_next_root A strategy hwin
      (profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
        inputs n) (inputs (n + 2))
  rw [← profiledRawJointGuardedForeverCommonControlTrace_succ A strategy hwin
    inputs n] at hroot
  have hrun :=
    profiledRawJointGuardedForeverCommon_run_add_two A strategy hwin inputs n
  exact hroot.trans hrun.symm

/-- **Forever-common physical acceptance.**  The output word generated by
the two local receive machines is accepted by the original DPA.  The proof
uses one occurrence-sensitive rational policy and finite slot coupling; it
does not paste independently selected semantic histories. -/
theorem profiledRawJointGuardedForeverCommonPhysicalWord_accepts
    (inputs : Nat → In₁ × In₂) :
    A.Accepts
      (profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
        inputs) := by
  let initialCode := (InitialPoint A strategy inputs).code A strategy
  let codeWord :=
    profiledRawJointGuardedForeverCommonTaggedCodeWord A strategy hwin inputs
  let codePriorities :=
    profiledRawJointGuardedForeverCommonCodePriorities A strategy hwin inputs
  let physicalWord :=
    profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin inputs
  let physicalPriorities := fun n ↦ A.priority (A.run physicalWord n)
  have hbare :=
    profiledRawJointGuardedForeverCommonCodeWord_accepts A strategy hwin inputs
  have hcodeAccepts :
      (profiledRawJointHybridCodeParityDPA A (.common initialCode)).Accepts
        codeWord := by
    rw [profiledRawJointGuardedCommonCodeParityDPA,
      DetParityAutomaton.comap_accepts_iff] at hbare
    simpa [initialCode, codeWord,
      profiledRawJointGuardedForeverCommonTaggedCodeWord] using hbare
  have hcodeParity : NatSeqMinEvenParity codePriorities := by
    have hcoded :
        (codedAlternatingIndexedLineageCodeDPA (.common initialCode)
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).Accepts codeWord := by
      simpa [profiledRawJointHybridCodeParityDPA] using hcodeAccepts
    have hall := (codedAlternatingIndexedLineageCodeDPA_accepts_iff
      (.common initialCode)
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) codeWord).1 hcoded
    simpa [codePriorities,
      profiledRawJointGuardedForeverCommonCodePriorities, codeWord,
      initialCode] using hall IndexedLineageSide.right ()
  have hcodeTail :
      NatSeqMinEvenParity (fun n ↦ codePriorities (1 + n)) :=
    (natSeqMinEvenParity_shift codePriorities 1).mpr hcodeParity
  have hphysicalTail :
      NatSeqMinEvenParity (fun n ↦ physicalPriorities (2 + n)) := by
    convert hcodeTail using 1
    funext n
    simpa [codePriorities, physicalPriorities, physicalWord, Nat.add_comm]
      using
        (profiledRawJointGuardedForeverCommonCodePriorities_succ A strategy
          hwin inputs n).symm
  rw [A.accepts_iff_natSeqMinEvenParity]
  exact (natSeqMinEvenParity_shift physicalPriorities 2).mp hphysicalTail

end

end DetParityAutomaton

end DistributedSynthesis
