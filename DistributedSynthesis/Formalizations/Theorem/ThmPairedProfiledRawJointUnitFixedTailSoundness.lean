/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryControllerSoundness
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyControllerBank

/-!
# Fixed-side soundness of the raw-joint policy controllers

If the environment remains forever in one strict orientation, the two local
roles keep executing one controller from the raw-joint policy bank.  This
file reads the physical paired lambda from that controller and proves the
original two-row forever condition.  The orientation and the entry row are
only parameters of the proof statement; neither local controller is given a
leader or orientation bit.
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

/-! ## Reading the physical lambda from a narrowed raw-joint controller -/

/-- Forget the target certificates in a narrowed right controller and read
its physical paired lambda. -/
noncomputable def profiledRawJointUnitRightLambdaOfNarrowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawRightSlot A)
    (narrowed : List In₁ → NarrowedBlockLabel In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy state source).State) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := fun word input ↦ (narrowed word).1 input
  informedLeft := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.informedFirst
  informedBoth := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.informedBoth
  bothOneLeft := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.closingFirst
  bothOneBoth := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.closingBoth

/-- Left-oriented mirror of `profiledRawJointUnitRightLambdaOfNarrowed`. -/
noncomputable def profiledRawJointUnitLeftLambdaOfNarrowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawLeftSlot A)
    (narrowed : List In₂ → NarrowedBlockLabel In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy state source).State) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) where
  blind := fun word input ↦ (narrowed word).1 input
  informedRight := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.informedFirst
  informedBoth := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.informedBoth
  bothTwoRight := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.closingFirst
  bothTwoBoth := fun past move ↦
    ((narrowed (senderWord past)).2
      (narrowedControl
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy state source)
        narrowed past) move).physical.closingBoth

/-! ## Exact physical readback -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointUnitRightLambdaOfNarrowed_blockWord
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawRightSlot A)
    (narrowed : List In₁ → NarrowedBlockLabel In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy state source).State)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointUnitRightPhysicalLetter A
        (treePlay
          (narrowedInducedTree
            (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy initialCode policy state source)
            narrowed) env n) =
      pairedRightBlockWord
        (profiledRawJointUnitRightLambdaOfNarrowed A strategy initialCode
          policy state source narrowed) env n := by
  simp [treePlay, narrowedInducedTree, blockLabelApply,
    profiledRawJointUnitRightPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointUnitRightLambdaOfNarrowed, branchNode_eq_omegaPrefix,
    pairedRightBlockWord]

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointUnitLeftLambdaOfNarrowed_blockWord
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawLeftSlot A)
    (narrowed : List In₂ → NarrowedBlockLabel In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy state source).State)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointUnitLeftPhysicalLetter A
        (treePlay
          (narrowedInducedTree
            (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy initialCode policy state source)
            narrowed) env n) =
      pairedLeftBlockWord
        (profiledRawJointUnitLeftLambdaOfNarrowed A strategy initialCode
          policy state source narrowed) env n := by
  simp [treePlay, narrowedInducedTree, blockLabelApply,
    profiledRawJointUnitLeftPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointUnitLeftLambdaOfNarrowed, branchNode_eq_omegaPrefix,
    pairedLeftBlockWord, pairedLeftBlockLetterAt]

/-! ## Universal component of an arbitrary raw-joint play -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointUnitRightBlockMonitor_run_universal
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁) :
    ∀ n,
    ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy initialCode policy state source).run play n).1 =
      (pairedRightThreadSystem A source.1.1).universalRunDPA.run
        (fun k ↦ profiledRawJointUnitRightPhysicalLetter A (play k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (pairedRightThreadSystem A source.1.1).universalRunDPA.step
            ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy initialCode policy state source).run
                play n).1
            (profiledRawJointUnitRightPhysicalLetter A (play n)) =
          (pairedRightThreadSystem A source.1.1).universalRunDPA.step
            ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
              (fun k ↦ profiledRawJointUnitRightPhysicalLetter A (play k)) n)
            (profiledRawJointUnitRightPhysicalLetter A (play n))
      rw [ih]

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointUnitLeftBlockMonitor_run_universal
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂) :
    ∀ n,
    ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy initialCode policy state source).run play n).1 =
      (pairedLeftThreadSystem A source.1.1).universalRunDPA.run
        (fun k ↦ profiledRawJointUnitLeftPhysicalLetter A (play k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (pairedLeftThreadSystem A source.1.1).universalRunDPA.step
            ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy initialCode policy state source).run
                play n).1
            (profiledRawJointUnitLeftPhysicalLetter A (play n)) =
          (pairedLeftThreadSystem A source.1.1).universalRunDPA.step
            ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
              (fun k ↦ profiledRawJointUnitLeftPhysicalLetter A (play k)) n)
            (profiledRawJointUnitLeftPhysicalLetter A (play n))
      rw [ih]

/-! ## Fixed-side controller soundness -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointUnitRightController_forever
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy source.state
            source.slot).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy source.state source.slot)
      controller.labeledTree) :
    PairedRightForeverAccepts A source.slot.1.1
      (profiledRawJointUnitRightLambdaOfNarrowed A strategy initialCode policy
        source.state source.slot controller.labeledTree) := by
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy initialCode policy source.state source.slot
  let lambda := profiledRawJointUnitRightLambdaOfNarrowed A strategy
    initialCode policy source.state source.slot controller.labeledTree
  apply pairedRightForeverAccepts_of_universalDPA A source.slot.1.1 lambda
  intro env
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hwin : monitor.WinsPlay play := by
    exact (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp
        (narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads) env
  have hword :
      (fun k ↦ profiledRawJointUnitRightPhysicalLetter A (play k)) =
        pairedRightBlockWord lambda env := by
    funext k
    simpa [play, monitor, lambda] using
      (profiledRawJointUnitRightLambdaOfNarrowed_blockWord A strategy
        initialCode policy source.state source.slot controller.labeledTree env k)
  unfold BlockRecordMonitor.WinsPlay at hwin
  have heq :
      (fun n ↦ monitor.priority (monitor.run play n)) =
        (fun n ↦
          (pairedRightThreadSystem A source.slot.1.1).universalRunDPA.priority
            ((pairedRightThreadSystem A source.slot.1.1).universalRunDPA.run
              (pairedRightBlockWord lambda env) n) + 2) := by
    funext n
    have hsafe := profiledRawJointUnitRightBlockMonitor_safe_of_wins A strategy
      initialCode policy source play hwin n
    change (if (monitor.run play n).2.2.2.2 then
        (pairedRightThreadSystem A source.slot.1.1).universalRunDPA.priority
          (monitor.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointUnitRightBlockMonitor_run_universal A strategy
        initialCode policy source.state source.slot play n, hword]
  rw [heq] at hwin
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwin

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointUnitLeftController_forever
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initialCode policy source.state
            source.slot).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initialCode policy source.state source.slot)
      controller.labeledTree) :
    PairedLeftForeverAccepts A source.slot.1.1
      (profiledRawJointUnitLeftLambdaOfNarrowed A strategy initialCode policy
        source.state source.slot controller.labeledTree) := by
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy initialCode policy source.state source.slot
  let lambda := profiledRawJointUnitLeftLambdaOfNarrowed A strategy
    initialCode policy source.state source.slot controller.labeledTree
  apply pairedLeftForeverAccepts_of_universalDPA A source.slot.1.1 lambda
  intro env
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hwin : monitor.WinsPlay play := by
    exact (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp
        (narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads) env
  have hword :
      (fun k ↦ profiledRawJointUnitLeftPhysicalLetter A (play k)) =
        pairedLeftBlockWord lambda env := by
    funext k
    simpa [play, monitor, lambda] using
      (profiledRawJointUnitLeftLambdaOfNarrowed_blockWord A strategy
        initialCode policy source.state source.slot controller.labeledTree env k)
  unfold BlockRecordMonitor.WinsPlay at hwin
  have heq :
      (fun n ↦ monitor.priority (monitor.run play n)) =
        (fun n ↦
          (pairedLeftThreadSystem A source.slot.1.1).universalRunDPA.priority
            ((pairedLeftThreadSystem A source.slot.1.1).universalRunDPA.run
              (pairedLeftBlockWord lambda env) n) + 2) := by
    funext n
    have hsafe := profiledRawJointUnitLeftBlockMonitor_safe_of_wins A strategy
      initialCode policy source play hwin n
    change (if (monitor.run play n).2.2.2.2 then
        (pairedLeftThreadSystem A source.slot.1.1).universalRunDPA.priority
          (monitor.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointUnitLeftBlockMonitor_run_universal A strategy
        initialCode policy source.state source.slot play n, hword]
  rw [heq] at hwin
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwin

/-! ## The selected bank controllers -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointUnitPolicyControllerBank.right_forever
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :
    PairedRightForeverAccepts A source.slot.1.1
      (profiledRawJointUnitRightLambdaOfNarrowed A strategy (initial.code A)
        policy source.state source.slot ((bank.right source).1).labeledTree) :=
  profiledRawJointUnitRightController_forever A strategy (initial.code A)
    policy source (bank.right source).1 (bank.right source).2

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointUnitPolicyControllerBank.left_forever
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :
    PairedLeftForeverAccepts A source.slot.1.1
      (profiledRawJointUnitLeftLambdaOfNarrowed A strategy (initial.code A)
        policy source.state source.slot ((bank.left source).1).labeledTree) :=
  profiledRawJointUnitLeftController_forever A strategy (initial.code A)
    policy source (bank.left source).1 (bank.left source).2

/-! ## The literal infinite plays of the selected bank controllers -/

/-- The enriched infinite right-block play started at a fresh bank root. -/
noncomputable def profiledRawJointUnitRightPolicyOmegaPlay
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy (initial.code A))
      Out₁ :=
  treePlay
    (narrowedInducedTree
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot)
      ((bank.right source).1).labeledTree) env

/-- Left-oriented literal bank play. -/
noncomputable def profiledRawJointUnitLeftPolicyOmegaPlay
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy (initial.code A))
      Out₂ :=
  treePlay
    (narrowedInducedTree
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot)
      ((bank.left source).1).labeledTree) env

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- For either latent entry row, the literal physical word emitted by a
fresh selected right controller is accepted from exactly that row's source
state.  This is the fixed-right tail theorem consumed by the global carrier. -/
theorem ProfiledRawJointUnitPolicyControllerBank.right_physical_acceptsFrom
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (env : Nat → In₂ × In₁) :
    A.AcceptsFrom
      (match row with | .first => source.slot.1.1.1 | .both => source.slot.1.1.2)
      (fun n ↦ pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank source env n))) := by
  let lambda := profiledRawJointUnitRightLambdaOfNarrowed A strategy
    (initial.code A) policy source.state source.slot
      ((bank.right source).1).labeledTree
  have hforever := bank.right_forever A source
  have hword :
      (fun n ↦ pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank source env n))) =
      match row with
      | .first => pairedRightOmegaWord lambda.blind lambda.informedLeft env
      | .both => pairedRightOmegaWord lambda.blind lambda.informedBoth env := by
    funext n
    have hphysical :=
      profiledRawJointUnitRightLambdaOfNarrowed_blockWord A strategy
        (initial.code A) policy source.state source.slot
        ((bank.right source).1).labeledTree env n
    change profiledRawJointUnitRightPhysicalLetter A
        (profiledRawJointUnitRightPolicyOmegaPlay A bank source env n) = _
      at hphysical
    rw [hphysical]
    cases row <;> rfl
  rw [hword]
  cases row
  · exact hforever.1 env
  · exact hforever.2 env

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Fixed-left mirror of `right_physical_acceptsFrom`. -/
theorem ProfiledRawJointUnitPolicyControllerBank.left_physical_acceptsFrom
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (env : Nat → In₁ × In₂) :
    A.AcceptsFrom
      (match row with | .first => source.slot.1.1.1 | .both => source.slot.1.1.2)
      (fun n ↦ pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank source env n))) := by
  let lambda := profiledRawJointUnitLeftLambdaOfNarrowed A strategy
    (initial.code A) policy source.state source.slot
      ((bank.left source).1).labeledTree
  have hforever := bank.left_forever A source
  have hword :
      (fun n ↦ pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank source env n))) =
      match row with
      | .first => pairedLeftOmegaWord lambda.blind lambda.informedRight env
      | .both => pairedLeftOmegaWord lambda.blind lambda.informedBoth env := by
    funext n
    have hphysical :=
      profiledRawJointUnitLeftLambdaOfNarrowed_blockWord A strategy
        (initial.code A) policy source.state source.slot
        ((bank.left source).1).labeledTree env n
    change profiledRawJointUnitLeftPhysicalLetter A
        (profiledRawJointUnitLeftPolicyOmegaPlay A bank source env n) = _
      at hphysical
    rw [hphysical]
    cases row <;> rfl
  rw [hword]
  cases row
  · exact hforever.1 env
  · exact hforever.2 env

end

end DetParityAutomaton

end DistributedSynthesis
