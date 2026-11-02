/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridProvenancePolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonMoveData

/-!
# The move installed at a reachable common hybrid control

Before the first strict round, a reachable finite hybrid-policy state whose
public tag is `common` still comes from one literal common semantic world.
This file inverts that provenance and records the two local receive
projections of its one installed raw move.

The common tag and the proof-side semantic witness are verification data.
Neither local receive table is given a graph, a strict orientation, or the
identity of a strict leader.
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

/-! ## Finite reachable common controls -/

/-- A reachable complete finite policy state whose public tag is literally
common.  The incidence payload is stored explicitly so later local tables do
not need dependent constructor inversion. -/
structure ProfiledRawJointHybridCommonPolicyKey
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) where
  incidenceCode : ProfiledRawJointIncidenceCode A (I := Unit)
  state : ProfiledRawJointHybridProvenancePolicyState A strategy initialCode
  reachable : ProfiledRawJointHybridProvenancePolicyReachable A strategy
    initialCode policy state
  state_code : state.1 = .common incidenceCode

/-- Reachable common policy controls form a finite macro alphabet. -/
noncomputable instance profiledRawJointHybridCommonPolicyKeyFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) :
    Fintype (ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
      policy) := by
  classical
  let encode := fun key : ProfiledRawJointHybridCommonPolicyKey A strategy
      initialCode policy ↦ (key.incidenceCode, key.state)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftCode, leftState, leftReachable, leftStateCode⟩
    rcases right with
      ⟨rightCode, rightState, rightReachable, rightStateCode⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-! ## Inversion of the installed move -/

/-- Complete common-world provenance of the one move installed at a common
finite policy control. -/
structure ProfiledRawJointHybridCommonInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
      policy) where
  rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  world : ProfiledRawJointCommonBaseWorld A strategy
  realizes : ProfiledRawJointHybridProvenanceMoveRealizesAt A strategy
    initialCode policy key.state (some rawMove)
  incidence_eq :
    (profiledRawJointCommonWorldFamily A world).incidenceCode A =
      key.incidenceCode
  move_eq : (profiledRawJointCommonWorldFamily A world).move A = rawMove

/-- Forget the policy realization while retaining exactly the data consumed
by local common/strict root guards. -/
def ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
      policy}
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    ProfiledRawJointHybridCommonMoveData A strategy where
  incidenceCode := key.incidenceCode
  rawMove := installed.rawMove
  world := installed.world
  incidence_eq := installed.incidence_eq
  move_eq := installed.move_eq

/-- Existing common installed moves coerce to their policy-free guard data,
so all old guard call sites remain source-compatible. -/
noncomputable instance
    profiledRawJointHybridCommonInstalledMoveCoeCommonMoveData
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
      policy} :
    CoeOut (ProfiledRawJointHybridCommonInstalledMove A strategy initialCode
      policy key)
      (ProfiledRawJointHybridCommonMoveData A strategy) where
  coe := ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every reachable common finite policy control has one installed raw move
and one literal common semantic source realizing it. -/
theorem nonempty_profiledRawJointHybridCommonInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
      policy) :
    Nonempty (ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) := by
  rcases exists_profiledRawJointHybridProvenanceInstalledSemanticSource A
      strategy initialCode policy key.state key.reachable with
    ⟨move, source, hmove, hsourceCode, hsourceMove⟩
  rw [key.state_code] at hsourceCode
  cases source with
  | common world =>
      simp only [ProfiledRawJointHybridSemanticState.code,
        ProfiledRawJointHybridSemanticState.move] at hsourceCode hsourceMove
      cases move with
      | none => simp at hsourceMove
      | some rawMove =>
          have hincidence :
              (profiledRawJointCommonWorldFamily A world).incidenceCode A =
                key.incidenceCode := by
            exact ProfiledRawJointHybridCode.common.inj hsourceCode
          have hrawMove :
              (profiledRawJointCommonWorldFamily A world).move A = rawMove := by
            exact Option.some.inj hsourceMove
          exact ⟨⟨rawMove, world, hmove, hincidence, hrawMove⟩⟩
  | oneSided source => simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead => simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode

namespace ProfiledRawJointHybridCommonInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointHybridCode A}
variable {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
  initialCode}
variable {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
  policy}

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Reassembled as a hybrid semantic source, the stored common world has
exactly the complete policy state's public code. -/
theorem semanticSource_code
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    (ProfiledRawJointHybridSemanticState.common installed.world).code A =
      key.state.1 := by
  rw [key.state_code]
  exact congrArg ProfiledRawJointHybridCode.common installed.incidence_eq

/-- Its semantic move is exactly the installed `some rawMove`. -/
theorem semanticSource_move
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    (ProfiledRawJointHybridSemanticState.common installed.world).move A =
      some installed.rawMove := by
  exact congrArg some installed.move_eq

/-- The process-one/right slot carried by the common code. -/
theorem right_slot
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    key.incidenceCode.family.right () =
      some (installed.world.procOneSlot A) := by
  rw [← installed.incidence_eq]
  rfl

/-- The process-two/left slot carried by the same common code. -/
theorem left_slot
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    key.incidenceCode.family.left () =
      some (installed.world.procTwoSlot A) := by
  rw [← installed.incidence_eq]
  rfl

end

/-- Process-one's right-block lambda selected by the installed joint move. -/
def rightLambda
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (installed.world.procOne A).lambdaOfStrategy

/-- Process-two's left-block mirror. -/
def leftLambda
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (installed.world.procTwo A).lambdaOfStrategy

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The right lambda is literally the Unit entry of the installed move. -/
theorem rightLambda_selected
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    installed.rawMove.rightLambda () = some installed.rightLambda := by
  rw [← installed.move_eq]
  rfl

/-- The left lambda is literally the other Unit entry of that same move. -/
theorem leftLambda_selected
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    installed.rawMove.leftLambda () = some installed.leftLambda := by
  rw [← installed.move_eq]
  rfl

/-- The selected right lambda has exactly the finite profile stored in its
common slot. -/
theorem rightLambda_initialProfile
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    rightInitialFirstProfile installed.rightLambda =
      (installed.world.procOneSlot A).2 :=
  rfl

/-- Left-profile mirror. -/
theorem leftLambda_initialProfile
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    leftInitialFirstProfile installed.leftLambda =
      (installed.world.procTwoSlot A).2 :=
  rfl

/-- Under the original winner, the selected right lambda wins every paired
continuation from the exact stored entry code. -/
theorem rightLambda_foreverAccepts
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    PairedRightForeverAccepts A
      (installed.world.procOneSlot A).1.1 installed.rightLambda := by
  exact pairedRightForeverAccepts_of_winning A strategy hwin
    (installed.world.procOne A)

/-- Left-orientation mirror. -/
theorem leftLambda_foreverAccepts
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    PairedLeftForeverAccepts A
      (installed.world.procTwoSlot A).1.1 installed.leftLambda := by
  exact pairedLeftForeverAccepts_of_winning A strategy hwin
    (installed.world.procTwo A)

end

/-! ## The two local simultaneous receive projections -/

/-- Process one's receive output computed from the left lambda installed at
the common control.  Its arguments contain no graph or orientation bit. -/
def bothOutputOne
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) : Out₁ :=
  pairedLeftInformedForRow .both
    (pairedLeftReceiverStrategy installed.leftLambda [] input)

/-- Process-two's local mirror, with the right-block input order. -/
def bothOutputTwo
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) : Out₂ :=
  pairedRightInformedForRow .both
    (pairedRightReceiverStrategy installed.rightLambda []
      (input.2, input.1))

/-- Literal physical output of the original strategy at the common
simultaneous successor. -/
def literalBothOutput
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  let round := nextRound strategy (installed.world.procOne A).bothHistory
    ⟨input.1, input.2, Graph.both⟩
  (round.outputOne, round.outputTwo)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The two independently executable receive projections are the literal
common semantic output. -/
@[simp] theorem bothOutputs_eq_literal
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    (bothOutputOne A installed input, bothOutputTwo A installed input) =
      literalBothOutput A installed input := by
  rfl

/-- Process one's simultaneous receive output is the same `.both` receiver
projection used on the locally indistinguishable strict-left alternative. -/
theorem bothOutputOne_eq_leftReceiver
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    bothOutputOne A installed input =
      pairedLeftInformedForRow .both
        (profiledLeftReceiverStrategy A
          (installed.world.procTwoSlot A).1.1
          installed.leftLambda [] input).physical := by
  rfl

/-- Process-two's simultaneous/strict-right coherence equation. -/
theorem bothOutputTwo_eq_rightReceiver
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    bothOutputTwo A installed input =
      pairedRightInformedForRow .both
        (profiledRightReceiverStrategy A
          (installed.world.procOneSlot A).1.1
          installed.rightLambda [] (input.2, input.1)).physical := by
  rfl

end

/-! ## The actual simultaneous finite-policy successor -/

/-- Finite common tag requested by one actual simultaneous input. -/
def simultaneousChildCode
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) : ProfiledRawJointHybridCode A :=
  .common (profiledRawJointIncidenceNext A key.incidenceCode.family
    installed.rawMove (profiledRawJointBothRestartDirection input))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The installed move's raw hybrid successor at a simultaneous direction is
exactly the explicit common child tag. -/
theorem hybridNext_simultaneous
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    profiledRawJointHybridNext A key.state.1 (some installed.rawMove)
        (.simultaneous input) =
      simultaneousChildCode A installed input := by
  rw [key.state_code]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- On the actual simultaneous child code, the finite policy successor is
the literal raw successor and the corresponding parity-monitor step. -/
theorem successor_eq_simultaneous
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    policy.successor key.state (simultaneousChildCode A installed input) =
      (simultaneousChildCode A installed input,
        (profiledRawJointHybridCodeParityDPA A initialCode).step key.state.2
          (simultaneousChildCode A installed input)) := by
  have hsuccessor := installed.realizes.2
    (simultaneousChildCode A installed input)
  have hraw :
      profiledRawJointHybridNext A key.state.1 (some installed.rawMove)
          (.simultaneous input) =
        simultaneousChildCode A installed input :=
    hybridNext_simultaneous A installed input
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A key.state.1
          (some installed.rawMove) (simultaneousChildCode A installed input) =
        simultaneousChildCode A installed input := by
    rw [← hraw]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) key.state.1 (some installed.rawMove)
        (.simultaneous input)
  rw [hfinite] at hsuccessor
  exact hsuccessor

/-- Package the actual simultaneous successor as another reachable finite
common policy control. -/
noncomputable def simultaneousSuccessorKey
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridCommonPolicyKey A strategy initialCode policy where
  incidenceCode := profiledRawJointIncidenceNext A key.incidenceCode.family
    installed.rawMove (profiledRawJointBothRestartDirection input)
  state := policy.successor key.state (simultaneousChildCode A installed input)
  reachable := profiledRawJointHybridProvenancePolicy_successor_reachable A
    strategy initialCode policy key.state key.reachable
      (simultaneousChildCode A installed input)
  state_code := by
    have h := congrArg Prod.fst (successor_eq_simultaneous A installed input)
    exact h

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem simultaneousSuccessorKey_state
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    (simultaneousSuccessorKey A installed input).state =
      policy.successor key.state (simultaneousChildCode A installed input) :=
  rfl

end ProfiledRawJointHybridCommonInstalledMove

end

end DetParityAutomaton

end DistributedSynthesis
