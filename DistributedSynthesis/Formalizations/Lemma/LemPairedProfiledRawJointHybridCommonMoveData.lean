/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBothRestart

/-!
# Policy-free data of one installed common move

The exact common/strict root guards use only one literal common world, its
installed raw move, and the two equations identifying their public incidence
code and move.  They do not use reachability or the realization table of the
finite policy that happened to expose those data.

This four-field interface makes that dependency explicit.  In particular it
can be populated both by an ordinary common-policy control and by a reachable
false/common state of one fixed root-pinned policy.  The interface is
proof-side data: its local output projections contain no graph, orientation,
or strict-leader observation.
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

/-- The policy-free part of a common installed move.  The incidence code is
stored explicitly so coercions from either provenance interface are
nondependent and remain usable inside dependent controller families. -/
structure ProfiledRawJointHybridCommonMoveData
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  incidenceCode : ProfiledRawJointIncidenceCode A (I := Unit)
  rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  world : ProfiledRawJointCommonBaseWorld A strategy
  incidence_eq :
    (profiledRawJointCommonWorldFamily A world).incidenceCode A =
      incidenceCode
  move_eq : (profiledRawJointCommonWorldFamily A world).move A = rawMove

namespace ProfiledRawJointHybridCommonMoveData

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The process-one/right slot carried by the common incidence code. -/
theorem right_slot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    installed.incidenceCode.family.right () =
      some (installed.world.procOneSlot A) := by
  calc
    installed.incidenceCode.family.right () =
        ((profiledRawJointCommonWorldFamily A installed.world).incidenceCode A
          ).family.right () :=
      congrArg (fun code ↦ code.family.right ()) installed.incidence_eq.symm
    _ = some (installed.world.procOneSlot A) := rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The process-two/left slot carried by the same common incidence code. -/
theorem left_slot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    installed.incidenceCode.family.left () =
      some (installed.world.procTwoSlot A) := by
  calc
    installed.incidenceCode.family.left () =
        ((profiledRawJointCommonWorldFamily A installed.world).incidenceCode A
          ).family.left () :=
      congrArg (fun code ↦ code.family.left ()) installed.incidence_eq.symm
    _ = some (installed.world.procTwoSlot A) := rfl

/-- Process one's right-block lambda selected by the installed joint move. -/
def rightLambda
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (installed.world.procOne A).lambdaOfStrategy

/-- Process-two's left-block mirror. -/
def leftLambda
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (installed.world.procTwo A).lambdaOfStrategy

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- The right lambda is the Unit entry of the installed raw move. -/
theorem rightLambda_selected
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    installed.rawMove.rightLambda () = some installed.rightLambda := by
  rw [← installed.move_eq]
  rfl

/-- The left lambda is the other Unit entry of the installed raw move. -/
theorem leftLambda_selected
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    installed.rawMove.leftLambda () = some installed.leftLambda := by
  rw [← installed.move_eq]
  rfl

/-- The selected right lambda has the profile stored in the common slot. -/
theorem rightLambda_initialProfile
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    rightInitialFirstProfile installed.rightLambda =
      (installed.world.procOneSlot A).2 :=
  rfl

/-- Left-profile mirror. -/
theorem leftLambda_initialProfile
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    leftInitialFirstProfile installed.leftLambda =
      (installed.world.procTwoSlot A).2 :=
  rfl

/-- The selected right lambda wins from its exact stored entry whenever the
original distributed strategy wins. -/
theorem rightLambda_foreverAccepts
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    PairedRightForeverAccepts A
      (installed.world.procOneSlot A).1.1 installed.rightLambda := by
  exact pairedRightForeverAccepts_of_winning A strategy hwin
    (installed.world.procOne A)

/-- Left-orientation mirror. -/
theorem leftLambda_foreverAccepts
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    PairedLeftForeverAccepts A
      (installed.world.procTwoSlot A).1.1 installed.leftLambda := by
  exact pairedLeftForeverAccepts_of_winning A strategy hwin
    (installed.world.procTwo A)

end

/-- Process one's locally executable simultaneous receive projection. -/
def bothOutputOne
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) : Out₁ :=
  pairedLeftInformedForRow .both
    (pairedLeftReceiverStrategy installed.leftLambda [] input)

/-- Process-two's local mirror, in right-block input order. -/
def bothOutputTwo
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) : Out₂ :=
  pairedRightInformedForRow .both
    (pairedRightReceiverStrategy installed.rightLambda []
      (input.2, input.1))

/-- Literal output of the original strategy at the common simultaneous
successor. -/
def literalBothOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  let round := nextRound strategy (installed.world.procOne A).bothHistory
    ⟨input.1, input.2, Graph.both⟩
  (round.outputOne, round.outputTwo)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- The two local projections are the literal common semantic output. -/
@[simp] theorem bothOutputs_eq_literal
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    (bothOutputOne A installed input, bothOutputTwo A installed input) =
      literalBothOutput A installed input := by
  rfl

/-- Process one's common/strict-left receive coherence equation. -/
theorem bothOutputOne_eq_leftReceiver
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    bothOutputOne A installed input =
      pairedLeftInformedForRow .both
        (profiledLeftReceiverStrategy A
          (installed.world.procTwoSlot A).1.1
          installed.leftLambda [] input).physical := by
  rfl

/-- Process-two's common/strict-right receive coherence equation. -/
theorem bothOutputTwo_eq_rightReceiver
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (input : In₁ × In₂) :
    bothOutputTwo A installed input =
      pairedRightInformedForRow .both
        (profiledRightReceiverStrategy A
          (installed.world.procOneSlot A).1.1
          installed.rightLambda [] (input.2, input.1)).physical := by
  rfl

end

end ProfiledRawJointHybridCommonMoveData

end

end DetParityAutomaton

end DistributedSynthesis
