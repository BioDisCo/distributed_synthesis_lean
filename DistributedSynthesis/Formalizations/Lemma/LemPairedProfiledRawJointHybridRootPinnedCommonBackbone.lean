/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedInstalledMove

/-!
# The recurrent common backbone of the exact root-pinned hybrid policy

A simultaneous child of the guarded initial root is not merely a pair of
inputs.  It is a reachable false/common state of the *one policy selected at
the first input pair*.  Every later simultaneous round must advance that
same policy state.  Re-selecting an ordinary common policy here would lose
the sibling relation with a later strict exit.

This file packages the finite dependent control

```
  Σ first, FalseCommonKey first
```

and its exact same-policy simultaneous transition.  The outer `first` index
is proof-side policy provenance, not a leader or graph observation.  The two
physical output projections below are computed from the one installed common
world and therefore remain locally executable without learning an
orientation bit.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## One finite family of recurrent common controls -/

/-- A common control remembers the first input pair solely to retain the
exact guarded policy selected there.  Its dependent component is an arbitrary
reachable false/common state of that same policy. -/
abbrev ProfiledRawJointHybridRootPinnedCommonControl :=
  Σ first : In₁ × In₂,
    ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy hwin first

noncomputable instance profiledRawJointHybridRootPinnedCommonControlFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin) := by
  classical
  infer_instance

/-- The canonical first common control is the literal simultaneous child of
the guarded root. -/
noncomputable def profiledRawJointHybridRootPinnedInitialCommonControl
    (first current : In₁ × In₂) :
    ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin :=
  ⟨first,
    profiledRawJointHybridInitialRootPinnedSimultaneousKey A strategy hwin
      first current⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridRootPinnedInitialCommonControl_first
    (first current : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedInitialCommonControl A strategy hwin
      first current).1 = first :=
  rfl

/-- Invert the installed move at an arbitrary recurrent common control. -/
noncomputable def profiledRawJointHybridRootPinnedCommonInstalled
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin) :
    ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A strategy
      hwin control.1 control.2 :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove
      A strategy hwin control.1 control.2)

/-- One further simultaneous round advances the state of the exact same
root-pinned policy. -/
noncomputable def profiledRawJointHybridRootPinnedCommonNext
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin :=
  ⟨control.1,
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).simultaneousSuccessorKey A input⟩

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridRootPinnedCommonNext_first
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
      input).1 = control.1 :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedCommonNext_incidenceCode
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
      input).2.incidenceCode =
      profiledRawJointIncidenceNext A control.2.incidenceCode.family
        (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
          control).rawMove
        (profiledRawJointBothRestartDirection input) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedCommonNext_state
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
      input).2.state =
      (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin control.1
        ).policy.successor control.2.state
          ((profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
            control).simultaneousChildCode A input) :=
  rfl

/-- The state equation exposes both the literal common child code and the
literal parity-monitor successor. -/
theorem profiledRawJointHybridRootPinnedCommonNext_state_eq
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedCommonNext A strategy hwin control
      input).2.state =
      (false,
        ((profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
            control).simultaneousChildCode A input,
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy
              control.1)).step control.2.state.2.2
              ((profiledRawJointHybridRootPinnedCommonInstalled A strategy
                hwin control).simultaneousChildCode A input))) := by
  exact
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).successor_eq_simultaneous A input

end

/-- Proof-side strict alternative to one ambiguous round.  It is a sibling
successor of `CommonNext` in the very same policy table; this constructor is
not a runtime test for which graph occurred. -/
noncomputable def profiledRawJointHybridRootPinnedCommonStrictKey
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      control.1 :=
  (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
    ).strictSuccessorKey A actual

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridRootPinnedCommonStrictKey_incidenceCode
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedCommonStrictKey A strategy hwin control
      actual).incidenceCode =
      profiledRawJointOneSidedNext A control.2.incidenceCode
        (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
          control).rawMove
        (profiledRawJointCommonActualDirection actual) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact complete-state equation for the strict sibling. -/
theorem profiledRawJointHybridRootPinnedCommonStrictKey_state_eq
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridRootPinnedCommonStrictKey A strategy hwin control
      actual).state =
      (false,
        ((profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
            control).strictChildCode A actual,
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy
              control.1)).step control.2.state.2.2
              ((profiledRawJointHybridRootPinnedCommonInstalled A strategy
                hwin control).strictChildCode A actual))) := by
  exact
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).successor_eq_strict A actual

/-! ## Literal local output projections from the installed common world -/

namespace ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {first : In₁ × In₂}
variable {key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A
  strategy hwin first}

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The process-one/right slot named by the installed common world. -/
theorem right_slot
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    key.incidenceCode.family.right () =
      some (installed.world.procOneSlot A) := by
  rw [← installed.incidence_eq]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two/left mirror. -/
theorem left_slot
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    key.incidenceCode.family.left () =
      some (installed.world.procTwoSlot A) := by
  rw [← installed.incidence_eq]
  rfl

/-- The right-block lambda stored in the one installed semantic world. -/
def rightLambda
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (installed.world.procOne A).lambdaOfStrategy

/-- The left-block lambda stored in that same world. -/
def leftLambda
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  (installed.world.procTwo A).lambdaOfStrategy

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem rightLambda_selected
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    installed.rawMove.rightLambda () = some installed.rightLambda := by
  rw [← installed.move_eq]
  rfl

theorem leftLambda_selected
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    installed.rawMove.leftLambda () = some installed.leftLambda := by
  rw [← installed.move_eq]
  rfl

theorem rightLambda_initialProfile
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    rightInitialFirstProfile installed.rightLambda =
      (installed.world.procOneSlot A).2 :=
  rfl

theorem leftLambda_initialProfile
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    leftInitialFirstProfile installed.leftLambda =
      (installed.world.procTwoSlot A).2 :=
  rfl

/-- Any semantic representative installed at the same-policy simultaneous
successor has the literal process-one slot of the current world's `.both`
child.  Thus `Classical.choice` may change representatives, but it cannot
create a physical mosaic at the incidence boundary. -/
theorem simultaneousSuccessor_procOneSlot
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂)
    (nextInstalled :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first (installed.simultaneousSuccessorKey A input)) :
    nextInstalled.world.procOneSlot A =
      (profiledRawJointCommonWorldAfterBoth A installed.world input
        ).procOneSlot A := by
  have hfamily :
      (profiledRawJointCommonWorldFamily A installed.world).code A =
        key.incidenceCode.family :=
    congrArg ProfiledRawJointIncidenceCode.family installed.incidence_eq
  have hincidence :
      (profiledRawJointCommonWorldFamily A nextInstalled.world).incidenceCode A =
        (profiledRawJointCommonWorldFamily A
          (profiledRawJointCommonWorldAfterBoth A installed.world input)
          ).incidenceCode A := by
    calc
      (profiledRawJointCommonWorldFamily A nextInstalled.world).incidenceCode A
          = (installed.simultaneousSuccessorKey A input).incidenceCode :=
            nextInstalled.incidence_eq
      _ = profiledRawJointIncidenceNext A key.incidenceCode.family
          installed.rawMove (profiledRawJointBothRestartDirection input) := rfl
      _ = profiledRawJointIncidenceNext A
          ((profiledRawJointCommonWorldFamily A installed.world).code A)
          ((profiledRawJointCommonWorldFamily A installed.world).move A)
          (profiledRawJointBothRestartDirection input) := by
            rw [hfamily, installed.move_eq]
      _ = (profiledRawJointCommonWorldFamily A
          (profiledRawJointCommonWorldAfterBoth A installed.world input)
          ).incidenceCode A :=
            (profiledRawJointCommonWorldAfterBoth_incidenceCode A
              installed.world input).symm
  have hright := congrArg
    (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      code.family.right ()) hincidence
  exact Option.some.inj (by
    simpa [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procOneSlot,
      profiledRawRightSlotOfSemanticPair] using hright)

end

/-- Process one's locally executable projection of a simultaneous receive. -/
def bothOutputOne
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) : Out₁ :=
  pairedLeftInformedForRow .both
    (pairedLeftReceiverStrategy installed.leftLambda [] input)

/-- Process-two mirror. -/
def bothOutputTwo
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) : Out₂ :=
  pairedRightInformedForRow .both
    (pairedRightReceiverStrategy installed.rightLambda []
      (input.2, input.1))

/-- The original strategy's literal physical output at this common world. -/
def literalBothOutput
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  let round := nextRound strategy (installed.world.procOne A).bothHistory
    ⟨input.1, input.2, Graph.both⟩
  (round.outputOne, round.outputTwo)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The separately executable projections form that one literal output pair. -/
@[simp] theorem bothOutputs_eq_literal
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) :
    (installed.bothOutputOne A input, installed.bothOutputTwo A input) =
      installed.literalBothOutput A input := by
  rfl

end ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove

/-! ## Output and transition packaged at the finite common control -/

/-- The pair emitted on a genuine simultaneous receive from a recurrent
common control. -/
noncomputable def profiledRawJointHybridRootPinnedCommonBothOutput
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) : Out₁ × Out₂ :=
  let installed :=
    profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
  (installed.bothOutputOne A input, installed.bothOutputTwo A input)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridRootPinnedCommonBothOutput_eq_literal
    (control : ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointHybridRootPinnedCommonBothOutput A strategy hwin control
        input =
      (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
        ).literalBothOutput A input := by
  exact
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).bothOutputs_eq_literal A input

end

end DetParityAutomaton

end DistributedSynthesis
