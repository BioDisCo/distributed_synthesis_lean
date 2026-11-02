/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBothRestart
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedActualChild
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState

/-!
# The finite one-shot simultaneous restart below the initial root

The independently narrowed exceptional controllers were needed only after a
strict second round.  If the second round is again `both`, using those two
controllers is both unnecessary and unsound: their independently selected
receiver tables can form a cross mosaic.

This file keeps the two projections together for that one ambiguous round.
After an immediate root `both`, both processes know the first input pair.  On
the next `both`, both know the second input pair as well.  The pair of input
pairs is therefore a finite proof-side key.  From it we reconstruct the one
literal common world and emit the original strategy's physical `both` output.
The two executable projections factor through the two actual local receive
signatures; the full pair is never postulated as an extra process input.

Crucially, a `both` child remains a two-sided common world.  It is not replaced
here by either one-sided actual child and no Unit policy is selected here.
The hybrid common/one-sided tree performs that selection only after a strict
exit.  The last two lemmas below are the exact strict/`both` local projection
equalities consumed by that tree.

No unbounded view is stored by the implementation.  The semantic history is
used only to prove the finite output table and child code correct.  No process
is told an orientation, the graph, or the identity of a strict leader.
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

local instance : DecidableEq In₁ := Classical.decEq In₁
local instance : DecidableEq In₂ := Classical.decEq In₂

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-! ## The finite leader-free key -/

/-- The two consecutive input pairs surrounding the one-shot common restart.
Both pairs are known locally after two simultaneous receives. -/
abbrev ProfiledRawJointInitialCommonBothKey :=
  (In₁ × In₂) × (In₁ × In₂)

noncomputable instance profiledRawJointInitialCommonBothKeyFintype :
    Fintype (ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) := by
  classical
  infer_instance

/-- Common semantic world after the first physical root round. -/
def profiledRawJointInitialCommonBothWorld
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawJointInitialCommonBaseWorld A strategy key.1.1 key.1.2

/-- The exact two-sided raw family before the second simultaneous round. -/
def profiledRawJointInitialCommonBothFamily
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  profiledRawJointCommonWorldFamily A
    (profiledRawJointInitialCommonBothWorld A strategy key)

/-- The source-free direction of the second simultaneous round. -/
def profiledRawJointInitialCommonBothDirection
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointBothRestartDirection key.2

/-! ## The exact recursively common child -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The full two-sided child has the single source-free finite code proved by
the common-restart lemma. -/
theorem profiledRawJointInitialCommonBoth_jointChild_code
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    let direction := profiledRawJointInitialCommonBothDirection key
    (family.semanticChild A direction).code A =
      profiledRawJointFamilyNext A (family.code A) (family.move A) direction := by
  exact profiledRawJointCommonWorld_semanticChild_code_eq_bothRestart A
    (profiledRawJointInitialCommonBothWorld A strategy key) key.2

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- More strongly, the semantic child is literally the next common world.
Thus repeated simultaneous rounds never merge two separately selected
policies. -/
theorem profiledRawJointInitialCommonBoth_jointChild_eq
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    let world := profiledRawJointInitialCommonBothWorld A strategy key
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    family.semanticChild A (profiledRawJointInitialCommonBothDirection key) =
      profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A world key.2) := by
  exact profiledRawJointCommonWorld_semanticChild_eq_bothRestart A
    (profiledRawJointInitialCommonBothWorld A strategy key) key.2

/-! ## The finite physical one-shot output -/

/-- Literal physical output of the original strategy at the second `both`.
Only this finite pair is retained by the executable handoff. -/
def profiledRawJointInitialCommonBothOutput
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) : Out₁ × Out₂ :=
  let world := profiledRawJointInitialCommonBothWorld A strategy key
  let round := nextRound strategy (world.procOne A).bothHistory
    ⟨key.2.1, key.2.2, Graph.both⟩
  (round.outputOne, round.outputTwo)

/-! ## The two genuinely local receive projections -/

/-- Process one's proof-side key reconstruction.  Its arguments are exactly
the old common control, its own current input, and the input delivered by the
current receive. -/
def profiledRawJointInitialCommonBothKeyOfOneReceive
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) :
    ProfiledRawJointInitialCommonBothKey (In₁ := In₁) (In₂ := In₂) :=
  (first, (own, delivered))

/-- Process-two mirror. -/
def profiledRawJointInitialCommonBothKeyOfTwoReceive
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) :
    ProfiledRawJointInitialCommonBothKey (In₁ := In₁) (In₂ := In₂) :=
  (first, (delivered, own))

/-- Process one's local receive table.  No graph or leader bit is an
argument. -/
def profiledRawJointInitialCommonBothOutputOneOfReceive
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) : Out₁ :=
  (profiledRawJointInitialCommonBothOutput A strategy
    (profiledRawJointInitialCommonBothKeyOfOneReceive first own delivered)).1

/-- Process-two local receive table. -/
def profiledRawJointInitialCommonBothOutputTwoOfReceive
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) : Out₂ :=
  (profiledRawJointInitialCommonBothOutput A strategy
    (profiledRawJointInitialCommonBothKeyOfTwoReceive first own delivered)).2

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] in
/-- On a physical simultaneous round, the two independently executable local
reconstructions name the same proof-side common key. -/
@[simp] theorem profiledRawJointInitialCommonBoth_localKeys_agree
    (first current : In₁ × In₂) :
    profiledRawJointInitialCommonBothKeyOfOneReceive first current.1 current.2 =
      profiledRawJointInitialCommonBothKeyOfTwoReceive first current.2
        current.1 :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Hence the two local receive tables emit exactly the literal common
physical output. -/
@[simp] theorem profiledRawJointInitialCommonBoth_localOutputs
    (first current : In₁ × In₂) :
    (profiledRawJointInitialCommonBothOutputOneOfReceive A strategy first
        current.1 current.2,
      profiledRawJointInitialCommonBothOutputTwoOfReceive A strategy first
        current.2 current.1) =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) :=
  rfl

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Process one's local table is the raw left-receiver table at the common
`.both` row.  Since process one receives in both `left` and `both`, this is
also the strict/`both` output-coherence equation. -/
theorem profiledRawJointInitialCommonBoth_outputOne_eq_leftReceiver
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointInitialCommonBothOutput A strategy key).1 =
      pairedLeftInformedForRow .both
        (profiledLeftReceiverStrategy A
          ((profiledRawJointInitialCommonBothWorld A strategy key).procTwo A).code
          ((profiledRawJointInitialCommonBothWorld A strategy key).procTwo A
            ).lambdaOfStrategy [] key.2).physical := by
  rfl

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Process-two receive mirror. -/
theorem profiledRawJointInitialCommonBoth_outputTwo_eq_rightReceiver
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointInitialCommonBothOutput A strategy key).2 =
      pairedRightInformedForRow .both
        (profiledRightReceiverStrategy A
          ((profiledRawJointInitialCommonBothWorld A strategy key).procOne A).code
          ((profiledRawJointInitialCommonBothWorld A strategy key).procOne A
            ).lambdaOfStrategy [] (key.2.2, key.2.1)).physical := by
  rfl

/-! ## Finite child controls reconstructed from the same local signatures -/

/-- Finite process-one projection installed by its receive transition. -/
noncomputable def profiledRawJointInitialCommonBothOneReceiveChildControl
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) :
    Unit → Option (ProfiledRawRightSlot A) :=
  let key := profiledRawJointInitialCommonBothKeyOfOneReceive first own delivered
  let family := profiledRawJointInitialCommonBothFamily A strategy key
  ((family.semanticChild A
    (profiledRawJointInitialCommonBothDirection key)).incidenceCode A
      ).family.right

/-- Finite process-two projection installed by its receive transition. -/
noncomputable def profiledRawJointInitialCommonBothTwoReceiveChildControl
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) :
    Unit → Option (ProfiledRawLeftSlot A) :=
  let key := profiledRawJointInitialCommonBothKeyOfTwoReceive first own delivered
  let family := profiledRawJointInitialCommonBothFamily A strategy key
  ((family.semanticChild A
    (profiledRawJointInitialCommonBothDirection key)).incidenceCode A
      ).family.left

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The two local reconstructions are exactly the two projections of one
finite joint successor code on an actual simultaneous receive. -/
theorem profiledRawJointInitialCommonBoth_localChildControls
    (first current : In₁ × In₂) :
    let key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂) := (first, current)
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    (profiledRawJointInitialCommonBothOneReceiveChildControl A strategy first
        current.1 current.2,
      profiledRawJointInitialCommonBothTwoReceiveChildControl A strategy first
        current.2 current.1) =
      (((family.semanticChild A
        (profiledRawJointInitialCommonBothDirection key)).incidenceCode A
          ).family.right,
        ((family.semanticChild A
        (profiledRawJointInitialCommonBothDirection key)).incidenceCode A
          ).family.left) := by
  rfl

/-- Executable finite one-shot transition.  It emits the common physical
output and hands both local processes the same finite child key. -/
def stepProfiledRawJointInitialCommonBoth
    (first current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointInitialCommonBothKey
        (In₁ := In₁) (In₂ := In₂) :=
  (profiledRawJointInitialCommonBothOutput A strategy (first, current),
    (first, current))

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem stepProfiledRawJointInitialCommonBoth_child
    (first current : In₁ × In₂) :
    (stepProfiledRawJointInitialCommonBoth A strategy first current).2 =
      (first, current) :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem stepProfiledRawJointInitialCommonBoth_output
    (first current : In₁ × In₂) :
    (stepProfiledRawJointInitialCommonBoth A strategy first current).1 =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) :=
  rfl

/-! ## Strict/`both` child-control agreement -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- Process one's child family is the same on the strict-left and
simultaneous alternatives of its receive transition. -/
theorem profiledRawJointInitialCommonBoth_childRight_eq_leftActual
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    let direction := profiledRawJointInitialCommonBothDirection key
    (family.semanticChild A direction).right =
      (family.leftActualChild A direction).right := by
  exact ProfiledRawJointSemanticFamily.semanticChild_right_eq_leftActual A _ _

/-- Process-two strict-right/simultaneous mirror. -/
theorem profiledRawJointInitialCommonBoth_childLeft_eq_rightActual
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    let direction := profiledRawJointInitialCommonBothDirection key
    (family.semanticChild A direction).left =
      (family.rightActualChild A direction).left := by
  exact ProfiledRawJointSemanticFamily.semanticChild_left_eq_rightActual A _ _

/-- The finite control installed by process one's local receive is therefore
also exactly the control required by the indistinguishable strict-left exit.
-/
theorem profiledRawJointInitialCommonBoth_oneReceiveChildControl_eq_leftActual
    (first : In₁ × In₂) (own : In₁) (delivered : In₂) :
    let key := profiledRawJointInitialCommonBothKeyOfOneReceive first own
      delivered
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    profiledRawJointInitialCommonBothOneReceiveChildControl A strategy first
        own delivered =
      ((family.leftActualChild A
        (profiledRawJointInitialCommonBothDirection key)).incidenceCode A
          ).family.right := by
  dsimp only [profiledRawJointInitialCommonBothOneReceiveChildControl]
  simp only [ProfiledRawJointSemanticFamily.incidenceCode,
    ProfiledRawJointSemanticFamily.code]
  rw [ProfiledRawJointSemanticFamily.semanticChild_right_eq_leftActual]

/-- Process-two strict-right/simultaneous finite-control agreement. -/
theorem profiledRawJointInitialCommonBoth_twoReceiveChildControl_eq_rightActual
    (first : In₁ × In₂) (own : In₂) (delivered : In₁) :
    let key := profiledRawJointInitialCommonBothKeyOfTwoReceive first own
      delivered
    let family := profiledRawJointInitialCommonBothFamily A strategy key
    profiledRawJointInitialCommonBothTwoReceiveChildControl A strategy first
        own delivered =
      ((family.rightActualChild A
        (profiledRawJointInitialCommonBothDirection key)).incidenceCode A
          ).family.left := by
  dsimp only [profiledRawJointInitialCommonBothTwoReceiveChildControl]
  simp only [ProfiledRawJointSemanticFamily.incidenceCode,
    ProfiledRawJointSemanticFamily.code]
  rw [ProfiledRawJointSemanticFamily.semanticChild_left_eq_rightActual]

end

end

end DetParityAutomaton

end DistributedSynthesis
