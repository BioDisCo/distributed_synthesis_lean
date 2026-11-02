/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReadback

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

abbrev BlockPosition (I₁ I₂ : Type) (D : Nat) :=
  List (BlockInput I₁ I₂ D) × (Σ t : Fin D, BlockInput I₁ I₂ (t.val+1))

def positionHistory {I₁ I₂ : Type} {D : Nat} (x : BlockPosition I₁ I₂ D) : EnvHistory I₁ I₂ :=
  blockHistory x.1 ++ x.2.2.val

theorem position_time_eq {I₁ I₂ : Type} {D : Nat} (x y : BlockPosition I₁ I₂ D)
    (p : Proc) (same : currentView p (positionHistory x) = currentView p (positionHistory y)) :
    x.1.length = y.1.length ∧ x.2.1 = y.2.1 := by
  have adjacent : InputAdjacent (positionHistory x) (positionHistory y) := by
    cases p <;> [exact Or.inl same; exact Or.inr same]
  have len := adjacent_same_depth (inputAdjacent_projects adjacent)
  have equation : x.1.length*D + (x.2.1.val+1) = y.1.length*D + (y.2.1.val+1) := by
    simpa only [History.graphSequence, List.length_map, positionHistory, List.length_append,
      blockHistory_length, x.2.2.property, y.2.2.property] using len
  have lx := x.2.1.isLt
  have ly := y.2.1.isLt
  have blocks : x.1.length = y.1.length := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have le := Nat.mul_le_mul_right D (Nat.succ_le_of_lt lt)
      simp only [Nat.succ_mul] at le
      omega
    · have le := Nat.mul_le_mul_right D (Nat.succ_le_of_lt gt)
      simp only [Nat.succ_mul] at le
      omega
  refine ⟨blocks,Fin.ext ?_⟩
  rw [blocks] at equation
  omega

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D))
variable (legal : SupportedMovesValid (blockOffers M step) (initialBlockOutcome M q₀ B D)
  (fun outcome move => BlockMoveValid M step outcome.target move) tree)
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)

def positionOutput (x : BlockPosition I₁ I₂ D) : O₁ × O₂ :=
  let state := blockMachine M step tree x.1
  (tree state.1).policy x.2.1 (wordScenario state.2 x.2.2)

include legal closed recognizes in
theorem blockPrefix_local (words other : List (BlockInput I₁ I₂ D)) (lengths : words.length = other.length)
    (t : Fin D) (u v : BlockInput I₁ I₂ (t.val+1))
    (live : P (History.graphSequence (blockHistory words ++ u.val)))
    (otherLive : P (History.graphSequence (blockHistory other ++ v.val)))
    (p : Proc) (same : currentView p (blockHistory words ++ u.val) = currentView p (blockHistory other ++ v.val)) :
    (blockMachine M step tree words).1 = (blockMachine M step tree other).1 ∧
      currentView p (closingLayerHistory (virtualFamily tree (blockMachine M step tree words).1)
        (t.val+1) (wordScenario (blockMachine M step tree words).2 u)) =
      currentView p (closingLayerHistory (virtualFamily tree (blockMachine M step tree words).1)
        (t.val+1) (wordScenario (blockMachine M step tree other).2 v)) := by
  have leftLive : P (History.graphSequence (blockHistory words)) := by
    apply closed _ (History.graphSequence u.val)
    simpa only [History.graphSequence,List.map_append] using live
  have rightLive : P (History.graphSequence (blockHistory other)) := by
    apply closed _ (History.graphSequence v.val)
    simpa only [History.graphSequence,List.map_append] using otherLive
  have oldSame : currentView p (blockHistory words) = currentView p (blockHistory other) := by
    have lu := lagView_suffix p (blockHistory words) u.val
    have lv := lagView_suffix p (blockHistory other) v.val
    rw [u.property] at lu
    rw [v.property] at lv
    exact lu.symm.trans ((congrArg (lagView (t.val+1)) same).trans lv)
  have nodes := (blockMachine_local M step tree q₀ legal P closed recognizes words other lengths
    leftLive rightLive p oldSame).1
  refine ⟨nodes,?_⟩
  rw [wordScenario_history,wordScenario_history]
  apply append_preserves_views _ _ _ _ _ u.val v.val (u.property.trans v.property.symm) p same
  intro q eq
  have result := (blockMachine_local M step tree q₀ legal P closed recognizes words other lengths
    leftLive rightLive q eq).2
  rwa [← nodes] at result

include legal closed recognizes in
theorem positionOutput_local (x y : BlockPosition I₁ I₂ D)
    (live : P (History.graphSequence (positionHistory x)))
    (otherLive : P (History.graphSequence (positionHistory y))) (p : Proc)
    (same : currentView p (positionHistory x) = currentView p (positionHistory y)) :
    match p with
    | .one => (positionOutput M step tree x).1 = (positionOutput M step tree y).1
    | .two => (positionOutput M step tree x).2 = (positionOutput M step tree y).2 := by
  obtain ⟨lengths,times⟩ := position_time_eq x y p same
  rcases x with ⟨words,t,u⟩
  rcases y with ⟨other,s,v⟩
  dsimp only at times
  subst s
  obtain ⟨nodes,views⟩ := blockPrefix_local M step q₀ tree legal P closed recognizes
    words other lengths t u v live otherLive p same
  have parentLive : P (History.graphSequence (blockHistory words)) := by
    apply closed _ (History.graphSequence u.val)
    simpa only [positionHistory, History.graphSequence,List.map_append] using live
  have supported := (blockMachine_supported M step tree q₀ legal P closed recognizes words parentLive).1
  have rep := (virtualFamily_exact M step tree q₀ legal _ supported).1
  have coherent := (legal _ supported).2.1 t
  have shapeEq := (closingLayerShape_exact _ _ rep (t.val+1) p _ _).mpr views
  dsimp only [positionOutput]
  rw [← nodes]
  cases p
  · exact coherent.1 _ _ shapeEq
  · exact coherent.2 _ _ shapeEq

include legal closed recognizes in
/-- Every legal public block controller has one distributed implementation
on all live histories. Compatibility is proved across different public
histories and across all block positions. -/
theorem blockController_strategy [Nonempty O₁] [Nonempty O₂] :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ x : BlockPosition I₁ I₂ D,
      P (History.graphSequence (positionHistory x)) →
      (σ.one (currentView .one (positionHistory x)), σ.two (currentView .two (positionHistory x))) =
        positionOutput M step tree x := by
  let X := {x : BlockPosition I₁ I₂ D // P (History.graphSequence (positionHistory x))}
  let hist (x : X) := positionHistory x.val
  let out (x : X) := positionOutput M step tree x.val
  have coherent : ShapeCoherent (extractInputShape hist) out := by
    constructor
    · intro x y eq
      exact positionOutput_local M step q₀ tree legal P closed recognizes x.val y.val x.property y.property .one
        ((extractInputShape_exact hist .one x y).mp eq)
    · intro x y eq
      exact positionOutput_local M step q₀ tree legal P closed recognizes x.val y.val x.property y.property .two
        ((extractInputShape_exact hist .two x y).mp eq)
  obtain ⟨σ,correct⟩ := (shapeCoherent_iff_local hist _ (extractInputShape_exact hist) out).mp coherent
  refine ⟨σ, fun x live => ?_⟩
  exact Prod.ext (correct ⟨x,live⟩).1 (correct ⟨x,live⟩).2

end
end Characterisation.PeriodicBlocks
