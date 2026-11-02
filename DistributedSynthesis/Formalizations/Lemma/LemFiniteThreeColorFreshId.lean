/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDelayedBitResolver

/-!
# Three finite colors suffice for a fresh delayed-receive identifier

At a simultaneous round, the two endpoints must install one common identifier
which is different from either unresolved identifier delivered from the old
carriers.  There are at most two such forbidden identifiers, so `Fin 3`
suffices.

The selector below is executable and uses only the two optional identifiers
carried by the delivered finite controls.  It does not inspect a graph,
orientation, leader bit, view, or history.
-/

namespace DistributedSynthesis

/-- Choose a color which is absent from the two optional old fork IDs.

The order `0`, then `1`, then `2` merely makes the choice canonical. -/
def freshDelayedForkColor
    (left right : Option (Fin 3)) : Fin 3 :=
  if left ≠ some 0 ∧ right ≠ some 0 then
    0
  else if left ≠ some 1 ∧ right ≠ some 1 then
    1
  else
    2

/-- Both receivers compute the same new color although they see the old
carriers in opposite local order. -/
theorem freshDelayedForkColor_comm
    (left right : Option (Fin 3)) :
    freshDelayedForkColor left right = freshDelayedForkColor right left := by
  simp only [freshDelayedForkColor, and_comm]

@[simp] theorem freshDelayedForkColor_none_none :
    freshDelayedForkColor none none = 0 := by
  rfl

/-- The selected color is different from every ID present on the left. -/
theorem freshDelayedForkColor_ne_left
    (left right : Option (Fin 3)) (id : Fin 3)
    (hleft : left = some id) :
    freshDelayedForkColor left right ≠ id := by
  subst left
  fin_cases id <;>
    cases right with
    | none => simp [freshDelayedForkColor]
    | some rightId => fin_cases rightId <;> simp [freshDelayedForkColor]

/-- The selected color is different from every ID present on the right. -/
theorem freshDelayedForkColor_ne_right
    (left right : Option (Fin 3)) (id : Fin 3)
    (hright : right = some id) :
    freshDelayedForkColor left right ≠ id := by
  subst right
  fin_cases id <;>
    cases left with
    | none => simp [freshDelayedForkColor]
    | some leftId => fin_cases leftId <;> simp [freshDelayedForkColor]

/-- Convenient left-side specialization when the optional ID is visibly
present. -/
@[simp] theorem freshDelayedForkColor_some_left_ne
    (left : Fin 3) (right : Option (Fin 3)) :
    freshDelayedForkColor (some left) right ≠ left :=
  freshDelayedForkColor_ne_left (some left) right left rfl

/-- Convenient right-side specialization when the optional ID is visibly
present. -/
@[simp] theorem freshDelayedForkColor_some_right_ne
    (left : Option (Fin 3)) (right : Fin 3) :
    freshDelayedForkColor left (some right) ≠ right :=
  freshDelayedForkColor_ne_right left (some right) right rfl

end DistributedSynthesis
