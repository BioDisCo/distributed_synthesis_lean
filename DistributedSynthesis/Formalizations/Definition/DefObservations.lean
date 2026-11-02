/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# Observations and information order

This file formalizes the definitions of full and non-fringe observations and of
the induced information order from `paper.tex`.
-/

namespace DistributedSynthesis

universe u v x y

/-- The full indistinguishability relation induced by the current full view. -/
def FullIndistinguishable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h h' : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  currentView p h = currentView p h'

/-- The non-fringe indistinguishability relation induced by the current non-fringe view. -/
def NonFringeIndistinguishable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h h' : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  currentNonFringe p h = currentNonFringe p h'

/-- The current receipt tag of process `p` after history `h`. -/
def currentReceiptTag
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂) : ReceiptTag :=
  (currentView p h).receiptTag

/-- Set-theoretic inclusion between two history relations. -/
def RelationIncluded
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (R S : History In₁ In₂ Graph Out₁ Out₂ -> History In₁ In₂ Graph Out₁ Out₂ -> Prop) : Prop :=
  ∀ ⦃h h' : History In₁ In₂ Graph Out₁ Out₂⦄, R h h' -> S h h'

/-- Process `j` has at least as much non-fringe information as process `i`. -/
def HasAtLeastAsMuchNonFringeInformation
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (i j : Proc) : Prop :=
  @RelationIncluded In₁ In₂ Out₁ Out₂
    (@NonFringeIndistinguishable In₁ In₂ Out₁ Out₂ j)
    (@NonFringeIndistinguishable In₁ In₂ Out₁ Out₂ i)

@[simp]
theorem fullIndistinguishable_iff
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h h' : History In₁ In₂ Graph Out₁ Out₂) :
    FullIndistinguishable p h h' ↔ currentView p h = currentView p h' := by
  rfl

@[simp]
theorem nonFringeIndistinguishable_iff
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h h' : History In₁ In₂ Graph Out₁ Out₂) :
    NonFringeIndistinguishable p h h' ↔ currentNonFringe p h = currentNonFringe p h' := by
  rfl

end DistributedSynthesis
