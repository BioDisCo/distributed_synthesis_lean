/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Sigma.Order

/-! Computable comparison of finite tables and finite sets. These orders
are opt-in via `open scoped DistributedSynthesis.FiniteOrders`; importing
this module does not replace the standard pointwise product/function orders.
The underlying types are Mathlib's `Fintype`, `Finset`, `List`, and `Equiv`.
The generic Pi lexicographic order in Mathlib is noncomputable, so the finite
case uses a sorted list of domain elements to compute comparisons. -/
namespace DistributedSynthesis.FiniteOrders
def functionCode {X Y : Type} [Fintype X] [LinearOrder X] (f : X → Y) : List Y :=
  (Finset.univ.sort (· ≤ ·)).map f

theorem functionCode_injective {X Y : Type} [Fintype X] [LinearOrder X] :
    Function.Injective (functionCode (X:=X) (Y:=Y)) := by
  intro f g eq
  funext x
  exact List.map_inj_left.mp eq x (by simp)

scoped instance functionOrder {X Y : Type} [Fintype X] [LinearOrder X] [LinearOrder Y] : LinearOrder (X → Y) :=
  LinearOrder.lift' functionCode functionCode_injective

scoped instance productOrder {X Y : Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (X × Y) :=
  LinearOrder.lift' toLex (fun _ _ eq => eq)

scoped instance sigmaOrder {X : Type} {Y : X → Type} [LinearOrder X] [∀ x, LinearOrder (Y x)] : LinearOrder (Sigma Y) :=
  LinearOrder.lift' toLex (fun _ _ eq => eq)

scoped instance optionOrder {X : Type} [LinearOrder X] : LinearOrder (Option X) :=
  inferInstanceAs (LinearOrder (WithBot X))

scoped instance finsetOrder {X : Type} [LinearOrder X] : LinearOrder (Finset X) :=
  LinearOrder.lift' (fun s : Finset X => s.sort (· ≤ ·)) (by
    intro a b eq
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset eq)


end DistributedSynthesis.FiniteOrders
