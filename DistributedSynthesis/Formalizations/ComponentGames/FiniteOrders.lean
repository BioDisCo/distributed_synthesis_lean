/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteProduct
import DistributedSynthesis.Library.Computability.FiniteOrders

/- Computable orders are used only to select a table from a finite search.
They add no order assumption to the histories or their view relations. -/
namespace Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

scoped instance procOrder : LinearOrder Proc :=
  LinearOrder.lift' (fun p : Proc => match p with | .one => (0 : Fin 2) | .two => 1)
    (by intro p q eq; cases p <;> cases q <;> simp_all)

open Representation
scoped instance dataOrder {H G Q : Type} [Fintype H] [LinearOrder H] [LinearOrder G] [LinearOrder Q] :
    LinearOrder (Data H G Q) := LinearOrder.lift' dataEquiv dataEquiv.injective

variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [LinearOrder H] [LinearOrder I₁] [LinearOrder I₂]
variable [LinearOrder O₁] [LinearOrder O₂]

/-- A closing policy is the existing dependent function type. Curry/uncurry
identifies it with a table on the finite disjoint union of its domains. -/
scoped instance policyOrder : LinearOrder (ClosingPolicy H I₁ I₂ O₁ O₂ D) :=
  LinearOrder.lift' (Equiv.piCurry (fun (n : Fin D) (_ : ClosingLayer H I₁ I₂ (n.val+1)) => O₁ × O₂)).symm
    (Equiv.piCurry (fun (n : Fin D) (_ : ClosingLayer H I₁ I₂ (n.val+1)) => O₁ × O₂)).symm.injective

end Characterisation.ComponentGames.FiniteEnumeration
