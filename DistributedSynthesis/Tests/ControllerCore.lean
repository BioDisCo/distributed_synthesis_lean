/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.MealyControllers

/-! Standalone clients of controller types and their timing bridge, without
the physical-round or finite-memory synthesis adapters. -/
namespace DistributedSynthesis.Tests.ControllerCore
open DistributedSynthesis

universe u v x y c₁ c₂
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

example (C : FinitePairedPhysicalController.{u,v,x,y,c₁,c₂} In₁ In₂ Out₁ Out₂)
    (s : C.OneControl × C.TwoControl) (i : In₁) (j : In₂) :
    C.advanceControls s ⟨i,j,.both⟩ =
      (C.recvOne s.1 i s.2 j, C.recvTwo s.2 j s.1 i) :=
  C.advanceControls_both s i j

example (C : FinitePairedMealyController.{u,v,x,y,c₁,c₂} In₁ In₂ Out₁ Out₂)
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (s : C.mooreize.OneControl) (i : In₁)
    (r : C.mooreize.TwoControl) (j : In₂) :
    C.mooreize.outputOne (C.mooreize.recvOne s i r j) =
      (C.recvOne s.1 i r.1 j).2 :=
  C.mooreize_recvOne_output s i r j

/-- An example finite controller, constructed using only the lightweight API. -/
def echo : FinitePairedMealyController Bool Bool Bool Bool where
  OneControl := Unit
  TwoControl := Unit
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := ()
  initialTwo := ()
  noRecvOne := fun _ i => ((), i)
  noRecvTwo := fun _ j => ((), j)
  recvOne := fun _ i _ _ => ((), i)
  recvTwo := fun _ j _ _ => ((), j)

example : (echo.recvOne () true () false).2 = true := rfl
example : (echo.noRecvTwo () false).2 = false := rfl

end DistributedSynthesis.Tests.ControllerCore
