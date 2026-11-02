/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecidableViews
import DistributedSynthesis.Formalizations.ComponentGames.ArenaController
import DistributedSynthesis.Formalizations.ComponentGames.SimulationRuns

namespace Characterisation.ComponentGames.ExecutableHistories
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

def shape {H I₁ I₂ : Type} [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) : InputShape H :=
  fun p h k => decide (currentView p (past h) = currentView p (past k))

theorem shape_eq {H I₁ I₂ : Type} [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) : shape past = extractInputShape past := by
  funext p h k
  apply Bool.eq_iff_iff.mpr
  rw [shape,decide_eq_true_eq]
  exact (extractInputShape_exact past p h k).symm

deriving instance DecidableEq for HistoryGame.Position

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

instance componentDecidable (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End) :
    Decidable (HistoryGame.IsComponent M m K) := by
  letI : Fintype m.source.End := inferInstance
  letI : DecidableEq m.source.End := inferInstance
  unfold HistoryGame.IsComponent HistoryGame.Position.shape
  rw [← shape_eq]
  infer_instance

instance nextDecidable (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (P : HistoryGame.Position I₁ I₂ Q D) :
    Decidable (HistoryGame.Next M step m P) := by
  unfold HistoryGame.Next
  infer_instance

def offers (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (P : HistoryGame.Position I₁ I₂ Q D) : Bool :=
  decide (HistoryGame.Next M step m P)

theorem offers_eq : offers (D:=D) M step = HistoryGame.offers M step := by
  funext m P
  apply Bool.eq_iff_iff.mpr
  simp only [offers,HistoryGame.offers,decide_eq_true_eq]

def recoverComponent (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step m P) : Finset m.source.End :=
  Fintype.choose (fun K : Finset m.source.End => P.histories = K.image m.source.history) (by
    obtain ⟨_,K,_,histories,_⟩ := next
    exact ⟨K,histories,fun L eq => Finset.image_injective m.source.history_injective (eq.symm.trans histories)⟩)

theorem recoverComponent_spec (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step m P) : P.histories = (recoverComponent M step m P next).image m.source.history := by
  unfold recoverComponent
  exact Fintype.choose_spec (fun K : Finset m.source.End => P.histories = K.image m.source.history) _

theorem recoverComponent_eq (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step m P) : recoverComponent M step m P next = next.2.choose :=
  Finset.image_injective m.source.history_injective
    ((recoverComponent_spec M step m P next).symm.trans next.2.choose_spec.2.1)

end Characterisation.ComponentGames.ExecutableHistories
