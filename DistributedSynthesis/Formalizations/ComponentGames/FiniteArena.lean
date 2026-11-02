/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteRepresentations
import DistributedSynthesis.Formalizations.ComponentGames.MonitorCompiler

namespace Characterisation.ComponentGames.Representation
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {H J I₁ I₂ O₁ O₂ G Q : Type} {D B : Nat}
variable [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def Components (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (K : Finset (ClosingLayer H I₁ I₂ D)) : Prop :=
  ∃ anchor, liveEnd M a out r anchor = true ∧ ∀ s,
    s ∈ K ↔ closingComponentMask (closingLayerShape a.shape D) (liveEnd M a out r) anchor s = true

instance componentsDecidable (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (K : Finset (ClosingLayer H I₁ I₂ D)) : Decidable (Components M a out r K) := by
  unfold Components; infer_instance

theorem component_nonempty (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (K : Finset (ClosingLayer H I₁ I₂ D)) (component : Components M a out r K) : K.Nonempty := by
  obtain ⟨s,live,mem⟩ := component
  exact ⟨s,(mem s).mpr (by simp [closingComponentMask,live])⟩

theorem component_live (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (K : Finset (ClosingLayer H I₁ I₂ D)) (component : Components M a out r K)
    (s : ClosingLayer H I₁ I₂ D) (mem : s ∈ K) : liveEnd M a out r s = true := by
  obtain ⟨root,_,members⟩ := component
  have mask := (members s).mp mem
  simp only [closingComponentMask,Bool.and_eq_true] at mask
  exact mask.1

theorem components_map (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (K : Finset (ClosingLayer H I₁ I₂ D)) (L : Finset (ClosingLayer J I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L) :
    Components M b (policy e.toEquiv out) (replacement e.toEquiv r) L ↔ Components M a out r K := by
  constructor
  · rintro ⟨j,live,mem⟩
    obtain ⟨h,rfl⟩ := (layerEquiv e.toEquiv D).surjective j
    change liveEnd M b (policy e.toEquiv out) (replacement e.toEquiv r) (mapClosingLayer e.toEquiv D h) = true at live
    change ∀ s, s ∈ L ↔ closingComponentMask (closingLayerShape b.shape D) (liveEnd M b (policy e.toEquiv out) (replacement e.toEquiv r)) (mapClosingLayer e.toEquiv D h) s = true at mem
    refine ⟨h,?_,fun s => ?_⟩
    · simpa only [liveEnd_map] using live
    · rw [members,mem,endComponentMask_map]
  · rintro ⟨h,live,mem⟩
    refine ⟨mapClosingLayer e.toEquiv D h,by simpa only [liveEnd_map] using live,?_⟩
    intro j
    obtain ⟨s,rfl⟩ := (layerEquiv e.toEquiv D).surjective j
    change mapClosingLayer e.toEquiv D s ∈ L ↔ _
    change mapClosingLayer e.toEquiv D s ∈ L ↔ closingComponentMask (closingLayerShape b.shape D) (liveEnd M b (policy e.toEquiv out) (replacement e.toEquiv r)) (mapClosingLayer e.toEquiv D h) (mapClosingLayer e.toEquiv D s) = true
    rw [endComponentMask_map,← members,mem]

/-- No component is discarded by the capacity test of the finite arena. -/
theorem component_card (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (K : Finset (ClosingLayer H I₁ I₂ D)) (component : Components M a out r K) :
    K.card ≤ (Finset.univ.image r).card * Nat.card (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) := by
  let kept := ((Finset.univ.image r) ×ˢ (Finset.univ : Finset (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D))).image
    (blockScenarioEquiv H I₁ I₂ D)
  have subset : K ⊆ kept := by
    intro s mem
    have live := component_live M a out r K component s mem
    have root := (of_decide_eq_true live).1
    exact Finset.mem_image.mpr ⟨(closingLayerRoot D s,scenarioWord D s),
      Finset.mem_product.mpr ⟨root,Finset.mem_univ _⟩,wordScenario_scenarioWord D s⟩
  calc
    K.card ≤ kept.card := Finset.card_le_card subset
    _ ≤ _ := Finset.card_image_le
    _ = _ := by rw [Finset.card_product,Finset.card_univ,Nat.card_eq_fintype_card]

namespace FiniteArena
abbrev Move (I₁ I₂ O₁ O₂ G Q : Type) (D B : Nat) :=
  (P : Position G Q B) × (ClosingPolicy P.Root I₁ I₂ O₁ O₂ D × (P.Root → P.Root))
abbrev Move.source (m : Move I₁ I₂ O₁ O₂ G Q D B) := m.1
abbrev Move.rule (m : Move I₁ I₂ O₁ O₂ G Q D B) := m.2.1
abbrev Move.replacement (m : Move I₁ I₂ O₁ O₂ G Q D B) := m.2.2
abbrev Move.End (m : Move I₁ I₂ O₁ O₂ G Q D B) := ClosingLayer m.source.Root I₁ I₂ D

/-- The move is already public. Echoing it makes the dependent component
carrier an ordinary finite observation type; it reveals no hidden history. -/
abbrev Outcome (I₁ I₂ O₁ O₂ G Q : Type) (D B : Nat) :=
  (m : Move I₁ I₂ O₁ O₂ G Q D B) × Finset m.End
abbrev Observation (I₁ I₂ O₁ O₂ G Q : Type) (D B : Nat) := Option (Outcome I₁ I₂ O₁ O₂ G Q D B)

def initial (q₀ : Q) (positive : 0 < B) : Position G Q B :=
  ⟨⟨1,by omega⟩,⟨fun _ _ _ => true,fun _ => M.start,fun _ => q₀⟩⟩

variable [LinearOrder I₁] [LinearOrder I₂]

def nextPosition (o : Outcome I₁ I₂ O₁ O₂ G Q D B) (bound : o.2.card ≤ B) : Position G Q B :=
  pack o.2 bound (successor M step o.1.source.2 o.1.rule o.2)

def observedPosition (q₀ : Q) (positive : 0 < B) : Observation I₁ I₂ O₁ O₂ G Q D B → Position G Q B
  | none => initial M q₀ positive
  | some o => if bound : o.2.card ≤ B then nextPosition M step o bound else initial M q₀ positive

variable [Fintype G] [Fintype Q]

def Legal (W : Nat) (q₀ : Q) (positive : 0 < B)
    (o : Observation I₁ I₂ O₁ O₂ G Q D B) (m : Move I₁ I₂ O₁ O₂ G Q D B) : Prop :=
  m.source = observedPosition M step q₀ positive o ∧
    (m.rule,m.replacement) ∈ legalMoves m.source.2.shape M m.source.2.graph step m.source.2.state D W

instance legalDecidable (W : Nat) (q₀ : Q) (positive : 0 < B) :
    DecidableRel (Legal (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (D:=D) M step W q₀ positive) := by
  intro o m; unfold Legal; infer_instance

def offers (m : Move I₁ I₂ O₁ O₂ G Q D B) : Observation I₁ I₂ O₁ O₂ G Q D B → Bool
  | none => false
  | some o => decide (o.1 = m ∧ Components M o.1.source.2 o.1.rule o.1.replacement o.2 ∧ o.2.card ≤ B)

theorem offers_component (m : Move I₁ I₂ O₁ O₂ G Q D B) (K : Finset m.End) :
    offers M m (some ⟨m,K⟩) = true ↔ Components M m.source.2 m.rule m.replacement K ∧ K.card ≤ B := by
  simp only [offers,decide_eq_true_eq,true_and]

theorem legal_component_fits (W : Nat) (q₀ : Q) (positive : 0 < B)
    (capacity : W * Nat.card (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) ≤ B)
    (o : Observation I₁ I₂ O₁ O₂ G Q D B) (m : Move I₁ I₂ O₁ O₂ G Q D B)
    (legal : Legal M step W q₀ positive o m) (K : Finset m.End)
    (component : Components M m.source.2 m.rule m.replacement K) : K.card ≤ B := by
  have width := (legalMoves_exact _ M _ step _ D W m.rule m.replacement).mp legal.2
  exact (component_card M _ _ _ K component).trans ((Nat.mul_le_mul_right _ width.2.2).trans capacity)

instance outcomeDecidableEq : DecidableEq (Outcome I₁ I₂ O₁ O₂ G Q D B) := by
  letI : ∀ m : Move I₁ I₂ O₁ O₂ G Q D B, DecidableEq (Finset m.End) := fun m => inferInstance
  infer_instance

end FiniteArena
end Characterisation.ComponentGames.Representation
