/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.BoundedChoice

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable {Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
variable (rank : EnvHistory I₁ I₂ → Rank)
variable (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
variable (wide : 0 < compressionBound I₁ I₂ O₁ O₂ G Q D)

abbrev CertifiedMove := {m : Move I₁ I₂ O₁ O₂ Q D //
  Legal M step (.bounded (compressionBound I₁ I₂ O₁ O₂ G Q D)) m.source m ∧ Faithful M step q₀ σ m}

def initialBounded : CertifiedMove M step q₀ σ (D:=D) := by
  let m := algorithmMove σ (Position.initial q₀ (I₁:=I₁) (I₂:=I₂) (D:=D))
  have legal := component_legal_replacement M step _ m (algorithmMove_legal M step σ _)
  have size : (retained m).card ≤ compressionBound I₁ I₂ O₁ O₂ G Q D := by
    have card : (retained m).card = 1 := by simp [retained,m,algorithmMove,Position.initial]
    rw [card]; exact wide
  refine ⟨m,⟨legal.1,legal.2.1,legal.2.2,size⟩,?_,?_,fun _ => rfl,legal.2.2⟩
  · intro h
    have empty : h.val = [] := Finset.mem_singleton.mp h.property
    change q₀ = _
    rw [empty]; rfl
  · funext n e
    simp only [m,algorithmMove,restrictClosingPolicy,mapClosingLayer_identity]

def chooseBounded (st : CertifiedMove M step q₀ σ (D:=D)) (P : Position I₁ I₂ Q D)
    (next : Next M step st.val P) : CertifiedMove M step q₀ σ (D:=D) := by
  let choice := bounded_successor_choice M step q₀ σ rank holes st.val st.property.2 P next
  exact ⟨choice.choose,⟨rfl,choice.choose_spec.1.2⟩,choice.choose_spec.2.1⟩

theorem chooseBounded_source (st : CertifiedMove M step q₀ σ (D:=D)) (P : Position I₁ I₂ Q D)
    (next : Next M step st.val P) :
    (chooseBounded M step q₀ σ rank holes st P next).val.source = P :=
  (bounded_successor_choice M step q₀ σ rank holes st.val st.property.2 P next).choose_spec.1.1

theorem chooseBounded_progress (st : CertifiedMove M step q₀ σ (D:=D)) (P : Position I₁ I₂ Q D)
    (next : Next M step st.val P) :
    ReplacementProgress step q₀ σ rank st.val (chooseBounded M step q₀ σ rank holes st P next).val :=
  (bounded_successor_choice M step q₀ σ rank holes st.val st.property.2 P next).choose_spec.2.2

def boundedStep (st : CertifiedMove M step q₀ σ (D:=D)) (P : Position I₁ I₂ Q D) : CertifiedMove M step q₀ σ (D:=D) :=
  if next : Next M step st.val P then chooseBounded M step q₀ σ rank holes st P next else st

def boundedState (node : List (Position I₁ I₂ Q D)) : CertifiedMove M step q₀ σ (D:=D) :=
  node.foldl (boundedStep M step q₀ σ rank holes) (initialBounded M step q₀ σ wide)

def boundedTree (node : List (Position I₁ I₂ Q D)) : Move I₁ I₂ O₁ O₂ Q D :=
  (boundedState M step q₀ σ rank holes wide node).val

theorem boundedState_append (node : List (Position I₁ I₂ Q D)) (P : Position I₁ I₂ Q D) :
    boundedState M step q₀ σ rank holes wide (node++[P]) =
      boundedStep M step q₀ σ rank holes (boundedState M step q₀ σ rank holes wide node) P := by
  simp only [boundedState,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem boundedTree_faithful (node : List (Position I₁ I₂ Q D)) :
    Faithful M step q₀ σ (boundedTree M step q₀ σ rank holes wide node) :=
  (boundedState M step q₀ σ rank holes wide node).property.2

theorem boundedTree_legal : SupportedMovesValid (offers M step) (Position.initial q₀)
    (Legal M step (.bounded (compressionBound I₁ I₂ O₁ O₂ G Q D))) (boundedTree M step q₀ σ rank holes wide) := by
  intro node supported
  refine ⟨?_,(boundedState M step q₀ σ rank holes wide node).property.1.2⟩
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node P =>
    have both : publicSupport (offers M step) (boundedTree M step q₀ σ rank holes wide) node = true ∧
        offers M step (boundedTree M step q₀ σ rank holes wide node) P = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    have next : Next M step (boundedTree M step q₀ σ rank holes wide node) P := of_decide_eq_true both.2
    change (boundedState M step q₀ σ rank holes wide (node++[P])).val.source = _
    rw [boundedState_append]
    dsimp only [boundedTree] at next
    simp only [boundedStep,dif_pos next]
    rw [chooseBounded_source]
    simp [observableAt]

theorem boundedTree_progress (node : List (Position I₁ I₂ Q D)) (P : Position I₁ I₂ Q D)
    (next : Next M step (boundedTree M step q₀ σ rank holes wide node) P) :
    ReplacementProgress step q₀ σ rank (boundedTree M step q₀ σ rank holes wide node)
      (boundedTree M step q₀ σ rank holes wide (node++[P])) := by
  change ReplacementProgress step q₀ σ rank _ (boundedState M step q₀ σ rank holes wide (node++[P])).val
  rw [boundedState_append]
  dsimp only [boundedTree] at next
  simp only [boundedStep,dif_pos next]
  exact chooseBounded_progress M step q₀ σ rank holes _ P next
end
end Characterisation.ComponentGames.HistoryGame
