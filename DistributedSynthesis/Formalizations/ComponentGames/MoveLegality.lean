/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReplay
import DistributedSynthesis.Library.Distributed.LeaderPhases.ActiveClosingRoots

/- The manuscript adds replacement-before-extension moves that do not occur
literally in the existing block game. This module supplies their finite
checks using the EXISTING ClosingLayer, ClosingPolicy, input shapes and replay.
It does not identify the two games without a proof. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 1200000

theorem mapClosingLayer_comp {H J K I₁ I₂ : Type}
    (f : H → J) (g : J → K) (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    mapClosingLayer g n (mapClosingLayer f n s) = mapClosingLayer (g ∘ f) n s := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih s.1) rfl

theorem mapClosingLayer_idempotent {H I₁ I₂ : Type} (r : H → H)
    (idem : ∀ h, r (r h) = r h) (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    mapClosingLayer r n (mapClosingLayer r n s) = mapClosingLayer r n s := by
  rw [mapClosingLayer_comp]
  have eq : r ∘ r = r := funext idem
  rw [eq]

-- This checks all intermediate states, including the initial and final one.
-- The original next-phase rule is arbitrary; it need not come from a winner.
theorem pulled_back_state_preservation {H I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (r : H → H) (idem : ∀ h, r (r h) = r h)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q)
    (same : ∀ h, q (r h) = q h) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step q (restrictClosingPolicy r out) n bound (mapClosingLayer r n s) =
      closingLayerLabels step q (restrictClosingPolicy r out) n bound s := by
  have start : q ∘ r = q := funext same
  have replay (x : ClosingLayer H I₁ I₂ n) :
      closingLayerLabels step q (restrictClosingPolicy r out) n bound x =
        closingLayerLabels step q out n bound (mapClosingLayer r n x) := by
    simpa only [start] using closingLayerLabels_restrict r step q out n bound x
  rw [replay, replay, mapClosingLayer_idempotent r idem]

-- Shape homomorphisms extend through all suffixes, on actual history roots.
theorem mapped_layer_views {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (r : H → H)
    (preserves : ∀ p h k, currentView p (past h) = currentView p (past k) →
      currentView p (past (r h)) = currentView p (past (r k)))
    (n : Nat) (p : Proc) (s t : ClosingLayer H I₁ I₂ n)
    (eq : currentView p (closingLayerHistory past n s) =
      currentView p (closingLayerHistory past n t)) :
    currentView p (closingLayerHistory past n (mapClosingLayer r n s)) =
      currentView p (closingLayerHistory past n (mapClosingLayer r n t)) := by
  induction n generalizing p with
  | zero => exact preserves p s t eq
  | succ n ih =>
    exact append_round_preserves_views _ _ _ _
      (fun p same => ih p s.1 t.1 same)
      ⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩
      ⟨t.2.1,t.2.2.1,t.2.2.2,(),()⟩ p eq

theorem pulled_back_rule_distributed {H I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (exactShape : RepresentsInputShape past shape) (r : H → H)
    (preserves : ∀ p h k, currentView p (past h) = currentView p (past k) →
      currentView p (past (r h)) = currentView p (past (r k)))
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (distributed : ClosingPolicyCoherent shape out) :
    ClosingPolicyCoherent shape (restrictClosingPolicy r out) := by
  intro n
  have exactLayer := closingLayerShape_exact past shape exactShape (n.val+1)
  constructor
  · intro s t eq
    apply (distributed n).1
    apply (exactLayer .one _ _).mpr
    exact mapped_layer_views past r preserves _ .one s t ((exactLayer .one s t).mp eq)
  · intro s t eq
    apply (distributed n).2
    apply (exactLayer .two _ _).mpr
    exact mapped_layer_views past r preserves _ .two s t ((exactLayer .two s t).mp eq)

-- Literal finite checks for the paper's legal replacement (not the earlier
-- library game's different post-extension response).
def ReplacementChecks {H I₁ I₂ O₁ O₂ G Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H) (M : Recognizer Graph G) (graph : H → G)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q)
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) : Prop :=
  (∀ p (s t : ClosingLayer H I₁ I₂ D), closingLayerShape shape D p s t = true →
    closingLayerShape shape D p (mapClosingLayer r D s) (mapClosingLayer r D t) = true) ∧
  (∀ (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val),
    closingLayerLabels (fun g e _ => M.step g e.2.2) graph out n.val (by omega) s =
      closingLayerLabels (fun g e _ => M.step g e.2.2) graph out n.val (by omega)
        (mapClosingLayer r n.val s) ∧
    closingLayerLabels step q out n.val (by omega) s =
      closingLayerLabels step q out n.val (by omega) (mapClosingLayer r n.val s))

instance replacementChecks_decidable {H I₁ I₂ O₁ O₂ G Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq G] [DecidableEq Q]
    (shape : InputShape H) (M : Recognizer Graph G) (graph : H → G)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q)
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) :
    Decidable (ReplacementChecks shape M graph step q out r) := by
  unfold ReplacementChecks
  infer_instance

def legalMoves {H I₁ I₂ O₁ O₂ G Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]
    (shape : InputShape H) (M : Recognizer Graph G) (graph : H → G)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q) (D W : Nat) :
    Finset (ClosingPolicy H I₁ I₂ O₁ O₂ D × (H → H)) :=
  Finset.univ.filter (fun move => ClosingPolicyCoherent shape move.1 ∧
    ReplacementChecks shape M graph step q move.1 move.2 ∧
    (Finset.univ.image move.2).card ≤ W)

theorem pulled_back_move_legal {H I₁ I₂ O₁ O₂ G Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (exactShape : RepresentsInputShape past shape)
    (M : Recognizer Graph G) (graph : H → G)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q)
    (r : H → H) (idem : ∀ h, r (r h) = r h)
    (preserves : ∀ p h k, currentView p (past h) = currentView p (past k) →
      currentView p (past (r h)) = currentView p (past (r k)))
    (graphSame : ∀ h, graph (r h) = graph h) (qSame : ∀ h, q (r h) = q h)
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (distributed : ClosingPolicyCoherent shape out) :
    ClosingPolicyCoherent shape (restrictClosingPolicy r out) ∧
    ReplacementChecks shape M graph step q (restrictClosingPolicy r out) r := by
  refine ⟨pulled_back_rule_distributed past shape exactShape r preserves out distributed, ?_, ?_⟩
  · intro p s t eq
    have exactLayer := closingLayerShape_exact past shape exactShape D
    exact (exactLayer p _ _).mpr
      (mapped_layer_views past r preserves D p s t ((exactLayer p s t).mp eq))
  · intro n s
    exact ⟨(pulled_back_state_preservation r idem (fun g e _ => M.step g e.2.2)
      graph graphSame out n.val (by omega) s).symm,
      (pulled_back_state_preservation r idem step q qSame out n.val (by omega) s).symm⟩

theorem legalMoves_exact {H I₁ I₂ O₁ O₂ G Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]
    (shape : InputShape H) (M : Recognizer Graph G) (graph : H → G)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q) (D W : Nat)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) :
    (out,r) ∈ legalMoves shape M graph step q D W ↔
      ClosingPolicyCoherent shape out ∧ ReplacementChecks shape M graph step q out r ∧
      (Finset.univ.image r).card ≤ W := by
  simp only [legalMoves,Finset.mem_filter,Finset.mem_univ,true_and]

end Characterisation.ComponentGames

