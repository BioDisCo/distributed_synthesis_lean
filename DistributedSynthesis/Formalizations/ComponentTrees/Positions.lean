/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.BlockRules
import DistributedSynthesis.Formalizations.ComponentTrees.Compression

/-! The full validity conditions on the positions in `main.tex`. The reused
`HistoryGame.Position` is only a container: it stores a nonempty finite
history family, its common depth, and state labels. The predicates below
add EXACTLY the draft's liveness, induced connectivity, and state
reachability requirements. None of these is inferred from the container.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))

/-- Actual input histories and actual runs of B, with existential outputs.
The witnessing outputs may differ between histories, as permitted in the draft. -/
def StateReachable (h : EnvHistory I₁ I₂) (q : B.State) : Prop :=
  ∃ words : List (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D),
    (words.map (fun w => w.val.map (fun a => envRecordEquiv I₁ I₂ a.1))).flatten = h ∧
      words.foldl B.step B.initial = q

def PositionValid (M : Recognizer Graph G) (P : Position I₁ I₂ B.State D) : Prop :=
  (∀ h : P.Root, M.eval (History.graphSequence h.val) ∈ M.accept) ∧
  (∀ h k : P.Root, Relation.ReflTransGen
    (fun x y : P.Root => ∃ p, currentView p x.val = currentView p y.val) h k) ∧
  ∀ h : P.Root, StateReachable B h.val (P.state h)

theorem initial_position_valid (M : Recognizer Graph G) (live : M.eval [] ∈ M.accept) :
    PositionValid B M (Position.initial (D := D) B.initial) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have eq : h.val = [] := Finset.mem_singleton.mp h.property
    simpa only [eq, History.graphSequence, List.map_nil] using live
  · intro h k
    have eq : h = k := Subtype.ext ((Finset.mem_singleton.mp h.property).trans
      (Finset.mem_singleton.mp k.property).symm)
    rw [eq]
  · intro h
    exact ⟨[], by simpa using (Finset.mem_singleton.mp h.property).symm, rfl⟩

theorem ruleBlock_environment {H : Type} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (s : ClosingLayer H I₁ I₂ D) :
    (ruleBlock out s).val.map (fun a => envRecordEquiv I₁ I₂ a.1) = (scenarioWord D s).val := by
  have env (n : Nat) (within : n ≤ D) (t : ClosingLayer H I₁ I₂ n) :
      (closingLayerTrace out n within t).map (fun a => envRecordEquiv I₁ I₂ a.1) =
        closingLayerHistory (fun _ : H => []) n t := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [closingLayerTrace, List.map_append, List.map_cons, List.map_nil,
        closingLayerHistory, scenarioHistory, ih]
      rfl
  change (closingLayerTrace out D _ s).map _ = _
  rw [env D (Nat.le_refl _), scenarioWord_history]
  rfl

/-- Extending a reachable source state by the prescribed block gives a
reachable endpoint state. This discharges the draft's position invariant. -/
theorem blockSuccessor_reachable (P : Position I₁ I₂ B.State D)
    (out : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D)
    (reachable : ∀ h : P.Root, StateReachable B h.val (P.state h)) (s : P.End) :
    StateReachable B (P.history s) (blockSuccessor B P.state out s) := by
  obtain ⟨words, hist, states⟩ := reachable (closingLayerRoot D s)
  refine ⟨words ++ [ruleBlock out s], ?_, ?_⟩
  · simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, hist, ruleBlock_environment]
    exact (scenarioWord_history P.past D s).symm
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, states]
    rfl

variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (m : Move I₁ I₂ O₁ O₂ B.State D) (K : Finset m.source.End)

/-- Auxiliary image-position construction from the earlier formulation.
The retained endpoints with their ACTUAL block-successor states form a
valid position. In current `main.tex` the child carries the FULL component;
use `component_position` in `ComponentSteps` for that child construction.
Connectivity is internal to the retained set; reachability is proved by
appending the prescribed output block, not assumed for the new position. -/
theorem folded_position
    (valid : PositionValid B M m.source)
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (component : IsComponent M m K)
    (rep : participatingRoots m K → participatingRoots m K)
    (preserves : ∀ h, endpointTable m K (blockSuccessor B m.source.state m.rule) (rep h) =
      endpointTable m K (blockSuccessor B m.source.state m.rule) h)
    (constant : ∀ h k, endpointTable m K (blockSuccessor B m.source.state m.rule) h =
      endpointTable m K (blockSuccessor B m.source.state m.rule) k → rep h = rep k) :
    let label := blockSuccessor B m.source.state m.rule
    let F := endpointFold m K label rep preserves
    ∃ P : Position I₁ I₂ B.State D,
      P.phase = m.source.phase+1 ∧
      P.histories = (Finset.univ.image F).image (fun e : K => m.source.history e.val) ∧
      PositionValid B M P ∧
      (∀ (h : P.Root) (e : K), e ∈ Finset.univ.image F → h.val = m.source.history e.val →
        P.state h = label e.val) ∧
      P.histories.card ≤ (1 + Nat.card B.State) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
        Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  classical
  dsimp only
  let label := blockSuccessor B m.source.state m.rule
  let F := endpointFold m K label rep preserves
  let image := Finset.univ.image F
  let histories := image.image (fun e : K => m.source.history e.val)
  have witnesses (h : histories) : ∃ e, e ∈ image ∧ m.source.history e.val = h.val :=
    Finset.mem_image.mp h.property
  let pick (h : histories) : K := (witnesses h).choose
  have pickMem (h : histories) : pick h ∈ image := (witnesses h).choose_spec.1
  have pickHist (h : histories) : m.source.history (pick h).val = h.val := (witnesses h).choose_spec.2
  have nonempty := endpointFold_image_nonempty m K label rep preserves M component
  let P : Position I₁ I₂ B.State D :=
    { phase := m.source.phase+1
      histories := histories
      nonempty := by
        obtain ⟨e, he⟩ := nonempty
        exact ⟨_, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      lengths := by
        intro h mem
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp mem
        exact m.source.history_length e.val
      state := fun h => label (pick h).val }
  let toHist (e : image) : P.Root := ⟨m.source.history e.val.val,
    Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩⟩
  have pickEq (h : P.Root) : toHist ⟨pick h, pickMem h⟩ = h := Subtype.ext (pickHist h)
  refine ⟨P, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨anchor, alive, mask⟩ := component
    have inside := (mask (pick h).val).mp (pick h).property
    simp only [closingComponentMask, Bool.and_eq_true] at inside
    have live := (of_decide_eq_true inside.1).2
    simpa only [pickHist h] using live
  · intro h k
    have path := endpointFold_image_connected m K label rep preserves M holes component
      ⟨pick h, pickMem h⟩ ⟨pick k, pickMem k⟩
    rw [← pickEq h, ← pickEq k]
    exact Relation.ReflTransGen.lift toHist (fun _ _ edge => edge) path
  · intro h
    change StateReachable B h.val (label (pick h).val)
    rw [← pickHist h]
    exact blockSuccessor_reachable B m.source m.rule valid.2.2 (pick h).val
  · intro h e _ eq
    have chosen : pick h = e := Subtype.ext (m.source.history_injective ((pickHist h).trans eq))
    change label (pick h).val = label e.val
    rw [chosen]
  · exact Finset.card_image_le.trans (endpointFold_image_bound m K label rep preserves constant)

/-- The same position construction under the ORIGINAL consensus premise,
including singleton application input alphabets. There is no additional
missing-extension hypothesis at this endpoint. -/
theorem folded_position_of_consensus {V : Type} [Nontrivial V]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      ComponentGames.Consensus.SolvesBy σ (Residual A u) D)
    (valid : PositionValid B M m.source)
    (component : IsComponent M m K)
    (rep : participatingRoots m K → participatingRoots m K)
    (preserves : ∀ h, endpointTable m K (blockSuccessor B m.source.state m.rule) (rep h) =
      endpointTable m K (blockSuccessor B m.source.state m.rule) h)
    (constant : ∀ h k, endpointTable m K (blockSuccessor B m.source.state m.rule) h =
      endpointTable m K (blockSuccessor B m.source.state m.rule) k → rep h = rep k) :
    let label := blockSuccessor B m.source.state m.rule
    let F := endpointFold m K label rep preserves
    ∃ P : Position I₁ I₂ B.State D,
      P.phase = m.source.phase+1 ∧
      P.histories = (Finset.univ.image F).image (fun e : K => m.source.history e.val) ∧
      PositionValid B M P ∧
      (∀ (h : P.Root) (e : K), e ∈ Finset.univ.image F → h.val = m.source.history e.val →
        P.state h = label e.val) ∧
      P.histories.card ≤ (1 + Nat.card B.State) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
        Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  have holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept := by
    intro h
    obtain ⟨u, len, missing⟩ := ComponentGames.Consensus.repeated_consensus_exact_holes
      A D positive consensus h
    exact ⟨u, len, fun live => missing ((recognizes _).mpr live)⟩
  exact folded_position B M m K valid holes component rep preserves constant

end
end Characterisation.ComponentTrees
