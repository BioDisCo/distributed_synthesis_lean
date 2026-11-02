/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.Representatives
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusHoles

/-! Endpoint-table algebra used by the component-tree proof in `main.tex`.

Unlike `HistoryGame.componentKey`, these tables contain ONLY membership in
the selected endpoint component and the endpoint label. In particular there
is no equality assumption on the old labels or on the distributed rules.
`Move`, `Position`, `ClosingLayer`, and actual input histories are reused.
The move's replacement field is irrelevant to the algebra below; for the
extension of an already selected source graph it is `id`.

The `*_of_consensus` endpoints below use the geometric common-view proof.
The manuscript correspondence uses `compression_reduction` in
`ComponentSteps`, which follows the broadcaster proof and returns an
actual vertex map.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ Q B G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
variable (label : m.source.End → B)

/-- The draft's `Θ_h^{C'}`; `none` covers both nonlive endpoints and
endpoints in another component. `B` is the combined block-state type. -/
def endpointTable (h : participatingRoots m K) :
    BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Option B :=
  fun u => if wordScenario h.val u ∈ K then some (label (wordScenario h.val u)) else none

variable (rep : participatingRoots m K → participatingRoots m K)
variable (preserves : ∀ h, endpointTable m K label (rep h) = endpointTable m K label h)

include preserves in
theorem table_entry (h : participatingRoots m K)
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (mem : wordScenario h.val u ∈ K) :
    wordScenario (rep h).val u ∈ K ∧
      label (wordScenario (rep h).val u) = label (wordScenario h.val u) := by
  classical
  have eq := congrFun (preserves h) u
  simp only [endpointTable, if_pos mem] at eq
  split at eq
  · exact ⟨‹_›, Option.some.inj eq⟩
  · cases eq

/-- The endpoint fold `hu ↦ ρ(h)u`, after the component has been fixed. -/
def endpointFold (e : K) : K :=
  ⟨wordScenario (rep (rootOf m K e)).val (scenarioWord D e.val),
    (table_entry m K label rep preserves (rootOf m K e) (scenarioWord D e.val)
      (by simpa only [rootOf, wordScenario_scenarioWord] using e.property)).1⟩

@[simp] theorem endpointFold_root (e : K) :
    rootOf m K (endpointFold m K label rep preserves e) = rep (rootOf m K e) := by
  apply Subtype.ext
  exact wordScenario_root _ _

@[simp] theorem endpointFold_word (e : K) :
    scenarioWord D (endpointFold m K label rep preserves e).val = scenarioWord D e.val :=
  scenarioWord_wordScenario _ _

theorem endpointFold_history (e : K) :
    m.source.history (endpointFold m K label rep preserves e).val =
      (rep (rootOf m K e)).val.val ++ (scenarioWord D e.val).val :=
  wordScenario_history m.source.past _ _

theorem endpointFold_label (e : K) :
    label (endpointFold m K label rep preserves e).val = label e.val := by
  have eq := (table_entry m K label rep preserves (rootOf m K e) (scenarioWord D e.val)
    (by simpa only [rootOf, wordScenario_scenarioWord] using e.property)).2
  simpa only [endpointFold, rootOf, wordScenario_scenarioWord] using eq

theorem endpointFold_priority (χ : B → Nat) (e : K) :
    χ (label (endpointFold m K label rep preserves e).val) = χ (label e.val) :=
  congrArg χ (endpointFold_label m K label rep preserves e)

variable (constant : ∀ h k, endpointTable m K label h = endpointTable m K label k → rep h = rep k)

include constant in
theorem endpointFold_idempotent (e : K) :
    endpointFold m K label rep preserves (endpointFold m K label rep preserves e) =
      endpointFold m K label rep preserves e := by
  apply Subtype.ext
  change wordScenario _ _ = wordScenario _ _
  rw [endpointFold_root, endpointFold_word,
    arbitrary_representative_idempotent _ rep preserves constant]

/-- The exact number of endpoint tables is `(1+|Q|)^(|Σ|^D)`.
This is not the larger bound from the game construction. -/
theorem endpointTable_card [Fintype B] :
    Nat.card (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Option B) =
      (1 + Nat.card B) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) := by
  rw [Nat.card_fun, blockWord_card]
  simp [Nat.card_eq_fintype_card, Nat.add_comm]

include constant in
theorem endpointFold_image_bound [Fintype B] :
    (Finset.univ.image (endpointFold m K label rep preserves)).card ≤
      (1 + Nat.card B) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
        Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  classical
  let image := Finset.univ.image (endpointFold m K label rep preserves)
  let code (e : image) := (endpointTable m K label (rootOf m K e.val), scenarioWord D e.val.val)
  have fixed (e : image) : endpointFold m K label rep preserves e.val = e.val := by
    obtain ⟨x, _, eq⟩ := Finset.mem_image.mp e.property
    rw [← eq]
    exact endpointFold_idempotent m K label rep preserves constant x
  have rootFixed (e : image) : rep (rootOf m K e.val) = rootOf m K e.val := by
    have h := congrArg (rootOf m K) (fixed e)
    simpa only [endpointFold_root] using h
  have injective : Function.Injective code := by
    intro e f eq
    have roots := (rootFixed e).symm.trans ((constant _ _ (congrArg Prod.fst eq)).trans (rootFixed f))
    have words := congrArg Prod.snd eq
    apply Subtype.ext
    apply Subtype.ext
    rw [← wordScenario_scenarioWord D e.val.val, ← wordScenario_scenarioWord D f.val.val]
    exact congrArg₂ (fun h w => wordScenario (n := D) h w) (congrArg Subtype.val roots) words
  have bound := Nat.card_le_card_of_injective code injective
  rw [Nat.card_prod, endpointTable_card, blockWord_card] at bound
  have cardImage : Nat.card image = image.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
  rw [cardImage] at bound
  exact bound

variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- With the identity replacement, the reused endpoint enumeration is
EXACTLY the draft's full live extension set. No old game replacement is
performed before λ. This is the intended instantiation of `Move` here. -/
theorem extensionLive_identity (P : Position I₁ I₂ Q D)
    (out : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D) (e : P.End) :
    extensionLive M (⟨P, out, id⟩ : Move I₁ I₂ O₁ O₂ Q D) e =
      decide (M.eval (History.graphSequence (P.history e)) ∈ M.accept) := by
  simp [extensionLive, retained]

/-- Forward preservation of both process views, from the existing
bounded-common-view and view-extension proofs. The table need not record
the source state, the source graph-recognizer state, or any output. -/
theorem endpointFold_views
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (component : IsComponent M m K) (p : Proc) (e f : K)
    (same : currentView p (m.source.history e.val) = currentView p (m.source.history f.val)) :
    currentView p (m.source.history (endpointFold m K label rep preserves e).val) =
      currentView p (m.source.history (endpointFold m K label rep preserves f).val) := by
  obtain ⟨leader, common⟩ := participating_roots_common M holes m K component
  rw [endpointFold_history, endpointFold_history]
  apply arbitrary_representative_views (fun i : participatingRoots m K => i.val.val)
    (fun _ _ eq => Subtype.ext (Subtype.ext eq)) leader common
    (endpointTable m K label) rep (rootOf m K e) (rootOf m K f)
    (scenarioWord D e.val).val (scenarioWord D f.val).val
    ((scenarioWord D e.val).property.trans (scenarioWord D f.val).property.symm) p
  simpa only [Position.history, scenarioWord_history, Position.past, rootOf] using same

theorem endpointFold_image_nonempty (component : IsComponent M m K) :
    (Finset.univ.image (endpointFold m K label rep preserves)).Nonempty := by
  classical
  obtain ⟨anchor, alive, mask⟩ := component
  have mem : anchor ∈ K := (mask anchor).mpr (by
    simp only [closingComponentMask, alive, Bool.true_and, decide_eq_true_eq]
    exact SimpleGraph.Reachable.refl anchor)
  exact ⟨_, Finset.mem_image.mpr ⟨⟨anchor, mem⟩, Finset.mem_univ _, rfl⟩⟩

/-- The image is connected USING ONLY RETAINED ENDPOINTS. Merely proving
connectivity in the larger live-history graph would be too weak here. -/
theorem endpointFold_image_connected
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (component : IsComponent M m K) :
    let image := Finset.univ.image (endpointFold m K label rep preserves)
    ∀ x y : image, Relation.ReflTransGen
      (fun a b : image => ∃ p, currentView p (m.source.history a.val.val) =
        currentView p (m.source.history b.val.val)) x y := by
  classical
  dsimp only
  let image := Finset.univ.image (endpointFold m K label rep preserves)
  let f (e : K) : image := ⟨endpointFold m K label rep preserves e,
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩
  intro x y
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp x.property
  obtain ⟨g, _, hg⟩ := Finset.mem_image.mp y.property
  have xe : x = f e := Subtype.ext he.symm
  have yg : y = f g := Subtype.ext hg.symm
  rw [xe, yg]
  obtain ⟨anchor, alive, mask⟩ := component
  have ee := (mask e.val).mp e.property
  have gg := (mask g.val).mp g.property
  simp only [closingComponentMask, Bool.and_eq_true, decide_eq_true_eq] at ee gg
  let graph := closingObservationGraph (closingLayerShape m.source.shape D) (extensionLive M m)
  have reach : graph.Reachable e.val g.val := ee.2.symm.trans gg.2
  have path := (graph.reachable_iff_reflTransGen e.val g.val).mp reach
  have go : ∀ (z : m.source.End), Relation.ReflTransGen graph.Adj e.val z →
      ∀ hz : z ∈ K, Relation.ReflTransGen
        (fun a b : image => ∃ p, currentView p (m.source.history a.val.val) =
          currentView p (m.source.history b.val.val)) (f e) (f ⟨z, hz⟩) := by
    intro z path
    induction path with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail b c path edge ih =>
      have hb : b ∈ K := (mask b).mpr (by
        simp only [closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨edge.2.1, ee.2.trans ((graph.reachable_iff_reflTransGen _ _).mpr path)⟩)
      intro hc
      apply (ih hb).tail
      have exactShape := closingLayerShape_exact m.source.past m.source.shape
        (extractInputShape_exact m.source.past) D
      obtain ⟨p, same | same⟩ := edge.2.2.2
      · exact ⟨p, endpointFold_views m K label rep preserves M holes
          ⟨anchor, alive, mask⟩ p ⟨b, hb⟩ ⟨c, hc⟩ ((exactShape p b c).mp same)⟩
      · exact ⟨p, endpointFold_views m K label rep preserves M holes
          ⟨anchor, alive, mask⟩ p ⟨b, hb⟩ ⟨c, hc⟩ ((exactShape p c b).mp same).symm⟩
  exact go g.val path g.property

/-- The draft's additional branching bound `|E| ≤ |C| |Σ|^D`.
No bound on the source component is silently assumed. -/
theorem live_endpoints_bound (L : Nat) (small : m.source.histories.card ≤ L) :
    (extensions M m).card ≤ L * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  classical
  have equiv : m.source.End ≃ m.source.Root × BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D :=
    { toFun := fun e => (closingLayerRoot D e, scenarioWord D e)
      invFun := fun x => wordScenario x.1 x.2
      left_inv := wordScenario_scenarioWord D
      right_inv := fun x => Prod.ext (wordScenario_root _ _) (scenarioWord_wordScenario _ _) }
  have count : Nat.card m.source.End =
      m.source.histories.card * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
    rw [Nat.card_congr equiv, Nat.card_prod, blockWord_card]
    congr 1
    exact Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
  calc
    (extensions M m).card ≤ (Finset.univ.filter (fun e => extensionLive M m e = true)).card :=
      Finset.card_image_le
    _ ≤ Fintype.card m.source.End := Finset.card_le_univ _
    _ = Nat.card m.source.End := Nat.card_eq_fintype_card.symm
    _ ≤ L * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
      rw [count]; exact Nat.mul_le_mul_right _ small

/-- Restore the paper's consensus hypothesis. The exact-depth missing
extension premise of the geometric library is DERIVED, not added to the
draft as a new assumption. `V` is the fresh proposal alphabet, independent
of the application input alphabets (which may be singletons). -/
theorem endpointFold_views_of_consensus {V : Type} [Nontrivial V]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      ComponentGames.Consensus.SolvesBy σ (Residual A u) D)
    (component : IsComponent M m K) (p : Proc) (e f : K)
    (same : currentView p (m.source.history e.val) = currentView p (m.source.history f.val)) :
    currentView p (m.source.history (endpointFold m K label rep preserves e).val) =
      currentView p (m.source.history (endpointFold m K label rep preserves f).val) := by
  have holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept := by
    intro h
    obtain ⟨u, len, missing⟩ := ComponentGames.Consensus.repeated_consensus_exact_holes
      A D positive consensus h
    exact ⟨u, len, fun live => missing ((recognizes _).mpr live)⟩
  exact endpointFold_views m K label rep preserves M holes component p e f same

/-- A single statement collecting the local geometric and counting
conclusions of `lem:tree-compression`. Labels may be any block successor
states; equality of old states or rules is deliberately absent. -/
theorem endpoint_compression [Fintype B] {V : Type} [Nontrivial V]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      ComponentGames.Consensus.SolvesBy σ (Residual A u) D)
    (component : IsComponent M m K)
    (constant : ∀ h k, endpointTable m K label h = endpointTable m K label k → rep h = rep k) :
    let F := endpointFold m K label rep preserves
    let image := Finset.univ.image F
    (∀ e, F (F e) = F e) ∧
    (∀ p (e f : K), currentView p (m.source.history e.val) = currentView p (m.source.history f.val) →
      currentView p (m.source.history (F e).val) = currentView p (m.source.history (F f).val)) ∧
    (∀ e, label (F e).val = label e.val) ∧
    image.Nonempty ∧
    (∀ x y : image, Relation.ReflTransGen
      (fun a b : image => ∃ p, currentView p (m.source.history a.val.val) =
        currentView p (m.source.history b.val.val)) x y) ∧
    image.card ≤ (1 + Nat.card B) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
      Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  have holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept := by
    intro h
    obtain ⟨u, len, missing⟩ := ComponentGames.Consensus.repeated_consensus_exact_holes
      A D positive consensus h
    exact ⟨u, len, fun live => missing ((recognizes _).mpr live)⟩
  exact ⟨endpointFold_idempotent m K label rep preserves constant,
    endpointFold_views m K label rep preserves M holes component,
    endpointFold_label m K label rep preserves,
    endpointFold_image_nonempty m K label rep preserves M component,
    endpointFold_image_connected m K label rep preserves M holes component,
    endpointFold_image_bound m K label rep preserves constant⟩

end
end Characterisation.ComponentTrees
