/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ComponentRoots
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingRestrictionCorrect

/- Arbitrary representatives of the exact previous-block key. The previous
and next rules are arbitrary distributed tables, not restrictions of a
previously chosen winning strategy. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1800000

variable {H I₁ I₂ O₁ O₂ Q G : Type} {D : Nat}

def policyCode (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (h : H)
    (u : BlockPrefix (RoundRecord I₁ I₂ Graph Unit Unit) D) : O₁ × O₂ :=
  let n : Fin D := ⟨u.val.length-1, by have := u.property; omega⟩
  let word : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (n.val+1) :=
    ⟨u.val,by have := u.property; dsimp [n]; omega⟩
  out n (wordScenario h word)

theorem policyCode_word (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (h : H)
    (n : Fin D) (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (n.val+1)) :
    policyCode out h ⟨u.val,by rw [u.property]; omega,by rw [u.property]; omega⟩ =
      out n (wordScenario h u) := by
  rcases n with ⟨n,hn⟩
  rcases u with ⟨w,hw⟩
  change w.length = n+1 at hw
  have eq : w.length-1 = n := by omega
  subst n
  rfl

theorem policyCode_scenario (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)) :
    policyCode out (closingLayerRoot (n.val+1) s)
      ⟨(scenarioWord (n.val+1) s).val,
       by rw [(scenarioWord (n.val+1) s).property]; omega,
       by rw [(scenarioWord (n.val+1) s).property]; omega⟩ = out n s := by
  rw [policyCode_word,wordScenario_scenarioWord]

theorem scenarioWord_map (f : H → H) (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    scenarioWord n (mapClosingLayer f n s) = scenarioWord n s := by
  simp only [scenarioWord,EncodedClosingRestriction.word_map]

/-- Equal key entries suffice for the previous-block replay, even when the
initial labels were assigned by earlier replacements. -/
theorem policyCode_replay
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (q : H → Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (i j : H) (initial : q i = q j) (rules : policyCode out i = policyCode out j)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n)
    (root : closingLayerRoot n s = i) :
    closingLayerLabels step q out n bound s =
      closingLayerLabels step q out n bound (mapClosingLayer (fun _ => j) n s) := by
  induction n with
  | zero =>
    change s = i at root
    subst s
    exact initial
  | succ n ih =>
    have outputs : out ⟨n,by omega⟩ s = out ⟨n,by omega⟩ (mapClosingLayer (fun _ => j) (n+1) s) := by
      rw [← policyCode_scenario out ⟨n,by omega⟩ s,
        ← policyCode_scenario out ⟨n,by omega⟩ (mapClosingLayer (fun _ => j) (n+1) s)]
      simp only [closingLayerRoot_map,scenarioWord_map,root,rules]
    simp only [closingLayerLabels,mapClosingLayer]
    rw [ih (by omega) s.1 root, outputs]
    rfl

section Component
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)

abbrev Key := BlockType G Q (BlockPrefix (RoundRecord I₁ I₂ Graph Unit Unit) D)
  (O₁ × O₂) (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)

def componentKey (i : participatingRoots m K) : Key (I₁:=I₁) (I₂:=I₂) (O₁:=O₁) (O₂:=O₂) (Q:=Q) (G:=G) (D:=D) :=
  ⟨M.eval (History.graphSequence i.val.val),m.source.state i.val,
    policyCode m.rule i.val, fun w => @decide (wordScenario i.val w ∈ K) (Classical.propDecidable _)⟩

def rootOf (e : K) : participatingRoots m K :=
  ⟨closingLayerRoot D e.val,Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩⟩

variable (rep : participatingRoots m K → participatingRoots m K)
variable (preserves : ∀ i, componentKey M m K (rep i) = componentKey M m K i)

def fold (e : K) : K :=
  ⟨wordScenario (rep (rootOf m K e)).val (scenarioWord D e.val),by
    have same := congrArg (fun t => t.suffixes (scenarioWord D e.val)) (preserves (rootOf m K e))
    have original : (componentKey M m K (rootOf m K e)).suffixes (scenarioWord D e.val) = true := by
      simpa only [componentKey,rootOf,wordScenario_scenarioWord,decide_eq_true_eq] using e.property
    have folded := same.trans original
    simpa only [componentKey,decide_eq_true_eq] using folded⟩

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
@[simp] theorem fold_root (e : K) :
    rootOf m K (fold M m K rep preserves e) = rep (rootOf m K e) := by
  apply Subtype.ext
  exact wordScenario_root _ _

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
@[simp] theorem fold_word (e : K) :
    scenarioWord D (fold M m K rep preserves e).val = scenarioWord D e.val :=
  scenarioWord_wordScenario _ _

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem fold_history (e : K) :
    m.source.history (fold M m K rep preserves e).val =
      (rep (rootOf m K e)).val.val ++ (scenarioWord D e.val).val :=
  wordScenario_history m.source.past _ _

variable (constant : ∀ i j, componentKey M m K i = componentKey M m K j → rep i = rep j)

include constant in
omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem fold_idempotent (e : K) :
    fold M m K rep preserves (fold M m K rep preserves e) = fold M m K rep preserves e := by
  apply Subtype.ext
  change wordScenario _ _ = wordScenario _ _
  rw [fold_root,fold_word,arbitrary_representative_idempotent _ rep preserves constant]

/-- The folding map on the selected component preserves both processes'
views. It is independent of any particular choice of representatives. -/
theorem fold_views
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (component : IsComponent M m K) (p : Proc) (e f : K)
    (same : currentView p (m.source.history e.val) = currentView p (m.source.history f.val)) :
    currentView p (m.source.history (fold M m K rep preserves e).val) =
      currentView p (m.source.history (fold M m K rep preserves f).val) := by
  obtain ⟨leader,common⟩ := participating_roots_common M holes m K component
  rw [fold_history,fold_history]
  apply arbitrary_representative_views (fun i : participatingRoots m K => i.val.val)
    (fun _ _ eq => Subtype.ext (Subtype.ext eq)) leader common
    (componentKey M m K) rep (rootOf m K e) (rootOf m K f)
    (scenarioWord D e.val).val (scenarioWord D f.val).val
    ((scenarioWord D e.val).property.trans (scenarioWord D f.val).property.symm) p
  simpa only [Position.history,scenarioWord_history,Position.past,rootOf] using same

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem fold_graph (e : K) :
    M.eval (History.graphSequence (m.source.history (fold M m K rep preserves e).val)) =
      M.eval (History.graphSequence (m.source.history e.val)) := by
  rw [fold_history]
  change _ = M.eval (History.graphSequence (closingLayerHistory m.source.past D e.val))
  rw [scenarioWord_history]
  apply graph_recognizer_replay
  exact congrArg BlockType.graphState (preserves (rootOf m K e))

omit [Fintype I₁] [Fintype I₂] [DecidablePred (· ∈ M.accept)] in
theorem fold_state (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (e : K) :
    closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) (fold M m K rep preserves e).val =
      closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e.val := by
  have same := preserves (rootOf m K e)
  have replay := policyCode_replay step m.source.state m.rule
    (rootOf m K e).val (rep (rootOf m K e)).val
    (congrArg BlockType.objectiveState same).symm
    (congrArg BlockType.rule same).symm D (Nat.le_refl D) e.val rfl
  have mapped : mapClosingLayer (fun _ => (rep (rootOf m K e)).val) D e.val =
      (fold M m K rep preserves e).val := by
    rw [← wordScenario_scenarioWord D (mapClosingLayer _ D e.val),closingLayerRoot_map,scenarioWord_map]
    rfl
  rw [mapped] at replay
  exact replay.symm

include constant in
omit [DecidablePred (· ∈ M.accept)] in
theorem fold_image_bound [Fintype G] [Fintype Q] [Fintype O₁] [Fintype O₂] :
    (Finset.univ.image (fold M m K rep preserves)).card ≤
      (Nat.card G * Nat.card Q *
        Nat.card (O₁ × O₂) ^ (∑ t : Fin D, Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ (t.val+1)) *
        2 ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D)) *
      Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  classical
  let image := Finset.univ.image (fold M m K rep preserves)
  let code (e : image) := (componentKey M m K (rootOf m K e.val),scenarioWord D e.val.val)
  have fixed (e : image) : fold M m K rep preserves e.val = e.val := by
    obtain ⟨x,_,eq⟩ := Finset.mem_image.mp e.property
    rw [← eq]
    exact fold_idempotent M m K rep preserves constant x
  have rootFixed (e : image) : rep (rootOf m K e.val) = rootOf m K e.val := by
    have h := congrArg (rootOf m K) (fixed e)
    simpa only [fold_root] using h
  have injective : Function.Injective code := by
    intro e f eq
    have roots := (rootFixed e).symm.trans ((constant _ _ (congrArg Prod.fst eq)).trans (rootFixed f))
    have words := congrArg Prod.snd eq
    apply Subtype.ext
    apply Subtype.ext
    rw [← wordScenario_scenarioWord D e.val.val,← wordScenario_scenarioWord D f.val.val]
    exact congrArg₂ (fun h w => wordScenario (n:=D) h w) (congrArg Subtype.val roots) words
  have bound := Nat.card_le_card_of_injective code injective
  rw [Nat.card_prod,blockType_card_exact,blockWord_card] at bound
  have cardImage : Nat.card image = image.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
  rw [cardImage] at bound
  exact bound

/-- The canonical bijection with the actual next position. -/
def componentEquiv (P : Position I₁ I₂ Q D) (histories : P.histories = K.image m.source.history) :
    K ≃ P.Root := Equiv.ofBijective
      (fun e : K => ⟨m.source.history e.val,by change _ ∈ P.histories; rw [histories]; exact Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩⟩)
      ⟨fun _ _ eq => Subtype.ext (m.source.history_injective (congrArg Subtype.val eq)), by
        intro h
        have mem : h.val ∈ K.image m.source.history := by rw [← histories]; exact h.property
        obtain ⟨e,he,eq⟩ := Finset.mem_image.mp mem
        exact ⟨⟨e,he⟩,Subtype.ext eq⟩⟩

/-- Transporting a self-map along a bijection preserves its image size. -/
theorem conjugate_image_card {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (f : A → A) :
    (Finset.univ.image (fun b => e (f (e.symm b)))).card = (Finset.univ.image f).card := by
  classical
  have same : Finset.univ.image (fun b => e (f (e.symm b))) = (Finset.univ.image f).image e := by
    ext b
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,rfl⟩; exact ⟨f (e.symm a),⟨e.symm a,rfl⟩,rfl⟩
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩; exact ⟨e a,by rw [e.symm_apply_apply]⟩
  rw [same,Finset.card_image_of_injective _ e.injective]

/-- Full local conclusion of the paper's representative lemma, for an
arbitrary previous move and its actual selected successor, with arbitrary
representatives and arbitrary new distributed rule. -/
theorem bounded_representative_move [Fintype G] [Fintype Q] [Fintype O₁] [Fintype O₂]
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (P : Position I₁ I₂ Q D) (component : IsComponent M m K)
    (histories : P.histories = K.image m.source.history)
    (labels : ∀ (h : P.Root) (e : m.source.End), e ∈ K → h.val = m.source.history e →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e)
    (out : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D) (distributed : ClosingPolicyCoherent P.shape out)
    (constant : ∀ i j, componentKey M m K i = componentKey M m K j → rep i = rep j) :
    let e := componentEquiv m K P histories
    let r := fun h => e (fold M m K rep preserves (e.symm h))
    ClosingPolicyCoherent P.shape (restrictClosingPolicy r out) ∧
      ReplacementChecks P.shape M (fun h => M.eval (History.graphSequence h.val))
        step P.state (restrictClosingPolicy r out) r ∧
      (Finset.univ.image r).card ≤
        (Nat.card G * Nat.card Q *
          Nat.card (O₁ × O₂) ^ (∑ t : Fin D, Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ (t.val+1)) *
          2 ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D)) *
        Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  classical
  dsimp only
  let e := componentEquiv m K P histories
  let r := fun h => e (fold M m K rep preserves (e.symm h))
  have idem : ∀ h, r (r h) = r h := by
    intro h
    dsimp only [r]
    rw [e.symm_apply_apply,fold_idempotent M m K rep preserves constant]
  have views : ∀ p h k, currentView p (P.past h) = currentView p (P.past k) →
      currentView p (P.past (r h)) = currentView p (P.past (r k)) := by
    intro p h k same
    obtain ⟨h,rfl⟩ := e.surjective h
    obtain ⟨k,rfl⟩ := e.surjective k
    dsimp only [r]
    rw [e.symm_apply_apply,e.symm_apply_apply]
    exact fold_views M m K rep preserves holes component p h k same
  have graphSame : ∀ h, M.eval (History.graphSequence (r h).val) = M.eval (History.graphSequence h.val) := by
    intro h
    obtain ⟨h,rfl⟩ := e.surjective h
    dsimp only [r]
    rw [e.symm_apply_apply]
    exact fold_graph M m K rep preserves h
  have stateSame : ∀ h, P.state (r h) = P.state h := by
    intro h
    obtain ⟨h,rfl⟩ := e.surjective h
    dsimp only [r]
    rw [e.symm_apply_apply,
      labels (e (fold M m K rep preserves h)) _ (fold M m K rep preserves h).property rfl,
      labels (e h) _ h.property rfl]
    exact fold_state M m K rep preserves step h
  have legal := pulled_back_move_legal P.past P.shape (extractInputShape_exact P.past)
    M (fun h => M.eval (History.graphSequence h.val)) step P.state r idem views graphSame stateSame out distributed
  refine ⟨legal.1,legal.2,?_⟩
  rw [conjugate_image_card e]
  exact fold_image_bound M m K rep preserves constant

end Component



end
end Characterisation.ComponentGames.HistoryGame



