/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockGame

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
set_option maxSynthPendingDepth 16

def initialBlockBoundary {G Q : Type} (M : Recognizer Graph G) (q₀ : Q) (B : Nat) :
    BlockBoundary G Q B := ⟨fun _ _ _ => true, fun _ => M.start, fun _ => q₀⟩

def initialBlockOutcome {I₁ I₂ G Q : Type} (M : Recognizer Graph G) (q₀ : Q) (B D : Nat) :
    BlockOutcome I₁ I₂ G Q B D := ⟨fun _ => false, initialBlockBoundary M q₀ B⟩

abbrev BlockInput (I₁ I₂ : Type) (D : Nat) := BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D

def blockHistory {I₁ I₂ : Type} {D : Nat} (words : List (BlockInput I₁ I₂ D)) : EnvHistory I₁ I₂ :=
  words.flatMap Subtype.val

@[simp] theorem blockHistory_nil {I₁ I₂ : Type} {D : Nat} :
    blockHistory ([] : List (BlockInput I₁ I₂ D)) = [] := rfl

@[simp] theorem blockHistory_append {I₁ I₂ : Type} {D : Nat}
    (words : List (BlockInput I₁ I₂ D)) (u : BlockInput I₁ I₂ D) :
    blockHistory (words++[u]) = blockHistory words ++ u.val := by simp [blockHistory]

theorem blockHistory_length {I₁ I₂ : Type} {D : Nat} (words : List (BlockInput I₁ I₂ D)) :
    List.length (blockHistory words) = words.length * D := by
  induction words with
  | nil => simp
  | cons u words ih =>
    change List.length (u.val ++ blockHistory words) = (words.length+1)*D
    rw [List.length_append, u.property, ih]
    simp [Nat.add_mul, Nat.add_comm]

section Families
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D))

def virtualFamily (node : List (BlockOutcome I₁ I₂ G Q B D)) : BlockSlots B → EnvHistory I₁ I₂ :=
  node.reverseRecOn (fun _ => []) (fun node outcome past =>
    closingLayerHistory past D ∘ ((tree node).response outcome.component).keep)

@[simp] theorem virtualFamily_nil (i : BlockSlots B) : virtualFamily tree [] i = [] := by simp [virtualFamily]

@[simp] theorem virtualFamily_append (node : List (BlockOutcome I₁ I₂ G Q B D))
    (outcome : BlockOutcome I₁ I₂ G Q B D) :
    virtualFamily tree (node++[outcome]) =
      closingLayerHistory (virtualFamily tree node) D ∘ ((tree node).response outcome.component).keep := by
  simp only [virtualFamily, List.reverseRecOn_concat]

theorem virtualFamily_length (node : List (BlockOutcome I₁ I₂ G Q B D)) (i : BlockSlots B) :
    List.length (virtualFamily tree node i) = node.length * D := by
  induction node using List.reverseRecOn generalizing i with
  | nil => simp
  | append_singleton node outcome ih =>
    rw [virtualFamily_append]
    change List.length (closingLayerHistory (virtualFamily tree node) D _) = _
    rw [closingLayerHistory_length _ _ ih]
    simp [Nat.add_mul]

end Families

section Machine
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D))

def blockMachine (words : List (BlockInput I₁ I₂ D)) :
    List (BlockOutcome I₁ I₂ G Q B D) × BlockSlots B :=
  words.reverseRecOn ([],0) (fun _ u state =>
    let e := wordScenario state.2 u
    let outcome := actualBlockOutcome M step (tree state.1) e
    (state.1++[outcome], ((tree state.1).response outcome.component).fold e))

@[simp] theorem blockMachine_nil : blockMachine M step tree [] = ([],0) := by simp [blockMachine]

@[simp] theorem blockMachine_append (words : List (BlockInput I₁ I₂ D)) (u : BlockInput I₁ I₂ D) :
    blockMachine M step tree (words++[u]) =
      let state := blockMachine M step tree words
      let e := wordScenario state.2 u
      let outcome := actualBlockOutcome M step (tree state.1) e
      (state.1++[outcome], ((tree state.1).response outcome.component).fold e) := by
  simp only [blockMachine, List.reverseRecOn_concat]

theorem blockMachine_length (words : List (BlockInput I₁ I₂ D)) :
    (blockMachine M step tree words).1.length = words.length := by
  induction words using List.reverseRecOn with
  | nil => simp
  | append_singleton words u ih => simp [blockMachine_append, ih]

variable [DecidableEq G] [DecidableEq Q]
variable (q₀ : Q)
variable (legal : SupportedMovesValid (blockOffers M step) (initialBlockOutcome M q₀ B D)
  (fun outcome move => BlockMoveValid M step outcome.target move) tree)

include legal in
theorem virtualFamily_exact (node : List (BlockOutcome I₁ I₂ G Q B D))
    (supported : publicSupport (blockOffers M step) tree node = true) :
    RepresentsInputShape (virtualFamily tree node) (tree node).source.shape ∧
      ∀ i, (tree node).source.graph i = M.eval (History.graphSequence (virtualFamily tree node i)) := by
  induction node using List.reverseRecOn with
  | nil =>
    have source := (legal [] supported).1
    change (tree []).source = initialBlockBoundary M q₀ B at source
    rw [source]
    constructor
    · intro p i j; simp [initialBlockBoundary]
    · intro i; simp [initialBlockBoundary, Recognizer.eval, Recognizer.evalFrom, History.graphSequence]
  | append_singleton node outcome ih =>
    have parts : publicSupport (blockOffers M step) tree node = true ∧
        blockOffers M step (tree node) outcome = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    obtain ⟨rep,graphs⟩ := ih parts.1
    have target : outcome.target = blockTarget M step (tree node) outcome.component :=
      ((of_decide_eq_true parts.2) : _ ∧ _).1
    have source := (legal (node++[outcome]) supported).1
    have last : (observableAt (initialBlockOutcome M q₀ B D) (node++[outcome])).target = outcome.target := by
      simp [observableAt]
    rw [last,target] at source
    rw [source,virtualFamily_append]
    exact ⟨blockTarget_shape M step (tree node) (virtualFamily tree node) rep outcome.component,
      blockTarget_graph M step (tree node) (virtualFamily tree node) outcome.component graphs⟩

variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)

include legal closed recognizes in
theorem blockMachine_supported (words : List (BlockInput I₁ I₂ D))
    (live : P (History.graphSequence (blockHistory words))) :
    publicSupport (blockOffers M step) tree (blockMachine M step tree words).1 = true ∧
    M.eval (History.graphSequence (virtualFamily tree (blockMachine M step tree words).1
      (blockMachine M step tree words).2)) = M.eval (History.graphSequence (blockHistory words)) := by
  induction words using List.reverseRecOn with
  | nil => simp
  | append_singleton words u ih =>
    have parentLive : P (History.graphSequence (blockHistory words)) := by
      apply closed _ (History.graphSequence u.val)
      simpa only [blockHistory_append, History.graphSequence, List.map_append] using live
    obtain ⟨supported,graphSame⟩ := ih parentLive
    let state := blockMachine M step tree words
    let move := tree state.1
    let e := wordScenario state.2 u
    let outcome := actualBlockOutcome M step move e
    obtain ⟨rep,graphs⟩ := virtualFamily_exact M step tree q₀ legal state.1 supported
    have endpointGraph : blockEndGraph M move e = M.eval (History.graphSequence (blockHistory (words++[u]))) := by
      rw [blockEndGraph, closingLayerLabels_recognizer M _ _ graphs, wordScenario_history, blockHistory_append]
      exact graph_recognizer_replay M _ _ u.val graphSame
    have endpointLive : blockEndLive M move e = true := by
      unfold blockEndLive
      rw [endpointGraph, decide_eq_true_eq]
      exact (recognizes _).mp live
    have offered : blockOffers M step move outcome = true :=
      actualBlockOutcome_offered M step move e endpointLive
    have response := (legal state.1 supported).2.2 e endpointLive
    have inside := (blockComponent_self M move e).trans endpointLive
    have kept := (response.2.2 e inside).1
    rw [blockMachine_append]
    constructor
    · simpa only [publicSupport_append, supported, Bool.true_and] using offered
    · change M.eval (History.graphSequence (virtualFamily tree (state.1++[outcome])
        ((move.response outcome.component).fold e))) = _
      rw [virtualFamily_append]
      change M.eval (History.graphSequence (closingLayerHistory (virtualFamily tree state.1) D _)) = _
      rw [← closingLayerLabels_recognizer M _ _ graphs move.policy D (Nat.le_refl _)]
      exact kept.trans endpointGraph

include legal closed recognizes in
theorem blockMachine_endpoint_live (words : List (BlockInput I₁ I₂ D)) (u : BlockInput I₁ I₂ D)
    (live : P (History.graphSequence (blockHistory (words++[u])))) :
    blockEndLive M (tree (blockMachine M step tree words).1)
      (wordScenario (blockMachine M step tree words).2 u) = true := by
  have parentLive : P (History.graphSequence (blockHistory words)) := by
    apply closed _ (History.graphSequence u.val)
    simpa only [blockHistory_append, History.graphSequence, List.map_append] using live
  obtain ⟨supported,same⟩ := blockMachine_supported M step tree q₀ legal P closed recognizes words parentLive
  obtain ⟨_,graphs⟩ := virtualFamily_exact M step tree q₀ legal _ supported
  unfold blockEndLive blockEndGraph
  rw [closingLayerLabels_recognizer M _ _ graphs, wordScenario_history,
    graph_recognizer_replay M _ _ u.val same, decide_eq_true_eq]
  exact (recognizes _).mp (by simpa only [blockHistory_append] using live)

include legal closed recognizes in
/-- Equal actual local views give the same public game node and equal
virtual local views. Thus the finite fold never supplies hidden information
to either process. -/
theorem blockMachine_local (words other : List (BlockInput I₁ I₂ D))
    (lengths : words.length = other.length)
    (live : P (History.graphSequence (blockHistory words)))
    (otherLive : P (History.graphSequence (blockHistory other)))
    (p : Proc) (same : currentView p (blockHistory words) = currentView p (blockHistory other)) :
    (blockMachine M step tree words).1 = (blockMachine M step tree other).1 ∧
      currentView p (virtualFamily tree (blockMachine M step tree words).1 (blockMachine M step tree words).2) =
      currentView p (virtualFamily tree (blockMachine M step tree other).1 (blockMachine M step tree other).2) := by
  induction words using List.reverseRecOn generalizing other p with
  | nil =>
    have empty : other = [] := List.length_eq_zero_iff.mp (by simpa using lengths.symm)
    subst other
    exact ⟨rfl,rfl⟩
  | append_singleton words u ih =>
    cases other using List.reverseRecOn with
    | nil => simp at lengths
    | append_singleton other v =>
      have len : words.length = other.length := by simpa using lengths
      have leftLive : P (History.graphSequence (blockHistory words)) := by
        apply closed _ (History.graphSequence u.val)
        simpa only [blockHistory_append, History.graphSequence, List.map_append] using live
      have rightLive : P (History.graphSequence (blockHistory other)) := by
        apply closed _ (History.graphSequence v.val)
        simpa only [blockHistory_append, History.graphSequence, List.map_append] using otherLive
      have oldSame : currentView p (blockHistory words) = currentView p (blockHistory other) := by
        have eq := congrArg (lagView D) same
        simp only [blockHistory_append] at eq
        have lu := lagView_suffix p (blockHistory words) u.val
        have lv := lagView_suffix p (blockHistory other) v.val
        rw [u.property] at lu
        rw [v.property] at lv
        exact lu.symm.trans (eq.trans lv)
      obtain ⟨nodes,_⟩ := ih other len leftLive rightLive p oldSame
      let left := blockMachine M step tree words
      let right := blockMachine M step tree other
      have roots : ∀ q, currentView q (blockHistory words) = currentView q (blockHistory other) →
          currentView q (virtualFamily tree left.1 left.2) = currentView q (virtualFamily tree left.1 right.2) := by
        intro q eq
        have result := (ih other len leftLive rightLive q eq).2
        rw [← nodes] at result
        exact result
      have extended := append_preserves_views _ _ _ _ roots u.val v.val
        (u.property.trans v.property.symm) p (by simpa only [blockHistory_append] using same)
      have supported := (blockMachine_supported M step tree q₀ legal P closed recognizes words leftLive).1
      have rep := (virtualFamily_exact M step tree q₀ legal left.1 supported).1
      let move := tree left.1
      let e := wordScenario left.2 u
      let f := wordScenario right.2 v
      have equalViews : currentView p (closingLayerHistory (virtualFamily tree left.1) D e) =
          currentView p (closingLayerHistory (virtualFamily tree left.1) D f) := by
        simpa only [e,f,wordScenario_history] using extended
      have liveE : blockEndLive M move e = true :=
        blockMachine_endpoint_live M step tree q₀ legal P closed recognizes words u live
      have liveF : blockEndLive M move f = true := by
        have result := blockMachine_endpoint_live M step tree q₀ legal P closed recognizes other v otherLive
        rw [← nodes] at result
        exact result
      have masks := blockComponent_eq_of_views M move e f liveE liveF p
        ((blockEndShape_exact move _ rep p e f).mpr equalViews)
      have outcomes : actualBlockOutcome M step move e = actualBlockOutcome M step move f := by
        simp only [actualBlockOutcome, masks]
      have valid := (legal left.1 supported).2.2 e liveE
      have insideE := (blockComponent_self M move e).trans liveE
      have insideF : blockComponent M move e f = true := by rw [masks,blockComponent_self,liveF]
      have kept := blockResponse_preserves_views M step move _ rep _ valid e f insideE insideF p equalViews
      simp only [blockMachine_append]
      change (left.1++[actualBlockOutcome M step move e] =
        right.1++[actualBlockOutcome M step (tree right.1) f]) ∧ _
      have nodes' : right.1 = left.1 := nodes.symm
      rw [nodes']
      constructor
      · rw [outcomes]
      · simp only [virtualFamily_append, Function.comp_apply]
        change currentView p (closingLayerHistory (virtualFamily tree left.1) D
          ((move.response (actualBlockOutcome M step move e).component).keep
            ((move.response (actualBlockOutcome M step move e).component).fold e))) = _
        rw [← outcomes]
        exact kept

end Machine
end Characterisation.PeriodicBlocks
