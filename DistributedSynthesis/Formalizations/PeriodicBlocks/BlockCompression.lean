/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.PartialCompression
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReadback

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)

theorem blockComponent_member_of_views (anchor e f : BlockEnd I₁ I₂ B D)
    (inside : blockComponent M move anchor e = true) (live : blockEndLive M move f = true)
    (p : Proc) (eq : blockEndShape move p e f = true) :
    blockComponent M move anchor f = true := by
  have parts : blockEndLive M move e = true ∧
      (closingObservationGraph (blockEndShape move) (blockEndLive M move)).Reachable anchor e := by
    simpa only [blockComponent, closingComponentMask, Bool.and_eq_true, decide_eq_true_eq] using inside
  have reach : (closingObservationGraph (blockEndShape move) (blockEndLive M move)).Reachable e f := by
    by_cases same : e = f
    · subst f; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨same,parts.1,live,p,Or.inl eq⟩
  simp only [blockComponent, closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨live,parts.2.trans reach⟩

variable (past : BlockSlots B → EnvHistory I₁ I₂)
variable (shape : RepresentsInputShape past move.source.shape)
variable (graphs : ∀ i, move.source.graph i = M.eval (History.graphSequence (past i)))

include shape graphs in
theorem blockComponent_member_same_history (anchor e f : BlockEnd I₁ I₂ B D)
    (same : closingLayerHistory past D e = closingLayerHistory past D f) :
    blockComponent M move anchor e = blockComponent M move anchor f := by
  have liveEq : blockEndLive M move e = blockEndLive M move f := by
    simp only [blockEndLive, blockEndGraph, closingLayerLabels_recognizer M past _ graphs, same]
  have equalViews (p : Proc) := (blockEndShape_exact move past shape p e f).mpr (congrArg (currentView p) same)
  have reverseViews (p : Proc) := (blockEndShape_exact move past shape p f e).mpr (congrArg (currentView p) same.symm)
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro inside
    have liveE : blockEndLive M move e = true := by
      simp only [blockComponent,closingComponentMask,Bool.and_eq_true] at inside
      exact inside.1
    exact blockComponent_member_of_views M move anchor e f inside (liveEq.symm.trans liveE) .one (equalViews .one)
  · intro inside
    have liveF : blockEndLive M move f = true := by
      simp only [blockComponent,closingComponentMask,Bool.and_eq_true] at inside
      exact inside.1
    exact blockComponent_member_of_views M move anchor f e inside (liveEq.trans liveF) .one (reverseViews .one)

def componentSuffixes (anchor : BlockEnd I₁ I₂ B D) (i : BlockSlots B)
    (z : BlockInput I₁ I₂ D) : Bool := blockComponent M move anchor (wordScenario i z)

end

section Compression
variable {I₁ I₂ O₁ O₂ G Q : Type} {Rank : Type*} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Finite O₁] [Finite O₂] [Finite G] [Finite Q]
variable [LinearOrder Rank] [WellFoundedLT Rank]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
variable (past : BlockSlots B → EnvHistory I₁ I₂)
variable (shape : RepresentsInputShape past move.source.shape)
variable (graphs : ∀ i, move.source.graph i = M.eval (History.graphSequence (past i)))
variable (states : ∀ i, move.source.objective i = strategyHistoryLabel σ step q₀ (past i))
variable (outputs : ∀ t s, move.policy t s =
  (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
   σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))

include shape graphs states outputs in
theorem block_response_exists
    (bound : compressionBound I₁ I₂ O₁ O₂ G Q D ≤ B+1)
    (anchor : BlockEnd I₁ I₂ B D) (live : blockEndLive M move anchor = true)
    (rank : BlockSlots B → Rank) (leader : Proc)
    (common : ∀ i j,
      (∃ z, componentSuffixes M move anchor i z = true) →
      (∃ z, componentSuffixes M move anchor j z = true) →
      currentView leader (past i) = currentView leader (past j)) :
    let key := strategyBlockType σ D past move.source.graph
      (fun i => strategyHistoryLabel σ step q₀ (past i)) (componentSuffixes M move anchor)
    ∃ response : BlockResponse I₁ I₂ B D,
      ResponseChecks M step move (blockComponent M move anchor) response ∧
      ∀ e, blockComponent M move anchor e = true →
        response.keep (response.fold e) =
          wordScenario (representative key rank (closingLayerRoot D e)) (scenarioWord D e) := by
  classical
  dsimp only
  let member := componentSuffixes M move anchor
  let key := strategyBlockType σ D past move.source.graph
    (fun i => strategyHistoryLabel σ step q₀ (past i)) member
  have memberSame : ∀ i j, past i = past j → member i = member j := by
    intro i j eq
    funext z
    apply blockComponent_member_same_history M move past shape graphs anchor
    simp only [wordScenario_history, eq]
  have keySame : ∀ i j, past i = past j → key i = key j := by
    intro i j eq
    have gm : move.source.graph i = move.source.graph j := by rw [graphs,graphs,eq]
    dsimp only [key, strategyBlockType]
    rw [gm,eq,memberSame i j eq]
  have existsEndpoint : ∃ i z, (key i).suffixes z = true := by
    refine ⟨closingLayerRoot D anchor, scenarioWord D anchor, ?_⟩
    change blockComponent M move anchor (wordScenario _ _) = true
    rw [wordScenario_scenarioWord, blockComponent_self,live]
  obtain ⟨keep,fold,kept,folded⟩ := retained_response key rank B bound existsEndpoint
  let response : BlockResponse I₁ I₂ B D :=
    ⟨fun j => wordScenario (keep j).1 (keep j).2,
      fun e => fold (closingLayerRoot D e, scenarioWord D e)⟩
  have exactFold : ∀ e, blockComponent M move anchor e = true →
      response.keep (response.fold e) =
        wordScenario (representative key rank (closingLayerRoot D e)) (scenarioWord D e) := by
    intro e inside
    change wordScenario (keep (fold _)).1 (keep (fold _)).2 = _
    rw [folded _ _ (by simpa only [key, strategyBlockType, member,componentSuffixes,wordScenario_scenarioWord] using inside)]
  refine ⟨response, ?_, exactFold⟩
  refine ⟨kept, ?_, ?_⟩
  · intro p e f insideE insideF same
    rw [exactFold e insideE,exactFold f insideF]
    apply (blockEndShape_exact move past shape p _ _).mpr
    rw [wordScenario_history,wordScenario_history]
    apply partial_representative_views key rank past keySame leader common
      (closingLayerRoot D e) (closingLayerRoot D f) (scenarioWord D e) (scenarioWord D f)
      (by simpa only [key,strategyBlockType,member,componentSuffixes,wordScenario_scenarioWord] using insideE)
      (by simpa only [key,strategyBlockType,member,componentSuffixes,wordScenario_scenarioWord] using insideF)
      _ _ ((scenarioWord D e).property.trans (scenarioWord D f).property.symm) p
    simpa only [scenarioWord_history] using (blockEndShape_exact move past shape p e f).mp same
  · intro e inside
    rw [exactFold e inside]
    have typeEq := representative_key key rank (closingLayerRoot D e)
    have graphEq := congrArg BlockType.graphState typeEq
    have objEq := congrArg BlockType.objectiveState typeEq
    have ruleEq := congrArg BlockType.rule typeEq
    constructor
    · simp only [blockEndGraph,closingLayerLabels_recognizer M past _ graphs,wordScenario_history,
        scenarioWord_history,wordScenario_root,scenarioWord_wordScenario]
      apply graph_recognizer_replay M
      change move.source.graph _ = move.source.graph _ at graphEq
      simpa only [graphs] using graphEq
    · simp only [blockEndObjective, closingLayerLabels_strategyHistory σ past step q₀ _ states _ outputs,
        wordScenario_history,scenarioWord_history,wordScenario_root,scenarioWord_wordScenario]
      exact strategy_block_replay σ step q₀ D _ _ objEq ruleEq _ (Nat.le_of_eq (scenarioWord D e).property)

end Compression

/-- At every live ending component, the roots of all participating
`D`-round continuations share one process's view. -/
def CommonBlockRoots {I₁ I₂ : Type} (P : List Graph → Prop) (D : Nat) : Prop :=
  ∀ (R : Type) (anchor : EnvHistory I₁ I₂), P (History.graphSequence anchor) →
    ∀ root suffix : R → EnvHistory I₁ I₂, (∀ i, List.length (suffix i) = D) →
      (∀ i, InputConnected P anchor (root i++suffix i)) →
      ∃ p, ∀ i j, currentView p (root i) = currentView p (root j)

theorem holes_commonBlockRoots {I₁ I₂ : Type}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ D, 0 < D ∧ CommonBlockRoots (I₁:=I₁) (I₂:=I₂) (LivePrefix A) D :=
  holes_block_common_root A regular holes

section Common
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (commonRoots : CommonBlockRoots (I₁:=I₁) (I₂:=I₂) P D)
variable (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
variable (past : BlockSlots B → EnvHistory I₁ I₂)
variable (shape : RepresentsInputShape past move.source.shape)
variable (graphs : ∀ i, move.source.graph i = M.eval (History.graphSequence (past i)))

include commonRoots shape graphs recognizes in
theorem component_common_roots (anchor : BlockEnd I₁ I₂ B D)
    (live : blockEndLive M move anchor = true) :
    ∃ leader, ∀ i j,
      (∃ z, componentSuffixes M move anchor i z = true) →
      (∃ z, componentSuffixes M move anchor j z = true) →
      currentView leader (past i) = currentView leader (past j) := by
  classical
  let R := {i : BlockSlots B // ∃ z, componentSuffixes M move anchor i z = true}
  let witness (i : R) := Classical.choose i.property
  have inside (i : R) : componentSuffixes M move anchor i.val (witness i) = true :=
    Classical.choose_spec i.property
  have liveExact : ∀ e, blockEndLive M move e = true ↔
      P (History.graphSequence (closingLayerHistory past D e)) := by
    intro e
    simp only [blockEndLive, blockEndGraph, closingLayerLabels_recognizer M past _ graphs, decide_eq_true_eq]
    exact (recognizes _).symm
  obtain ⟨p,common⟩ := commonRoots R (closingLayerHistory past D anchor) ((liveExact anchor).mp live)
    (fun i => past i.val) (fun i => (witness i).val) (fun i => (witness i).property)
    (fun i => by
      have conn := blockComponent_connected M move past shape P liveExact anchor
        (wordScenario i.val (witness i)) (inside i)
      simpa only [wordScenario_history] using conn)
  exact ⟨p,fun i j hi hj => common ⟨i,hi⟩ ⟨j,hj⟩⟩

end Common
end
end Characterisation.PeriodicBlocks
