/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.SimulationRuns

/- Component-game equivalence: follow the paper's construction assigning
outputs along all plays, and prove its cross-play well-definedness. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

/-- Equality includes the induced objective-state assignment, not only C. -/
theorem position_ext (P R : Position I₁ I₂ Q D)
    (phase : P.phase = R.phase) (histories : P.histories = R.histories)
    (states : ∀ (h : P.Root) (k : R.Root), h.val = k.val → P.state h = R.state k) : P = R := by
  cases P with | mk p H hn hl state =>
    cases R with | mk r K kn kl other =>
      dsimp only at phase histories states
      subst r
      subst K
      have eq : state = other := funext (fun h => states h h rfl)
      subst other
      rfl

/-- Two next positions containing indistinguishable histories are the SAME
component, including its uniquely induced state assignment. -/
theorem next_unique_of_view (m : Move I₁ I₂ O₁ O₂ Q D)
    (P R : Position I₁ I₂ Q D) (first : Next M step m P) (second : Next M step m R)
    (h : P.Root) (k : R.Root) (p : Proc) (same : currentView p h.val = currentView p k.val) : P = R := by
  obtain ⟨ph,K,compK,histK,stateK⟩ := first
  obtain ⟨pr,L,compL,histL,stateL⟩ := second
  obtain ⟨a,aliveA,maskA⟩ := compK
  obtain ⟨b,aliveB,maskB⟩ := compL
  have memH : h.val ∈ K.image m.source.history := by rw [← histK]; exact h.property
  have memK : k.val ∈ L.image m.source.history := by rw [← histL]; exact k.property
  obtain ⟨e,he,historyE⟩ := Finset.mem_image.mp memH
  obtain ⟨f,hf,historyF⟩ := Finset.mem_image.mp memK
  have ae := (maskA e).mp he
  have bf := (maskB f).mp hf
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq] at ae bf
  let graph := closingObservationGraph (closingLayerShape m.source.shape D) (extensionLive M m)
  have ef : graph.Reachable e f := by
    by_cases eq : e = f
    · rw [eq]
    · apply SimpleGraph.Adj.reachable
      refine ⟨eq,ae.1,bf.1,p,Or.inl ?_⟩
      apply (closingLayerShape_exact m.source.past _ (extractInputShape_exact m.source.past) D p e f).mpr
      change currentView p (m.source.history e) = currentView p (m.source.history f)
      rw [historyE,historyF]
      exact same
  have connected : graph.Reachable a b := ae.2.trans (ef.trans bf.2.symm)
  have equalComponents : K = L := by
    apply Finset.ext
    intro e
    rw [maskA,maskB]
    simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _ => ⟨fun reach => connected.symm.trans reach,
      fun reach => connected.trans reach⟩)
  have histories : P.histories = R.histories := by rw [histK,histL,equalComponents]
  apply position_ext P R (ph.trans pr.symm) histories
  intro x y eq
  have mem : x.val ∈ K.image m.source.history := by rw [← histK]; exact x.property
  obtain ⟨e,he,history⟩ := Finset.mem_image.mp mem
  have inL : e ∈ L := equalComponents ▸ he
  exact (stateK x e he history.symm).trans (stateL y e inL (eq.symm.trans history.symm)).symm

variable (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D)) (q₀ : Q)
variable (legal : SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component) tree)

include legal in
theorem source_phase (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) tree node = true) :
    (tree node).source.phase = node.length := by
  induction node using List.reverseRecOn with
  | nil => rw [(legal [] supported).1]; rfl
  | append_singleton node P ih =>
    have both : publicSupport (offers M step) tree node = true ∧ offers M step (tree node) P = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    have next : Next M step (tree node) P := of_decide_eq_true both.2
    have source : (tree (node ++ [P])).source = P := by simpa [observableAt] using (legal _ supported).1
    rw [source,next.1,ih both.1,List.length_append,List.length_singleton]

/- The English induction on the two finite plays: equality of a current
local view forces equality of the entire public play prefix. -/
include legal in
theorem component_nodes_equal (node other : List (Position I₁ I₂ Q D))
    (lengths : node.length = other.length)
    (supported : publicSupport (offers M step) tree node = true)
    (otherSupported : publicSupport (offers M step) tree other = true)
    (h : (tree node).source.Root) (k : (tree other).source.Root) (p : Proc)
    (same : currentView p h.val = currentView p k.val) : node = other := by
  induction node using List.reverseRecOn generalizing other with
  | nil =>
    have empty : other = [] := by simpa using lengths.symm
    exact empty.symm
  | append_singleton node P ih =>
    cases other using List.reverseRecOn with
    | nil => simp at lengths
    | append_singleton other R =>
      have first : publicSupport (offers M step) tree node = true ∧ offers M step (tree node) P = true := by
        simpa only [publicSupport_append,Bool.and_eq_true] using supported
      have second : publicSupport (offers M step) tree other = true ∧ offers M step (tree other) R = true := by
        simpa only [publicSupport_append,Bool.and_eq_true] using otherSupported
      have nextP : Next M step (tree node) P := of_decide_eq_true first.2
      have nextR : Next M step (tree other) R := of_decide_eq_true second.2
      have sourceP : (tree (node ++ [P])).source = P := by simpa [observableAt] using (legal _ supported).1
      have sourceR : (tree (other ++ [R])).source = R := by simpa [observableAt] using (legal _ otherSupported).1
      let hp : P.Root := ⟨h.val,by simpa only [Position.Root,sourceP] using h.property⟩
      let kr : R.Root := ⟨k.val,by simpa only [Position.Root,sourceR] using k.property⟩
      obtain ⟨⟨a,u⟩,⟨_,hu⟩,_⟩ := previous_phase_extensions M step (tree node) P nextP hp
      obtain ⟨⟨b,v⟩,⟨_,kv⟩,_⟩ := previous_phase_extensions M step (tree other) R nextR kr
      have oldSame : currentView p a.val = currentView p b.val := by
        have views : currentView p (a.val ++ u.val) = currentView p (b.val ++ v.val) := by
          rw [← hu,← kv]; exact same
        have lu := lagView_suffix p a.val u.val
        have lv := lagView_suffix p b.val v.val
        rw [u.property] at lu
        rw [v.property] at lv
        exact lu.symm.trans ((congrArg (lagView D) views).trans lv)
      have oldEq := ih other (by simpa using lengths) first.1 second.1 a b oldSame
      subst other
      have positions := next_unique_of_view M step (tree node) P R nextP nextR hp kr p same
      rw [positions]

/-- Exactly the output prescriptions in the English proof, restricted to
live histories reached along supported finite plays. -/
structure Prescription where
  node : List (Position I₁ I₂ Q D)
  supported : publicSupport (offers M step) tree node = true
  time : Fin D
  scenario : ClosingLayer (tree node).source.Root I₁ I₂ (time.val+1)
  live : M.eval (History.graphSequence
    (closingLayerHistory (tree node).source.past (time.val+1) scenario)) ∈ M.accept

def prescribedHistory (x : Prescription M step tree) : EnvHistory I₁ I₂ :=
  closingLayerHistory (tree x.node).source.past (x.time.val+1) x.scenario

def prescribedOutput (x : Prescription M step tree) : O₁ × O₂ :=
  (tree x.node).rule x.time x.scenario

include legal in
theorem prescribed_length (x : Prescription M step tree) :
    List.length (prescribedHistory M step tree x) = x.node.length * D + (x.time.val+1) := by
  have len := closingLayerHistory_length (tree x.node).source.past ((tree x.node).source.phase*D)
    (fun h => (tree x.node).source.lengths h.val h.property) (x.time.val+1) x.scenario
  simpa only [source_phase M step tree q₀ legal x.node x.supported] using len

include legal in
theorem prescription_times (x y : Prescription M step tree) (p : Proc)
    (same : currentView p (prescribedHistory M step tree x) = currentView p (prescribedHistory M step tree y)) :
    x.node.length = y.node.length ∧ x.time = y.time := by
  have adjacent : InputAdjacent (prescribedHistory M step tree x) (prescribedHistory M step tree y) := by
    cases p <;> [exact Or.inl same; exact Or.inr same]
  have lengths := adjacent_same_depth (inputAdjacent_projects adjacent)
  simp only [History.graphSequence,List.length_map] at lengths
  rw [prescribed_length M step tree q₀ legal x,prescribed_length M step tree q₀ legal y] at lengths
  have tx := x.time.isLt
  have ty := y.time.isLt
  have nodes : x.node.length = y.node.length := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have bound := Nat.mul_le_mul_right D (Nat.succ_le_of_lt lt)
      simp only [Nat.succ_mul] at bound
      omega
    · have bound := Nat.mul_le_mul_right D (Nat.succ_le_of_lt gt)
      simp only [Nat.succ_mul] at bound
      omega
  refine ⟨nodes,Fin.ext ?_⟩
  rw [nodes] at lengths
  omega

include legal in
theorem prescription_nodes (x y : Prescription M step tree) (p : Proc)
    (same : currentView p (prescribedHistory M step tree x) = currentView p (prescribedHistory M step tree y)) :
    x.node = y.node := by
  obtain ⟨lengths,times⟩ := prescription_times M step tree q₀ legal x y p same
  have old : currentView p (closingLayerRoot (x.time.val+1) x.scenario).val =
      currentView p (closingLayerRoot (y.time.val+1) y.scenario).val := by
    have left := lagView_suffix p (closingLayerRoot (x.time.val+1) x.scenario).val
      (scenarioWord (x.time.val+1) x.scenario).val
    have right := lagView_suffix p (closingLayerRoot (y.time.val+1) y.scenario).val
      (scenarioWord (y.time.val+1) y.scenario).val
    rw [(scenarioWord (x.time.val+1) x.scenario).property] at left
    rw [(scenarioWord (y.time.val+1) y.scenario).property] at right
    have lx : lagView (x.time.val+1) (currentView p (prescribedHistory M step tree x)) =
        currentView p (closingLayerRoot (x.time.val+1) x.scenario).val := by
      simpa only [prescribedHistory,scenarioWord_history,Position.past] using left
    have ly : lagView (y.time.val+1) (currentView p (prescribedHistory M step tree y)) =
        currentView p (closingLayerRoot (y.time.val+1) y.scenario).val := by
      simpa only [prescribedHistory,scenarioWord_history,Position.past] using right
    have shift := congrArg (fun t : Fin D => lagView (t.val+1)
      (currentView p (prescribedHistory M step tree y))) times
    exact lx.symm.trans ((congrArg (lagView (x.time.val+1)) same).trans (shift.trans ly))

  exact component_nodes_equal M step tree q₀ legal x.node y.node lengths x.supported y.supported _ _ p old

include legal in
theorem prescriptions_consistent (x y : Prescription M step tree) (p : Proc)
    (same : currentView p (prescribedHistory M step tree x) = currentView p (prescribedHistory M step tree y)) :
    match p with
    | .one => (prescribedOutput M step tree x).1 = (prescribedOutput M step tree y).1
    | .two => (prescribedOutput M step tree x).2 = (prescribedOutput M step tree y).2 := by
  have nodes := prescription_nodes M step tree q₀ legal x y p same
  have times := (prescription_times M step tree q₀ legal x y p same).2
  rcases x with ⟨node,support,t,e,live⟩
  rcases y with ⟨other,otherSupport,u,f,otherLive⟩
  dsimp only at nodes times
  subst other
  subst u
  have shape := (closingLayerShape_exact (tree node).source.past _
    (extractInputShape_exact (tree node).source.past) (t.val+1) p e f).mpr same
  have distributed := (legal node support).2.1 t
  cases p
  · exact distributed.1 e f shape
  · exact distributed.2 e f shape

include legal in
/-- Assign arbitrary values elsewhere using the existing local-table lemma.
This is the paper's global f, agreeing with ALL live prescriptions at once. -/
theorem component_controller_strategy [Nonempty O₁] [Nonempty O₂] :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ x : Prescription M step tree,
      (σ.one (currentView .one (prescribedHistory M step tree x)),
       σ.two (currentView .two (prescribedHistory M step tree x))) = prescribedOutput M step tree x := by
  let history := prescribedHistory M step tree
  let out := prescribedOutput M step tree
  have coherent : ShapeCoherent (extractInputShape history) out := by
    constructor
    · intro x y same
      exact prescriptions_consistent M step tree q₀ legal x y .one
        ((extractInputShape_exact history .one x y).mp same)
    · intro x y same
      exact prescriptions_consistent M step tree q₀ legal x y .two
        ((extractInputShape_exact history .two x y).mp same)
  obtain ⟨σ,correct⟩ := (shapeCoherent_iff_local history _ (extractInputShape_exact history) out).mp coherent
  exact ⟨σ,fun x => Prod.ext (correct x).1 (correct x).2⟩

end
end Characterisation.ComponentGames.HistoryGame

