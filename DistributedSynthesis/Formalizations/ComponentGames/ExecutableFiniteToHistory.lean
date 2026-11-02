/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms
import DistributedSynthesis.Formalizations.ComponentGames.FiniteToHistoryRuns

namespace Characterisation.ComponentGames.ExecutableFiniteToHistory
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks Representation Representation.FiniteToHistory
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Fintype G] [Fintype Q] [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (W : Nat) (q₀ : Q) (positive : 0 < B)
variable (capacity : W * Nat.card (FiniteArena.Word I₁ I₂ D) ≤ B)
variable (target : LabeledTree (FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B) (FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B))
variable (valid : SupportedMovesValid (FiniteArena.offers M) none (FiniteArena.Legal M step W q₀ positive) target)

def buildAdvanceData (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (K : Finset (action M target s).source.End)
    (component : HistoryGame.IsComponent M (action M target s) K)
    (histories : P.histories = K.image (action M target s).source.history)
    (states : ∀ (h : P.Root) (e : (action M target s).source.End), e ∈ K →
      h.val = (action M target s).source.history e → P.state h =
        closingLayerLabels step (action M target s).source.state (action M target s).rule D (Nat.le_refl D) e) :
    AdvanceData M step q₀ positive target s P := by
  let m := action M target s
  let fm := target s.node
  let L := componentImage s.iso.toEquiv K
  have members := componentImage_members s.iso.toEquiv K
  have pol := policy_inverse s.iso.toEquiv.symm fm.rule
  have rep := replacement_inverse s.iso.toEquiv.symm fm.replacement
  simp only [Equiv.symm_symm] at pol rep
  have comp : Components M fm.source.2 fm.rule fm.replacement L := by
    have c := (pushMove_component M m fm.source s.iso K).mpr component
    change Components M fm.source.2 (policy s.iso.toEquiv (policy s.iso.toEquiv.symm fm.rule))
      (replacement s.iso.toEquiv (replacement s.iso.toEquiv.symm fm.replacement)) L at c
    rw [pol,rep] at c
    exact c
  have bound : L.card ≤ B :=
    FiniteArena.legal_component_fits M step W q₀ positive capacity _ fm (valid s.node s.supported) L comp
  have offered : FiniteArena.offers M fm (some ⟨fm,L⟩) = true :=
    (FiniteArena.offers_component M fm L).mpr ⟨comp,bound⟩
  have observed : FiniteArena.observedPosition M step q₀ positive (some ⟨fm,L⟩) =
      FiniteArena.nextPosition M step ⟨pushMove M m fm.source s.iso,L⟩ bound := by
    simp only [FiniteArena.observedPosition,dif_pos bound]
    change pack L bound (successor M step fm.source.2 fm.rule L) =
      pack L bound (successor M step fm.source.2 (policy s.iso.toEquiv (policy s.iso.toEquiv.symm fm.rule)) L)
    rw [pol]
  let iso := castFiniteIso M (ExecutableHistories.reached M step m fm.source s.iso P K L members histories states bound) observed.symm
  refine ⟨some ⟨fm,L⟩,offered,iso,?_⟩
  intro h a w eq
  let t : m.source.End := wordScenario (m.replacement a) w
  have history : h.val = m.source.history t := by
    change h.val = closingLayerHistory m.source.past D (wordScenario (m.replacement a) w)
    rw [wordScenario_history]
    exact eq
  have inside : t ∈ K := by
    have hm := h.property
    change h.val ∈ P.histories at hm
    rw [histories,history] at hm
    obtain ⟨u,um,ue⟩ := Finset.mem_image.mp hm
    exact (m.source.history_injective ue) ▸ um
  let e : L := ⟨mapClosingLayer s.iso.toEquiv D t,(members t).mp inside⟩
  refine ⟨L,bound,e,rfl,?_,?_⟩
  · change mapClosingLayer s.iso.toEquiv D (wordScenario (m.replacement a) w) = _
    exact (HistoryGame.mapClosingLayer_wordScenario s.iso.toEquiv (m.replacement a) D w).trans
      (congrArg (fun root => wordScenario root w)
        (s.iso.toEquiv.apply_symm_apply (fm.replacement (s.iso.toEquiv a))))
  · rw [castFiniteIso_slot]
    have value := reachedIso_trace M step m fm.source s.iso P K L members histories states bound ⟨t,inside⟩ h history
    apply Fin.ext
    simpa only [ExecutableHistories.reached_eq] using congrArg (fun j : Fin L.card => j.val) value

def advanceData (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P) : AdvanceData M step q₀ positive target s P := by
  let K := ExecutableHistories.recoverComponent M step (action M target s) P next
  have keq : K = next.2.choose := ExecutableHistories.recoverComponent_eq M step (action M target s) P next
  apply buildAdvanceData M step W q₀ positive capacity target valid s P K
  · rw [keq]; exact next.2.choose_spec.1
  · rw [keq]; exact next.2.choose_spec.2.1
  · rw [keq]; exact next.2.choose_spec.2.2

theorem advanceData_eq (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P) :
    advanceData M step W q₀ positive capacity target valid s P next =
      FiniteToHistory.advanceData M step W q₀ positive capacity target valid s P next := by
  let f (K : {K : Finset (action M target s).source.End //
      HistoryGame.IsComponent M (action M target s) K ∧
      P.histories = K.image (action M target s).source.history ∧
      ∀ (h : P.Root) (e : (action M target s).source.End), e ∈ K →
        h.val = (action M target s).source.history e → P.state h =
          closingLayerLabels step (action M target s).source.state (action M target s).rule D (Nat.le_refl D) e}) :=
    buildAdvanceData M step W q₀ positive capacity target valid s P K.val K.property.1 K.property.2.1 K.property.2.2
  have eq := ExecutableHistories.recoverComponent_eq M step (action M target s) P next
  let C : Finset (action M target s).source.End → Prop := fun K => HistoryGame.IsComponent M (action M target s) K ∧
      P.histories = K.image (action M target s).source.history ∧
      ∀ (h : P.Root) (e : (action M target s).source.End), e ∈ K →
        h.val = (action M target s).source.history e → P.state h =
          closingLayerLabels step (action M target s).source.state (action M target s).rule D (Nat.le_refl D) e
  have sp : C (ExecutableHistories.recoverComponent M step (action M target s) P next) :=
    Eq.mpr (congrArg C eq) next.2.choose_spec
  have same := congrArg f (Subtype.ext
    (a1 := ⟨ExecutableHistories.recoverComponent M step (action M target s) P next,sp⟩)
    (a2 := ⟨next.2.choose,next.2.choose_spec⟩) eq)
  change advanceData M step W q₀ positive capacity target valid s P next = _ at same
  rw [same]
  unfold f buildAdvanceData FiniteToHistory.advanceData
  simp only [ExecutableHistories.reached_eq]


def buildAdvance (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (data : AdvanceData M step q₀ positive target s P) : State M target := by
  have supported : publicSupport (FiniteArena.offers M) target (s.node ++ [data.observation]) = true := by
    rw [publicSupport_append,s.supported,Bool.true_and]
    exact data.offered
  have source : (target (s.node ++ [data.observation])).source =
      FiniteArena.observedPosition M step q₀ positive data.observation := by
    have h := (valid _ supported).1
    simpa only [observableAt,List.getLast?_concat,Option.getD_some] using h
  exact ⟨P,s.node ++ [data.observation],supported,castFiniteIso M data.iso source.symm⟩

def advance (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P) : State M target :=
  buildAdvance M step W q₀ positive target valid s P
    (advanceData M step W q₀ positive capacity target valid s P next)

theorem advance_eq (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P) :
    advance M step W q₀ positive capacity target valid s P next =
      FiniteToHistory.advance M step W q₀ positive capacity target valid s P next := by
  exact congrArg (buildAdvance M step W q₀ positive target valid s P)
    (advanceData_eq M step W q₀ positive capacity target valid s P next)


def stepState (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D) : State M target :=
  if next : HistoryGame.Next M step (action M target s) P then
    advance M step W q₀ positive capacity target valid s P next else s

theorem stepState_eq : stepState M step W q₀ positive capacity target valid =
    (FiniteToHistory.interpreter M step W q₀ positive capacity target valid).step := by
  funext s P
  by_cases next : HistoryGame.Next M step (action M target s) P
  · have offered : HistoryGame.offers M step (action M target s) P = true :=
      @decide_eq_true _ (Classical.propDecidable _) next
    simp only [stepState,dif_pos next,SupportedInterpreter.step,FiniteToHistory.interpreter,offered,dif_pos True.intro,advance_eq]
  · have offered : HistoryGame.offers M step (action M target s) P = false :=
      @decide_eq_false _ (Classical.propDecidable _) next
    simp only [stepState,dif_neg next,SupportedInterpreter.step,FiniteToHistory.interpreter,offered,Bool.false_eq_true,dif_neg not_false]

def tree : LabeledTree (HistoryGame.Position I₁ I₂ Q D) (HistoryGame.Move I₁ I₂ O₁ O₂ Q D) :=
  fun node => action M target (node.foldl (stepState M step W q₀ positive capacity target valid)
    (start M step W q₀ positive target valid))

theorem tree_eq : tree M step W q₀ positive capacity target valid =
    (FiniteToHistory.interpreter M step W q₀ positive capacity target valid).tree := by
  unfold tree SupportedInterpreter.tree SupportedInterpreter.atState
  rw [stepState_eq]
  rfl

end Characterisation.ComponentGames.ExecutableFiniteToHistory
