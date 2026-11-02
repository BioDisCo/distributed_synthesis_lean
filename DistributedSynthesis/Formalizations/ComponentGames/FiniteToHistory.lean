/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.RepresentationLift
import DistributedSynthesis.Formalizations.ComponentGames.FiniteProduct

namespace Characterisation.ComponentGames.Representation
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
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

def castFiniteIso {P : HistoryGame.Position I₁ I₂ Q D} {A A' : Position G Q B}
    (e : Iso (ofHistory M P) A.2) (eq : A = A') : Iso (ofHistory M P) A'.2 := eq ▸ e

theorem castFiniteIso_slot {P : HistoryGame.Position I₁ I₂ Q D} {A A' : Position G Q B}
    (e : Iso (ofHistory M P) A.2) (eq : A = A') (h : P.Root) :
    FiniteArena.slot A' ((castFiniteIso M e eq).toEquiv h) = FiniteArena.slot A (e.toEquiv h) := by
  cases eq; rfl

namespace FiniteToHistory
structure State where
  real : HistoryGame.Position I₁ I₂ Q D
  node : List (FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B)
  supported : publicSupport (FiniteArena.offers M) target node = true
  iso : Iso (ofHistory M real) (target node).source.2

def action (s : State M target) : HistoryGame.Move I₁ I₂ O₁ O₂ Q D := pullMove M (target s.node) s.real s.iso

def start : State M target := by
  refine ⟨HistoryGame.Position.initial q₀,[],publicSupport_nil _ _,?_⟩
  have eq := (valid [] (publicSupport_nil _ _)).1
  change (target []).source = FiniteArena.initial M q₀ positive at eq
  rw [eq]
  exact initialIso M q₀ positive

include valid in
theorem action_legal (s : State M target) : HistoryGame.Legal M step (.bounded W) s.real (action M target s) :=
  pullMove_legal M step (target s.node) s.real s.iso W (valid s.node s.supported).2

structure AdvanceData (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D) where
  observation : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B
  offered : FiniteArena.offers M (target s.node) observation = true
  iso : Iso (ofHistory M P) (FiniteArena.observedPosition M step q₀ positive observation).2
  trace : ∀ (h : P.Root) (a : s.real.Root) (w : FiniteArena.Word I₁ I₂ D),
    h.val = ((action M target s).replacement a).val ++ w.val →
    ∃ (K : Finset (target s.node).End) (bound : K.card ≤ B) (e : K),
      observation = some ⟨target s.node,K⟩ ∧
      e.val = wordScenario ((target s.node).replacement (s.iso.toEquiv a)) w ∧
      FiniteArena.slot (FiniteArena.observedPosition M step q₀ positive observation) (iso.toEquiv h) =
        FiniteArena.endSlot (target s.node) K bound e

def advanceData (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P) : AdvanceData M step q₀ positive target s P := by
  let K := next.2.choose
  have component := next.2.choose_spec.1
  have histories := next.2.choose_spec.2.1
  have states := next.2.choose_spec.2.2
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
  let iso := castFiniteIso M (reachedIso M step m fm.source s.iso P K L members histories states bound) observed.symm
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
    exact congrArg (fun j : Fin L.card => j.val) value

def advance (s : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P) : State M target := by
  let data := advanceData M step W q₀ positive capacity target valid s P next
  have supported : publicSupport (FiniteArena.offers M) target (s.node ++ [data.observation]) = true := by
    rw [publicSupport_append,s.supported,Bool.true_and]
    exact data.offered
  have source : (target (s.node ++ [data.observation])).source =
      FiniteArena.observedPosition M step q₀ positive data.observation := by
    have h := (valid _ supported).1
    simpa only [observableAt,List.getLast?_concat,Option.getD_some] using h
  exact ⟨P,s.node ++ [data.observation],supported,castFiniteIso M data.iso source.symm⟩

def interpreter : SupportedInterpreter (HistoryGame.offers (D:=D) M step) (HistoryGame.Position.initial q₀)
    (HistoryGame.Legal M step (.bounded W)) (FiniteArena.offers M) target where
  State := State M target
  start := start M step W q₀ positive target valid
  observed := State.real
  action := action M target
  targetNode := State.node
  start_observed := rfl
  start_node := rfl
  legal := action_legal M step W q₀ positive target valid
  target_supported := State.supported
  advance := fun s P h => advance M step W q₀ positive capacity target valid s P (@of_decide_eq_true _ (Classical.propDecidable _) h)
  reply := fun s P h => (advanceData M step W q₀ positive capacity target valid s P (@of_decide_eq_true _ (Classical.propDecidable _) h)).observation
  advance_observed := fun _ _ _ => rfl
  advance_node := fun _ _ _ => rfl

end FiniteToHistory
end
end Characterisation.ComponentGames.Representation
