/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.RepresentationLift
import DistributedSynthesis.Formalizations.ComponentGames.FiniteProduct
import DistributedSynthesis.Formalizations.ComponentGames.FiniteToHistory

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
variable (target : LabeledTree (HistoryGame.Position I₁ I₂ Q D) (HistoryGame.Move I₁ I₂ O₁ O₂ Q D))
variable (valid : SupportedMovesValid (HistoryGame.offers M step) (HistoryGame.Position.initial q₀)
    (HistoryGame.Legal M step (.bounded W)) target)

def castHistoryIso {P P' : HistoryGame.Position I₁ I₂ Q D} {A : Position G Q B}
    (e : Iso (ofHistory M P) A.2) (eq : P = P') : Iso (ofHistory M P') A.2 := eq ▸ e

theorem castHistoryIso_inverse_val {P P' : HistoryGame.Position I₁ I₂ Q D} {A : Position G Q B}
    (e : Iso (ofHistory M P) A.2) (eq : P = P') (j : A.Root) :
    ((castHistoryIso M e eq).toEquiv.symm j).val = (e.toEquiv.symm j).val := by cases eq; rfl

theorem castFiniteIso_inverse_related {P : HistoryGame.Position I₁ I₂ Q D} {A A' : Position G Q B}
    (e : Iso (ofHistory M P) A.2) (eq : A = A') (j : A'.Root) :
    ∃ k : A.Root, (castFiniteIso M e eq).toEquiv.symm j = e.toEquiv.symm k ∧
      FiniteArena.slot A' j = FiniteArena.slot A k := by
  cases eq
  exact ⟨j,rfl,rfl⟩

namespace HistoryToFinite
structure State where
  observed : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B
  node : List (HistoryGame.Position I₁ I₂ Q D)
  supported : publicSupport (HistoryGame.offers M step) target node = true
  iso : Iso (ofHistory M (target node).source) (FiniteArena.observedPosition M step q₀ positive observed).2

def action (s : State M step q₀ positive target) : FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B :=
  pushMove M (target s.node) (FiniteArena.observedPosition M step q₀ positive s.observed) s.iso

def start : State M step q₀ positive target := by
  refine ⟨none,[],publicSupport_nil _ _,?_⟩
  have source := (valid [] (publicSupport_nil _ _)).1
  change (target []).source = HistoryGame.Position.initial q₀ at source
  rw [source]
  exact initialIso M q₀ positive

include valid in
theorem action_legal (s : State M step q₀ positive target) :
    FiniteArena.Legal M step W q₀ positive s.observed (action M step q₀ positive target s) := by
  refine ⟨rfl,?_⟩
  exact pushMove_legal M step (target s.node) _ s.iso W ⟨rfl,(valid s.node s.supported).2⟩

structure AdvanceData (s : State M step q₀ positive target)
    (o : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B) where
  real : HistoryGame.Position I₁ I₂ Q D
  next : HistoryGame.Next M step (target s.node) real
  iso : Iso (ofHistory M real) (FiniteArena.observedPosition M step q₀ positive o).2
  component : Finset (action M step q₀ positive target s).End
  bound : component.card ≤ B
  observation : o = some ⟨action M step q₀ positive target s,component⟩
  trace : ∀ (a : (target s.node).source.Root)
    (j : (FiniteArena.observedPosition M step q₀ positive o).Root)
    (w : FiniteArena.Word I₁ I₂ D) (e : component),
    e.val = wordScenario ((action M step q₀ positive target s).replacement (s.iso.toEquiv a)) w →
    FiniteArena.slot (FiniteArena.observedPosition M step q₀ positive o) j =
      FiniteArena.endSlot (action M step q₀ positive target s) component bound e →
    (iso.toEquiv.symm j).val = ((target s.node).replacement a).val ++ w.val

def advanceData (s : State M step q₀ positive target) (o : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B)
    (offered : FiniteArena.offers M (action M step q₀ positive target s) o = true) :
    AdvanceData M step q₀ positive target s o := by
  cases o with
  | none => simp [FiniteArena.offers] at offered
  | some o =>
    have conditions := of_decide_eq_true offered
    obtain ⟨fm,L⟩ := o
    have same : fm = action M step q₀ positive target s := conditions.1
    subst fm
    let A := FiniteArena.observedPosition M step q₀ positive s.observed
    let m := target s.node
    let K := componentImage s.iso.toEquiv.symm L
    have members (t : m.source.End) : t ∈ K ↔ mapClosingLayer s.iso.toEquiv D t ∈ L := by
      have h := componentImage_members s.iso.toEquiv.symm L (mapClosingLayer s.iso.toEquiv D t)
      simpa only [mapLayer_inverse] using h.symm
    have component : HistoryGame.IsComponent M m K := by
      apply (history_component_iff M m K).mpr
      exact (components_map M (ofHistory M m.source) A.2 s.iso m.rule m.replacement K L members).mp conditions.2.1
    let P := componentPosition M step m K component
    have histories := componentPosition_histories M step m K component
    have states := componentPosition_states M step m K component
    have bound : L.card ≤ B := conditions.2.2
    have observed : FiniteArena.observedPosition M step q₀ positive (some ⟨action M step q₀ positive target s,L⟩) =
        FiniteArena.nextPosition M step ⟨pushMove M m A s.iso,L⟩ bound := by
      simp only [FiniteArena.observedPosition,dif_pos bound]
      rfl
    let iso := castFiniteIso M (reachedIso M step m A s.iso P K L members histories states bound) observed.symm
    refine ⟨P,componentPosition_next M step m K component,iso,L,bound,rfl,?_⟩
    intro a j w e endpoint numbered
    obtain ⟨k,rootEq,slotEq⟩ := castFiniteIso_inverse_related M
      (reachedIso M step m A s.iso P K L members histories states bound) observed.symm j
    change ((castFiniteIso M _ observed.symm).toEquiv.symm j).val = _
    rw [rootEq]
    apply reachedIso_backtrace M step m A s.iso P K L members histories states bound e _ a w endpoint
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (congrArg (fun x : Fin (B+1) => x.val) (slotEq.symm.trans numbered))

def advance (s : State M step q₀ positive target) (o : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B)
    (offered : FiniteArena.offers M (action M step q₀ positive target s) o = true) : State M step q₀ positive target := by
  let data := advanceData M step q₀ positive target s o offered
  have supported : publicSupport (HistoryGame.offers M step) target (s.node ++ [data.real]) = true := by
    rw [publicSupport_append,s.supported,Bool.true_and]
    exact @decide_eq_true _ (Classical.propDecidable _) data.next
  have source : (target (s.node ++ [data.real])).source = data.real := by
    have eq := (valid _ supported).1
    simpa only [observableAt,List.getLast?_concat,Option.getD_some] using eq
  exact ⟨o,s.node ++ [data.real],supported,castHistoryIso M data.iso source.symm⟩

def interpreter : SupportedInterpreter (FiniteArena.offers M) (none : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B)
    (FiniteArena.Legal M step W q₀ positive) (HistoryGame.offers M step) target where
  State := State M step q₀ positive target
  start := start M step W q₀ positive target valid
  observed := State.observed
  action := action M step q₀ positive target
  targetNode := State.node
  start_observed := rfl
  start_node := rfl
  legal := action_legal M step W q₀ positive target valid
  target_supported := State.supported
  advance := advance M step W q₀ positive target valid
  reply := fun s o h => (advanceData M step q₀ positive target s o h).real
  advance_observed := fun _ _ _ => rfl
  advance_node := fun _ _ _ => rfl

end HistoryToFinite
end
end Characterisation.ComponentGames.Representation
