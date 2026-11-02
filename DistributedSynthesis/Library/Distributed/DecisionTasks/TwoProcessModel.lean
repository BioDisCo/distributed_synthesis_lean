/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Basic
import DistributedSynthesis.Library.Distributed.DecisionTasks.ProcessTransport
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Logic.LTL

/-! # The shared process and graph types at the task interface

The silent graph is `none`; the three existing graphs are `some g`.
Process renaming preserves every finite execution and task solvability.
-/

namespace DistributedSynthesis.DecisionTasks



namespace TwoProcess

def processEquiv : Proc ≃ Bool where
  toFun | .one => false | .two => true
  invFun | false => .one | true => .two
  left_inv p := by cases p <;> rfl
  right_inv b := by cases b <;> rfl

/-- `none` has neither cross-edge. The existing graph directions are preserved. -/
def graphLetter : Option Graph ≃ Source.Letter where
  toFun
    | none => (false, false)
    | some .left => (true, false)
    | some .right => (false, true)
    | some .both => (true, true)
  invFun
    | (false, false) => none
    | (true, false) => some .left
    | (false, true) => some .right
    | (true, true) => some .both
  left_inv g := by rcases g with _ | (_ | _ | _) <;> rfl
  right_inv g := by rcases g with ⟨_ | _, _ | _⟩ <;> rfl

def graphEvent (g : Option Graph) : Event Proc :=
  ProcessTransport.event processEquiv.symm (Source.Event.ofLetter (graphLetter g))

/-- A canonical graph event keeps self-loops and precisely the specified cross-edges. -/
theorem graphEvent_inN (g : Option Graph) (p q : Proc) :
    q ∈ (graphEvent g).inN p ↔
      q = p ∨ (p = .one ∧ (g = some .left ∨ g = some .both)) ∨
        (p = .two ∧ (g = some .right ∨ g = some .both)) := by
  cases p <;> cases q <;> rcases g with _ | (_ | _ | _) <;>
    simp [graphEvent, ProcessTransport.event, processEquiv, Source.Event.ofLetter,
      graphLetter, Source.Letter.hears]

noncomputable def graphWord (σ : ℕ → Event Proc) : ℕ → Option Graph :=
  graphLetter.symm ∘ Source.letter (ProcessTransport.event processEquiv ∘ σ)

@[simp] theorem graphWord_graphEvent (w : ℕ → Option Graph) :
    graphWord (graphEvent ∘ w) = w := by
  funext n
  unfold graphWord
  simp only [Function.comp_apply]
  have h : (ProcessTransport.event processEquiv ∘ graphEvent ∘ w) n =
      Source.Event.ofLetter (graphLetter (w n)) := by
    exact ProcessTransport.event_inverse processEquiv.symm _
  rw [Source.letter_eq_of_ofLetter h, Equiv.symm_apply_apply]

@[simp] theorem graphEvent_graphWord (σ : ℕ → Event Proc) :
    graphEvent ∘ graphWord σ = σ := by
  funext n
  have h : Source.Event.ofLetter
      (Source.letter (ProcessTransport.event processEquiv ∘ σ) n) =
        ProcessTransport.event processEquiv (σ n) := by
    have hn : (Source.Event.ofLetter
        (Source.letter (ProcessTransport.event processEquiv ∘ σ) n)).inN =
          (ProcessTransport.event processEquiv (σ n)).inN :=
      funext (Source.inN_ofLetter_letter (ProcessTransport.event processEquiv ∘ σ) n)
    generalize hl : Source.Event.ofLetter
      (Source.letter (ProcessTransport.event processEquiv ∘ σ) n) = l at *
    generalize hr : ProcessTransport.event processEquiv (σ n) = r at *
    cases l
    cases r
    congr
  simp only [Function.comp_apply, graphWord, graphEvent, Equiv.apply_symm_apply]
  rw [h, ProcessTransport.event_inverse]

/-- Edge atoms are named by their sender: `one` is e12 and `two` is e21. -/
def edgeInterp (sender : Proc) (g : Option Graph) : Prop :=
  match sender with
  | .one => g = some .right ∨ g = some .both
  | .two => g = some .left ∨ g = some .both

theorem edgeInterp_iff (sender : Proc) (g : Option Graph) :
    edgeInterp sender g ↔ sender ∈ (graphEvent g).inN sender.other := by
  rw [graphEvent_inN]
  cases sender <;> simp [edgeInterp, Proc.other]

def edgeDecidable (p : Proc) (g : Option Graph) : Decidable (edgeInterp p g) := by
  cases p <;> unfold edgeInterp <;> exact inferInstance

def noSilence : LTL Proc := .always (.disj (.atom .one) (.atom .two))

theorem noSilence_correct (w : ℕ → Option Graph) :
    LTL.Satisfies edgeInterp w noSilence ↔ ∀ n, w n ≠ none := by
  simp only [noSilence, LTL.always, LTL.Satisfies, OmegaWord.drop]
  apply forall_congr'
  intro n
  rcases w n with _ | (_ | _ | _) <;> simp [edgeInterp]

end TwoProcess
end DistributedSynthesis.DecisionTasks
