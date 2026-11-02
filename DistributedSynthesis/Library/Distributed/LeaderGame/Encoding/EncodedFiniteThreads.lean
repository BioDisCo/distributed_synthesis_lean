/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedThreadCompiler
import DistributedSynthesis.Formalizations.Theorem.ThmBundleDeterminization

/-! Reuse the original encoded universal-thread compiler for arbitrary finite
resolution systems. A block monitor with singleton output alphabets carries
exactly the source system, so no new determinization algorithm is needed. -/
namespace Characterisation.EncodedFiniteThreads
open DistributedSynthesis

variable {L : Type} (S : FiniteThreadSystem.{0,0,0} L)

def monitor : BlockRecordMonitor S.Resolution L Unit Unit where
  State := S.State
  stateFinite := S.stateFinite
  initial := S.initial
  step q record := S.step q record.1.2 record.1.1
  priority := S.priority

def letter (a : L) : BlockRecordMonitor.ThreadLetter (monitor S) :=
  ((fun _ => (),fun _ _ => ()),a)

theorem thread_iff (word : OmegaWord L) (q : Nat → S.State) :
    (monitor S).IsThread (OmegaWord.map (letter S) word) q ↔ S.IsRun word q := Iff.rfl

theorem priorityRange_eq : ThreadComputable.priorityRange (monitor S) = S.priorityRange := rfl

variable [Fintype S.Resolution] [DecidableEq S.State]
variable (number : S.State ≃ Fin (Fintype.card S.State)) (ps : List Nat)
variable (priority : ∀ q, ps.getD (number q).val 0 = S.priority q)
variable (range : ∀ p, p ∈ ps ↔ p ∈ S.priorityRange)
variable (edges : List EncodedThreadBuchi.Edges) (decode : Fin edges.length → L)
variable (transition : ∀ q (a : Fin edges.length) r,
  ((number q).val,(number r).val) ∈ edges[a.val]?.getD [] ↔
    ∃ resolution : S.Resolution, r = S.step q (decode a) resolution)

/-- The existing numeric data already encode every finite resolution system. -/
def data : EncodedThreadBuchi.Input :=
  (Fintype.card S.State,(number S.initial).val,ps,edges)

include priority range transition in
/-- The unchanged library compiler checks every persistent hidden run. -/
theorem accepts_iff (word : OmegaWord (Fin edges.length)) :
    (EncodedThreadCompiler.automaton (data S number ps edges)).Accepts word ↔
      S.universalRunDPA.Accepts (OmegaWord.map decode word) := by
  letI : DecidableEq (monitor S).State := inferInstanceAs (DecidableEq S.State)
  have hr : ∀ p, p ∈ ps ↔ p ∈ ThreadComputable.priorityRange (monitor S) := by
    intro p
    rw [priorityRange_eq]
    exact range p
  have he : ∀ q (a : Fin edges.length) r,
      ((number q).val,(number r).val) ∈ edges[a.val]?.getD [] ↔
        ∃ i : S.Resolution, r = (monitor S).step q
          (narrowedRecord (monitor S) (letter S (decode a)).1 q (i,(letter S (decode a)).2)) := transition
  have correct := EncodedThreadCompiler.accepts_iff (monitor S) number ps priority hr
    edges (fun a => letter S (decode a)) he word
  rw [FiniteThreadSystem.universalRunDPA_accepts_iff]
  exact correct

end Characterisation.EncodedFiniteThreads
