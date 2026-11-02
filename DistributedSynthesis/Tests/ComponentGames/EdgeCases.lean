/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.HistoryGames

/- Regression check for the nonempty-alphabet hypothesis. The exact initial
component bound fails for an empty input alphabet, independently of the
automata-state factor N. Inputless processes use the nonempty type Unit. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open HistoryGame

def bothOnly : Recognizer Graph Bool where
  start := true
  step q g := q && decide (g = Graph.both)
  accept := {true}

instance : DecidablePred (· ∈ bothOnly.accept) := fun q => inferInstanceAs (Decidable (q = true))

/-- This is a nontrivial prefix-hole example: the adversary allows only
bidirectional communication, and a left-only round is always a hole. -/
theorem bothOnly_exact_one_hole :
    ∀ h, ∃ u : List Graph, u.length = 1 ∧ bothOnly.eval (h ++ u) ∉ bothOnly.accept := by
  intro h
  refine ⟨[.left],rfl,?_⟩
  simp [Recognizer.eval,Recognizer.evalFrom,List.foldl_append,bothOnly]

/-- No value of N repairs B=N|Sigma|^(2D) when Sigma is empty and D=1.
The zero-length play reaches the singleton initial component. -/
theorem empty_input_breaks_initial_bound (N : Nat) :
    let P := Position.initial (I₁:=Empty) (I₂:=Unit) (D:=1) ()
    Reached bothOnly (fun (_ : Unit) (_ : Empty × Unit × Graph) (_ : Unit × Unit) => ())
      (.bounded (N * Nat.card (Empty × Unit × Graph)^1)) () P ∧
    ¬ P.histories.card ≤ N * Nat.card (Empty × Unit × Graph)^(2*1) := by
  refine ⟨Reached.initial,?_⟩
  simp [Position.initial,Nat.card_eq_fintype_card]

end Characterisation.ComponentGames
