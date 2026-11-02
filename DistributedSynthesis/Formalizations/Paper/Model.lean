/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Execution
import DistributedSynthesis.Formalizations.ComponentTrees.ViewMaps

/-!
# Model

Corresponds to the Model subsection and the view recursion in
the manuscript. All objects below are the library's existing objects.

| Paper | Lean |
| --- | --- |
| processes 1, 2 | `Proc.one`, `Proc.two` |
| other process | `Proc.other` |
| 1 <- 2, 1 -> 2, 1 <-> 2 | `Graph.left`, `Graph.right`, `Graph.both` |
| input signal (x1, x2, g) | `EnvironmentRound X₁ X₂` |
| infinite input signal history | `EnvironmentSequence X₁ X₂` |
| initial, nonreceiving, receiving views | `View.empty`, `View.noRecv`, `View.recv` |
| distributed algorithm (f1, f2) | `StrategyPair X₁ X₂ Y₁ Y₂` |
| execution | `execution` |

The input and output types are arbitrary. In the paper they are finite and
nonempty; the definitions themselves do not need these restrictions.
The decision-problem encoding in `ProblemStatement.lean` supplies them.
A message carries the sender's previous view and current input. Outputs are
chosen after reception. A strategy is a function of its own view, without a
finite-memory or computability restriction. Its values on unreachable views
are irrelevant. Lean indexes execution letters from 0; the paper starts at 1.

The equations below expose the existing definitions, rather than introducing
a second model. `PSum.inl` and `PSum.inr` tag the two input types.
-/

namespace DistributedSynthesis.Paper.Model

universe u v x y
variable {X₁ : Type u} {X₂ : Type v} {Y₁ : Type x} {Y₂ : Type y}

/-- Exactly the two processes used in the paper. -/
theorem processes (p : Proc) : p = .one ∨ p = .two := by
  cases p <;> simp

/-- Exactly the three graphs used in the paper. -/
theorem graphs (g : Graph) : g = .left ∨ g = .right ∨ g = .both := by
  cases g <;> simp

/-- The environment alphabet is X₁ × X₂ × Γ. -/
def inputSignals : EnvironmentRound X₁ X₂ ≃ X₁ × X₂ × Graph :=
  EnvironmentRound.equivProd

/-- The recursive table for the two views, with arbitrary private inputs. -/
theorem view_update
    (v₁ : View X₁ X₂ .one) (v₂ : View X₁ X₂ .two)
    (x₁ : X₁) (x₂ : X₂) (g : Graph) :
    advanceViewsWithEnvironment (v₁, v₂) ⟨x₁, x₂, g⟩ =
      match g with
      | .right => (.noRecv v₁ (.inl x₁), .recv v₂ (.inr x₂) v₁ (.inl x₁))
      | .both => (.recv v₁ (.inl x₁) v₂ (.inr x₂), .recv v₂ (.inr x₂) v₁ (.inl x₁))
      | .left => (.recv v₁ (.inl x₁) v₂ (.inr x₂), .noRecv v₂ (.inr x₂)) := by
  cases g <;> rfl

/-- Each output is chosen from that process's updated view. -/
theorem round_outputs (f : StrategyPair X₁ X₂ Y₁ Y₂)
    (h : History X₁ X₂ Graph Y₁ Y₂) (e : EnvironmentRound X₁ X₂) :
    (nextRound f h e).outputOne = f.one (nextView .one h e) ∧
      (nextRound f h e).outputTwo = f.two (nextView .two h e) := ⟨rfl, rfl⟩

/-- The r-th execution letter is generated after the preceding r rounds. -/
theorem execution_round (f : StrategyPair X₁ X₂ Y₁ Y₂)
    (σ : EnvironmentSequence X₁ X₂) (r : Nat) :
    execution f σ r = nextRound f (executionPrefix f σ r) (σ r) :=
  execution_apply f σ r


/-! ## View complex with output

Definition `View complex with output` in the paper.

For the round-r complex under A, take H to be the input histories of length r
whose graph histories are live under A, and `past` to be their inclusion into
`EnvHistory I₁ I₂`. The existing `ViewVertex past p` is exactly the set of views
of process p occurring in that family; `viewEndpoint past p h` is its endpoint
on the edge indexed by h. This includes arbitrary private inputs.

An output labeling assigns a value of O₁ to each process-1 vertex and a value
of O₂ to each process-2 vertex. The labeling induced by f is its restriction
to these vertices. The abbreviations below reuse those existing vertex sets.
-/
section ViewComplexOutput
open Characterisation ComponentTrees
variable {H I₁ I₂ O₁ O₂ : Type}

/-- Output labelings of the existing view complex, with the owner's output type. -/
abbrev ViewComplexOutput (past : H → EnvHistory I₁ I₂) (O₁ O₂ : Type) :=
  (ViewVertex past .one → O₁) × (ViewVertex past .two → O₂)

/-- The output labeling assigned by a distributed algorithm. -/
def labelViewComplex (past : H → EnvHistory I₁ I₂)
    (f : StrategyPair I₁ I₂ O₁ O₂) : ViewComplexOutput past O₁ O₂ :=
  (fun v => f.one v.val, fun v => f.two v.val)

/-- On each edge, the vertex labels are exactly f₁(v₁(h)) and f₂(v₂(h)). -/
theorem labelViewComplex_endpoints (past : H → EnvHistory I₁ I₂)
    (f : StrategyPair I₁ I₂ O₁ O₂) (h : H) :
    (labelViewComplex past f).1 (viewEndpoint past .one h) = f.one (currentView .one (past h)) ∧
      (labelViewComplex past f).2 (viewEndpoint past .two h) = f.two (currentView .two (past h)) :=
  ⟨rfl, rfl⟩

end ViewComplexOutput

end DistributedSynthesis.Paper.Model
