/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteTransitions
import DistributedSynthesis.Library.Automata.TreeNonemptiness

namespace Characterisation.ComponentGames.Representation.FiniteArena
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B L : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Fintype G] [Fintype Q] [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (priorityBound : ∀ q, χ q ≤ L)
variable (W : Nat) (q₀ : Q) (positive : 0 < B)

def phaseRelation : Observation I₁ I₂ O₁ O₂ G Q D B → TransitionAlphabet B L
  | none => ∅
  | some o => if bound : o.2.card ≤ B then relation step χ priorityBound o.1 o.2 bound else ∅

def progress : DetParityAutomaton (Move I₁ I₂ O₁ O₂ G Q D B × Observation I₁ I₂ O₁ O₂ G Q D B) :=
  (MonitorCompiler.automaton (B:=B) (K:=L) 0).comap (fun pair => phaseRelation step χ priorityBound pair.2)

/-- The finite arena's universal compatible-run objective, before taking
its deterministic parity product. Legality and finite termination are kept
separate from the infinite-branch obligation. -/
def Winning (tree : LabeledTree (Observation I₁ I₂ O₁ O₂ G Q D B) (Move I₁ I₂ O₁ O₂ G Q D B)) : Prop :=
  SupportedMovesValid (offers M) none (Legal M step W q₀ positive) tree ∧
  ∀ branch, (∀ n, publicSupport (offers M) tree (branchNode branch n) = true) →
    ∀ (h : Nat → Fin (B+1)) (c : Nat → Fin (L+1)), h 0 = 0 →
      (∀ n, (h n,c n,h (n+1)) ∈ phaseRelation step χ priorityBound (branch n)) →
      NatSeqMinEvenParity (fun n => (c n).val)

def product : DeterministicBlockMonitor (Observation I₁ I₂ O₁ O₂ G Q D B) (Move I₁ I₂ O₁ O₂ G Q D B) :=
  supportedPublicTreeMonitor (progress step χ priorityBound) (offers M) none (Legal M step W q₀ positive)

/-- The product adds only public deterministic memory. Its existing
support/safety construction checks illegal moves before empty offers. -/
theorem product_winning_iff (tree : LabeledTree (Observation I₁ I₂ O₁ O₂ G Q D B) (Move I₁ I₂ O₁ O₂ G Q D B)) :
    (product M step χ priorityBound W q₀ positive).WinningTree tree ↔
      Winning M step χ priorityBound W q₀ positive tree := by
  rw [product,supportedPublicTreeMonitor_winning_iff]
  unfold Winning
  apply and_congr_right
  intro _
  apply forall_congr'
  intro branch
  apply imp_congr_right
  intro _
  rw [progress,DetParityAutomaton.comap_accepts_iff,MonitorCompiler.bounded_parity_monitor_effective]
  rfl

instance progressStateDecidableEq : DecidableEq (MonitorCompiler.automaton (B:=B) (K:=L) 0).State := by
  rw [MonitorCompiler.automaton_eq_numeric]
  change DecidableEq (Fin _)
  infer_instance

instance productStateDecidableEq : DecidableEq (product (D:=D) M step χ priorityBound W q₀ positive).State := by
  letI := progressStateDecidableEq (B:=B) (L:=L)
  change DecidableEq (Observation I₁ I₂ O₁ O₂ G Q D B × (MonitorCompiler.automaton (B:=B) (K:=L) 0).State × Bool × Bool)
  infer_instance

def solve : Bool := TreeNonemptiness.nonempty (product (D:=D) M step χ priorityBound W q₀ positive)

theorem solve_correct : solve (D:=D) M step χ priorityBound W q₀ positive = true ↔
    ∃ tree, Winning (D:=D) M step χ priorityBound W q₀ positive tree := by
  rw [solve,TreeNonemptiness.nonempty_correct]
  apply exists_congr
  intro tree
  exact ((product M step χ priorityBound W q₀ positive).acceptsTree_iff_winningTree tree).trans
    (product_winning_iff M step χ priorityBound W q₀ positive tree)

end Characterisation.ComponentGames.Representation.FiniteArena
