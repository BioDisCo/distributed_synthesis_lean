/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderBoundaryInstructions

/-! During a one-way stretch, fix the leader's strategy as a tree indexed
only by its own inputs. Receiver inputs remain universally quantified and
are not supplied to the leader's tree. -/
namespace Characterisation
open DistributedSynthesis

def leaderForwardView {I₁ I₂ : Type*} {p : Proc}
    (base : View I₁ I₂ p) (word : List (PSum I₁ I₂)) : View I₁ I₂ p :=
  word.foldl View.noRecv base

theorem leader_view_append_outgoing {I₁ I₂ : Type*}
    (p : Proc) (h : EnvHistory I₁ I₂) (r : RoundRecord I₁ I₂ Graph Unit Unit)
    (outgoing : r.graph = leaderOutgoingGraph p) :
    currentView p (h++[r]) = View.noRecv (currentView p h) (RoundRecord.input p r) := by
  change currentView p (History.append h r) = _
  cases p
  · rw [currentView_one_append,outgoing]
    rfl
  · rw [currentView_two_append,outgoing]
    rfl

/-- The leader's view over the whole one-way stretch is determined by its
initial view and its own input word, independently of receiver inputs. -/
theorem leader_view_oneway_stretch {I₁ I₂ : Type*}
    (p : Proc) (h u : EnvHistory I₁ I₂)
    (outgoing : ∀ r ∈ u, r.graph = leaderOutgoingGraph p) :
    currentView p (h++u) = leaderForwardView (currentView p h) (inputWord p u) := by
  induction u using List.reverseRecOn with
  | nil => simp [leaderForwardView,inputWord]
  | append_singleton u r ih =>
    have last : r.graph = leaderOutgoingGraph p := outgoing r (by simp)
    have earlier : ∀ s ∈ u, s.graph = leaderOutgoingGraph p :=
      fun s hs => outgoing s (by simp [hs])
    rw [← List.append_assoc,leader_view_append_outgoing p _ r last,ih earlier]
    simp [leaderForwardView,inputWord,List.foldl_append]

theorem leader_oneway_inputs_suffice {I₁ I₂ : Type*}
    (p : Proc) (h k u v : EnvHistory I₁ I₂)
    (outgoingU : ∀ r ∈ u, r.graph = leaderOutgoingGraph p)
    (outgoingV : ∀ r ∈ v, r.graph = leaderOutgoingGraph p)
    (sameStart : currentView p h = currentView p k)
    (sameInputs : inputWord p u = inputWord p v) :
    currentView p (h++u) = currentView p (k++v) := by
  rw [leader_view_oneway_stretch p h u outgoingU,
    leader_view_oneway_stretch p k v outgoingV,sameStart,sameInputs]

/-- At each own-input word, the leader has a table for its next private
input. The full tree can be infinite; each node's table has a finite type
when the input and output alphabets are finite. -/
def leaderStrategyTree {I₁ I₂ O : Type*} {p : Proc}
    (strategy : View I₁ I₂ p → O) (base : View I₁ I₂ p)
    (word : List (PSum I₁ I₂)) (input : PSum I₁ I₂) : O :=
  strategy (View.noRecv (leaderForwardView base word) input)

/-- The tree reproduces the original leader's output in every one-way
continuation, for every possible receiver-input history. -/
theorem leaderStrategyTree_correct {I₁ I₂ O : Type*}
    (p : Proc) (strategy : View I₁ I₂ p → O)
    (h u : EnvHistory I₁ I₂) (r : RoundRecord I₁ I₂ Graph Unit Unit)
    (outgoingU : ∀ s ∈ u, s.graph = leaderOutgoingGraph p)
    (outgoingR : r.graph = leaderOutgoingGraph p) :
    leaderStrategyTree strategy (currentView p h) (inputWord p u) (RoundRecord.input p r) =
      strategy (currentView p (h++u++[r])) := by
  rw [leader_view_append_outgoing p _ r outgoingR,leader_view_oneway_stretch p h u outgoingU]
  rfl

theorem leader_strategy_node_finite {I₁ I₂ O : Type*}
    [Finite I₁] [Finite I₂] [Finite O] : Finite (PSum I₁ I₂ → O) := by
  infer_instance

end Characterisation
