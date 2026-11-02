/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PieceTransitions
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderCheckpoints

/-! Local-view preservation for the proposed fixed-length block construction.
These lemmas concern actual environment histories. They do not assume a finite
game reduction or a normalization theorem for winning strategies. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

/-- Replacing a family of distinct roots that share one process's view by
members of the same family preserves both local-view equivalence relations. -/
theorem common_view_root_map {I₁ I₂ R : Type*}
    (root : R → EnvHistory I₁ I₂) (injective : Function.Injective root)
    (leader : Proc) (common : ∀ i j, currentView leader (root i) = currentView leader (root j))
    (replace : R → R) (p : Proc) (i j : R)
    (same : currentView p (root i) = currentView p (root j)) :
    currentView p (root (replace i)) = currentView p (root (replace j)) := by
  by_cases eq : p = leader
  · subst p
    exact common _ _
  · have roots : root i = root j := by
      cases p <;> cases leader
      · exact False.elim (eq rfl)
      · exact joint_env_history _ _ same (common i j)
      · exact joint_env_history _ _ (common i j) same
      · exact False.elim (eq rfl)
    rw [injective roots]

/-- A homomorphism of both root view relations remains a homomorphism after
one round, with each history retaining its own input and graph event. -/
theorem append_round_preserves_views {I₁ I₂ : Type*}
    (h k h' k' : EnvHistory I₁ I₂)
    (preserves : ∀ p, currentView p h = currentView p k →
      currentView p h' = currentView p k')
    (r s : RoundRecord I₁ I₂ Graph Unit Unit) (p : Proc)
    (same : currentView p (h ++ [r]) = currentView p (k ++ [s])) :
    currentView p (h' ++ [r]) = currentView p (k' ++ [s]) := by
  change currentView p (History.append h r) = currentView p (History.append k s) at same
  change currentView p (History.append h' r) = currentView p (History.append k' s)
  cases p
  · rw [currentView_one_append, currentView_one_append] at same ⊢
    cases rg : r.graph <;> cases sg : s.graph <;>
      simp only [rg, sg, Proc.other, View.recv.injEq, View.noRecv.injEq,
        reduceCtorEq] at same ⊢
    all_goals first
      | contradiction
      | exact ⟨preserves .one same.1, same.2.1, preserves .two same.2.2.1, same.2.2.2⟩
      | exact ⟨preserves .one same.1, same.2⟩
  · rw [currentView_two_append, currentView_two_append] at same ⊢
    cases rg : r.graph <;> cases sg : s.graph <;>
      simp only [rg, sg, Proc.other, View.recv.injEq, View.noRecv.injEq,
        reduceCtorEq] at same ⊢
    all_goals first
      | contradiction
      | exact ⟨preserves .two same.1, same.2.1, preserves .one same.2.2.1, same.2.2.2⟩
      | exact ⟨preserves .two same.1, same.2⟩

/-- Root replacement preserves local-view equality after arbitrary suffixes
of the same length. The suffixes themselves are not replaced. -/
theorem append_preserves_views {I₁ I₂ : Type*}
    (h k h' k' : EnvHistory I₁ I₂)
    (preserves : ∀ p, currentView p h = currentView p k →
      currentView p h' = currentView p k')
    (u v : EnvHistory I₁ I₂) (lengths : List.length u = List.length v)
    (p : Proc) (same : currentView p (h ++ u) = currentView p (k ++ v)) :
    currentView p (h' ++ u) = currentView p (k' ++ v) := by
  induction u using List.reverseRecOn generalizing v p with
  | nil =>
    have empty : v = [] := List.length_eq_zero_iff.mp (by simpa using lengths.symm)
    subst v
    simpa using preserves p (by simpa using same)
  | append_singleton u r ih =>
    cases v using List.reverseRecOn with
    | nil => simp at lengths
    | append_singleton v s =>
      have len : List.length u = List.length v := by simpa using lengths
      simp only [← List.append_assoc] at same ⊢
      exact append_round_preserves_views _ _ _ _ (fun q eq => ih v len q eq) r s p same

/-- The common old view theorem supplies a common root view at the end of
a block of exactly `d` rounds. No bound on the size of the component is used. -/
theorem common_roots_of_common_lag {I₁ I₂ R : Type*}
    (root suffix : R → EnvHistory I₁ I₂) (d : Nat)
    (lengths : ∀ i, List.length (suffix i) = d) (p : Proc)
    (common : ∀ i j, lagView d (currentView p (root i ++ suffix i)) =
      lagView d (currentView p (root j ++ suffix j))) :
    ∀ i j, currentView p (root i) = currentView p (root j) := by
  intro i j
  have eq := common i j
  rw [← lengths i, lagView_suffix, lengths i, ← lengths j, lagView_suffix] at eq
  exact eq

theorem lagView_succ_outer {I₁ I₂ : Type*} {p : Proc} (d : Nat) (v : View I₁ I₂ p) :
    lagView (d+1) v = lagView 1 (lagView d v) := by
  induction d generalizing v with
  | zero => rfl
  | succ d ih => exact ih v.nonFringe.previousView

/-- The existing nowhere-dense, omega-regular theorem gives a positive
fixed block length. In every live ending component, all participating roots
share one process's view at the beginning of that block. -/
theorem holes_block_common_root {I₁ I₂ : Type*}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ D, 0 < D ∧ ∀ (R : Type) (anchor : EnvHistory I₁ I₂),
      LivePrefix A (History.graphSequence anchor) →
      ∀ root suffix : R → EnvHistory I₁ I₂,
        (∀ i, List.length (suffix i) = D) →
        (∀ i, InputConnected (LivePrefix A) anchor (root i ++ suffix i)) →
        ∃ p, ∀ i j, currentView p (root i) = currentView p (root j) := by
  obtain ⟨d, common⟩ := holes_common_past_view (I₁ := I₁) (I₂ := I₂) A regular holes
  refine ⟨d+1, by omega, ?_⟩
  intro R anchor live root suffix lengths connected
  obtain ⟨p, shared⟩ := common anchor live
  refine ⟨p, common_roots_of_common_lag root suffix (d+1) lengths p ?_⟩
  intro i j
  rw [lagView_succ_outer d, lagView_succ_outer d]
  exact congrArg (lagView 1) ((shared _ (connected i)).symm.trans (shared _ (connected j)))

end Characterisation.PeriodicBlocks
