/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! The precise topological meaning of open holes. This file does not yet
construct the manuscript's map from graph sequences to real coordinates. -/

namespace Characterisation

open Set

def HasOpenHoles {X : Type*} [TopologicalSpace X] (S : Set X) : Prop :=
  ∀ U, IsOpen U → U.Nonempty →
    ∃ V, IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧ Disjoint V S

theorem openHoles_iff_interior_closure_empty {X : Type*}
    [TopologicalSpace X] (S : Set X) :
    HasOpenHoles S ↔ interior (closure S) = ∅ := by
  constructor
  · intro holes
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨V, hv, ⟨y, hy⟩, sub, disj⟩ :=
      holes (interior (closure S)) isOpen_interior ⟨x, hx⟩
    have hc : y ∈ closure S := interior_subset (sub hy)
    obtain ⟨z, hzV, hzS⟩ := mem_closure_iff.mp hc V hv hy
    exact Set.disjoint_left.mp disj hzV hzS
  · intro empty U hu hne
    have dense : Dense (closure S)ᶜ :=
      interior_eq_empty_iff_dense_compl.mp empty
    refine ⟨U ∩ (closure S)ᶜ, hu.inter isClosed_closure.isOpen_compl,
      dense.inter_open_nonempty U hu hne, inter_subset_left, ?_⟩
    exact Set.disjoint_left.mpr (fun x hx hs => hx.2 (subset_closure hs))

/-- Interval formulation on the real line. For the conjecture itself, use
`HasOpenHoles` on the subtype `Set.Icc (0 : ℝ) 1`. -/
def HasIntervalHoles (S : Set ℝ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ c d : ℝ,
    c < d ∧ Ioo c d ⊆ Ioo a b ∧ Disjoint (Ioo c d) S

theorem intervalHoles_iff_openHoles (S : Set ℝ) :
    HasIntervalHoles S ↔ HasOpenHoles S := by
  constructor
  · intro holes U hu hne
    obtain ⟨a, b, hab, hsub⟩ := hu.exists_Ioo_subset hne
    obtain ⟨c, d, hcd, hsub', disj⟩ := holes a b hab
    exact ⟨Ioo c d, isOpen_Ioo, Set.nonempty_Ioo.mpr hcd,
      hsub'.trans hsub, disj⟩
  · intro holes a b hab
    obtain ⟨V, hv, hne, hsub, disj⟩ :=
      holes (Ioo a b) isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
    obtain ⟨c, d, hcd, hsub'⟩ := hv.exists_Ioo_subset hne
    exact ⟨c, d, hcd, hsub'.trans hsub, disj.mono_left hsub'⟩

theorem intervalHoles_iff_interior_closure_empty (S : Set ℝ) :
    HasIntervalHoles S ↔ interior (closure S) = ∅ :=
  (intervalHoles_iff_openHoles S).trans (openHoles_iff_interior_closure_empty S)

end Characterisation
