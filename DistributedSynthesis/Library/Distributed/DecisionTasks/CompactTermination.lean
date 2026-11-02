/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib
import DistributedSynthesis.Library.Distributed.DecisionTasks.Model

/-! # Uniform termination on a finite oblivious graph alphabet

An arbitrary-state protocol that terminates irrevocably on every word over a
finite graph alphabet has a uniform round bound. The proof uses compactness of
the product of the finite input space and the space of infinite graph words.
No finite-memory or computability assumption is imposed on the protocol.
-/

namespace DistributedSynthesis.DecisionTasks

variable {P : Type} [Fintype P] {I O : P → Type} [∀ p, Finite (I p)]
variable {St G : Type} [Finite G]

/-- Finite input alphabets and a finite oblivious graph alphabet give a uniform
decision bound. This applies in particular to the fixed IIS adversary. -/
theorem Protocol.uniform_bound (A : Protocol P I St) (out : ∀ p, St → Option (O p))
    (graph : G → Event P)
    (term : ∀ (w : ℕ → G) x p, ∃ r o, out p (A.run (graph ∘ w) x r p) = some o)
    (irrev : ∀ (w : ℕ → G) x p r r', r ≤ r' → ∀ o,
      out p (A.run (graph ∘ w) x r p) = some o →
      out p (A.run (graph ∘ w) x r' p) = some o) :
    ∃ r, ∀ (w : ℕ → G) x p, ∃ o, out p (A.run (graph ∘ w) x r p) = some o := by
  classical
  let X := ∀ p, I p
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := ⟨rfl⟩
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalSpace St := ⊥
  letI : DiscreteTopology St := ⟨rfl⟩
  let C := X × (ℕ → G)
  have hc (r : ℕ) : Continuous (fun z : C => A.run (graph ∘ z.2) z.1 r) := by
    induction r with
    | zero =>
        exact (continuous_of_discreteTopology (f := fun x : X => fun p => A.init p (x p))).comp
          continuous_fst
    | succ r ih =>
        let step : G × (P → St) → (P → St) := fun z p =>
          A.trans p (z.2 p) ((fun q => (q, z.2 q)) '' (graph z.1).inN p)
        exact (continuous_of_discreteTopology (f := step)).comp
          (((continuous_apply r).comp continuous_snd).prodMk ih)
  let U : ℕ → Set C := fun r => {z | ∀ p, ∃ o, out p (A.run (graph ∘ z.2) z.1 r p) = some o}
  have hopen (r : ℕ) : IsOpen (U r) := by
    change IsOpen {z : C | ∀ p, ∃ o, out p (A.run (graph ∘ z.2) z.1 r p) = some o}
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro p
    exact (isOpen_discrete ({s : St | ∃ o, out p s = some o})).preimage
      ((continuous_apply p).comp (hc r))
  have hmono : Monotone U := by
    intro r r' hrr z hz p
    obtain ⟨o, ho⟩ := hz p
    exact ⟨o, irrev z.2 z.1 p r r' hrr o ho⟩
  have hcover : (Set.univ : Set C) ⊆ ⋃ r, U r := by
    intro z _
    choose r o ho using term z.2 z.1
    refine Set.mem_iUnion.mpr ⟨Finset.univ.sup r, fun p => ?_⟩
    exact ⟨o p, irrev z.2 z.1 p (r p) (Finset.univ.sup r)
      (Finset.le_sup (Finset.mem_univ p)) (o p) (ho p)⟩
  obtain ⟨r, hr⟩ := isCompact_univ.elim_directed_cover U hopen hcover
    (fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  exact ⟨r, fun w x p => hr (Set.mem_univ (x, w)) p⟩

end DistributedSynthesis.DecisionTasks
