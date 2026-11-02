/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ExecutionSafety
import Mathlib.Topology.Constructions

/-! Finite-prefix cylinders, density, and fixed-strategy safety transfer to
the closure. Uses Mathlib product topology and the existing causality notion. -/
namespace Characterisation
open DistributedSynthesis

variable {α β : Type*} [TopologicalSpace α] [DiscreteTopology α]

/-- A finite prefix cylinder is open in the standard product topology. -/
theorem isOpen_agreeBefore (x : Nat → α) (n : Nat) :
    IsOpen {y | AgreeBefore n x y} := by
  have h : IsOpen (⋂ k ∈ Finset.range n, {y : Nat → α | y k = x k}) :=
    isOpen_biInter_finset fun k _ => by
      have hk : Continuous (fun y : Nat → α => y k) := continuous_apply k
      exact hk.isOpen_preimage {x k} (isOpen_discrete _)
  convert h using 1
  ext y
  simp only [Set.mem_setOf_eq, AgreeBefore, Set.mem_iInter, Finset.mem_range]
  exact forall_congr' fun k => imp_congr_right fun _ => eq_comm

/-- Every finite prefix of a point in the closure occurs in the adversary. -/
theorem closure_prefix (A : Set (Nat → α)) {x : Nat → α} (hx : x ∈ closure A) (n : Nat) :
    ∃ y ∈ A, AgreeBefore n x y := by
  obtain ⟨y, agree, member⟩ := mem_closure_iff.mp hx _ (isOpen_agreeBefore x n)
    (show AgreeBefore n x x from fun _ _ => rfl)
  exact ⟨y,member,agree⟩

/-- The finite-prefix density used by the existing library is exactly
ordinary density in the product of discrete alphabets. -/
theorem prefixDense_iff_dense (A : Set (Nat → α)) : PrefixDense A ↔ Dense A := by
  constructor
  · intro dense x
    choose y member agree using dense x
    have limit : Filter.Tendsto y Filter.atTop (nhds x) := by
      apply tendsto_pi_nhds.mpr
      intro k
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      exact Filter.eventually_atTop.mpr ⟨k+1, fun n hn => agree n k (by omega)⟩
    exact isClosed_closure.mem_of_tendsto limit
      (Filter.Eventually.of_forall fun n => subset_closure (member n))
  · intro dense x n
    exact closure_prefix A (dense x) n

/-- Lemma safety:is:safe, for the same fixed causal execution map. No
regularity, finite-memory, or closed-adversary assumption is used. -/
theorem safety_closure_transfer (A : Set (Nat → α))
    (run : (Nat → α) → (Nat → β)) (causal : Causal run)
    (S : Set (Nat → β)) (safety : IsSafety S) :
    (∀ x ∈ A, run x ∈ S) ↔ (∀ x ∈ closure A, run x ∈ S) := by
  constructor
  · intro win x hx
    by_contra bad
    obtain ⟨n, forbidden⟩ := safety (run x) bad
    obtain ⟨y,hy,agree⟩ := closure_prefix A hx n
    exact forbidden (run y) (causal x y n agree) (win y hy)
  · intro win x hx
    exact win x (subset_closure hx)

end Characterisation
