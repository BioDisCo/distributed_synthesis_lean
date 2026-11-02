/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Representatives

/-! Executable enumeration of the candidate folds. The construction does not
need to compute the ordinal ranks used to prove that a winning choice exists. -/

namespace Characterisation.PeriodicBlocks

/-- A fold chooses one member of each nonempty type class. -/
def ValidFold {R T : Type*} (key : R → T) (fold : R → R) : Prop :=
  (∀ i, key (fold i) = key i) ∧ (∀ i j, key i = key j → fold i = fold j)

instance {R T : Type*} [Fintype R] [DecidableEq R] [DecidableEq T]
    (key : R → T) (fold : R → R) : Decidable (ValidFold key fold) := by
  unfold ValidFold
  infer_instance

/-- All candidate folds are enumerated from the finite type assignment. -/
def foldChoices {R T : Type*} [Fintype R] [DecidableEq R] [DecidableEq T]
    (key : R → T) : Finset (R → R) :=
  Finset.univ.filter (ValidFold key)

theorem mem_foldChoices {R T : Type*} [Fintype R] [DecidableEq R] [DecidableEq T]
    (key : R → T) (fold : R → R) : fold ∈ foldChoices key ↔ ValidFold key fold := by
  simp only [foldChoices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ValidFold.idempotent {R T : Type*} {key : R → T} {fold : R → R}
    (valid : ValidFold key fold) (i : R) : fold (fold i) = fold i :=
  valid.2 _ _ (valid.1 i)

/-- The rank-minimal fold is among the executable candidate choices. -/
theorem representative_mem_foldChoices {R T Rank : Type*}
    [Fintype R] [DecidableEq R] [DecidableEq T] [LinearOrder Rank] [WellFoundedLT Rank]
    (key : R → T) (rank : R → Rank) : representative key rank ∈ foldChoices key := by
  rw [mem_foldChoices]
  exact ⟨representative_key key rank, fun _ _ eq => representative_eq key rank eq⟩

/-- Every candidate, rather than only the rank-minimal choice, satisfies
the same uniform bound on its fixed endpoints. -/
theorem ValidFold.endpoint_bound {R T Z : Type*} [Finite T] [Finite Z]
    {key : R → T} {fold : R → R} (valid : ValidFold key fold) :
    Finite {x : R × Z // fold x.1 = x.1} ∧
      Nat.card {x : R × Z // fold x.1 = x.1} ≤ Nat.card T * Nat.card Z := by
  let code : {x : R × Z // fold x.1 = x.1} → T × Z := fun x => (key x.val.1, x.val.2)
  have injective : Function.Injective code := by
    intro x y same
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.symm.trans ((valid.2 _ _ (congrArg Prod.fst same)).trans y.property)
    · exact congrArg (fun x : T × Z => x.2) same
  refine ⟨Finite.of_injective code injective, ?_⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective code injective

end Characterisation.PeriodicBlocks
