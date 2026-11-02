/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Syntax
import Mathlib.ModelTheory.Semantics

/-! # Full monadic second-order semantics

Set variables range over `Set M`, including infinite subsets. No enumeration,
finite-set restriction, or decision oracle is built into the semantics.
-/
namespace DistributedSynthesis.MSO

universe u v w
variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

namespace Formula

/-- Interpret an MSO formula in the existing first-order structure on `M`. -/
def Realize : {n m : Nat} → Formula L n m → (Fin n → M) → (Fin m → Set M) → Prop
  | _, _, .firstOrder φ, xs, _ => φ.Realize xs
  | _, _, .mem x X, xs, sets => xs x ∈ sets X
  | _, _, .falsum, _, _ => False
  | _, _, .imp φ ψ, xs, sets => Realize φ xs sets → Realize ψ xs sets
  | _, _, .allNode φ, xs, sets => ∀ x : M, Realize φ (Fin.snoc xs x) sets
  | _, _, .allSet φ, xs, sets => ∀ X : Set M, Realize φ xs (Fin.snoc sets X)

variable {n m : Nat} (xs : Fin n → M) (sets : Fin m → Set M)

@[simp] theorem realize_firstOrder (φ : L.Formula (Fin n)) :
    Realize (.firstOrder φ : Formula L n m) xs sets ↔ φ.Realize xs := Iff.rfl

@[simp] theorem realize_mem (x : Fin n) (X : Fin m) :
    Realize (.mem x X : Formula L n m) xs sets ↔ xs x ∈ sets X := Iff.rfl

@[simp] theorem realize_falsum : Realize (.falsum : Formula L n m) xs sets ↔ False := Iff.rfl

@[simp] theorem realize_imp (φ ψ : Formula L n m) :
    (φ.imp ψ).Realize xs sets ↔ (φ.Realize xs sets → ψ.Realize xs sets) := Iff.rfl

@[simp] theorem realize_not (φ : Formula L n m) :
    φ.not.Realize xs sets ↔ ¬ φ.Realize xs sets := Iff.rfl

@[simp] theorem realize_and (φ ψ : Formula L n m) :
    (φ.and ψ).Realize xs sets ↔ φ.Realize xs sets ∧ ψ.Realize xs sets := by
  classical
  simp [Formula.and]

@[simp] theorem realize_or (φ ψ : Formula L n m) :
    (φ.or ψ).Realize xs sets ↔ φ.Realize xs sets ∨ ψ.Realize xs sets := by
  classical
  by_cases h : φ.Realize xs sets <;> simp [Formula.or, h]

@[simp] theorem realize_iff (φ ψ : Formula L n m) :
    (φ.iff ψ).Realize xs sets ↔ (φ.Realize xs sets ↔ ψ.Realize xs sets) := by
  simp [Formula.iff, iff_def]

@[simp] theorem realize_allNode (φ : Formula L (n + 1) m) :
    φ.allNode.Realize xs sets ↔ ∀ x : M, φ.Realize (Fin.snoc xs x) sets := Iff.rfl

@[simp] theorem realize_allSet (φ : Formula L n (m + 1)) :
    φ.allSet.Realize xs sets ↔ ∀ X : Set M, φ.Realize xs (Fin.snoc sets X) := Iff.rfl

@[simp] theorem realize_exNode (φ : Formula L (n + 1) m) :
    φ.exNode.Realize xs sets ↔ ∃ x : M, φ.Realize (Fin.snoc xs x) sets := by
  classical
  simp [exNode]

@[simp] theorem realize_exSet (φ : Formula L n (m + 1)) :
    φ.exSet.Realize xs sets ↔ ∃ X : Set M, φ.Realize xs (Fin.snoc sets X) := by
  classical
  simp [exSet]

@[simp] theorem realize_truth : (truth : Formula L n m).Realize xs sets := by
  simp [truth]

@[simp] theorem realize_allOf (formulas : List (Formula L n m)) :
    (allOf formulas).Realize xs sets ↔ ∀ φ ∈ formulas, φ.Realize xs sets := by
  induction formulas with
  | nil => simp [allOf]
  | cons φ rest ih =>
      simp only [allOf, List.foldr_cons, realize_and, List.forall_mem_cons]
      exact and_congr Iff.rfl ih

private theorem snoc_comp_lift {n k : Nat} {α : Type*}
    (xs : Fin k → α) (x : α) (f : Fin n → Fin k) :
    Fin.snoc xs x ∘ liftRenaming f = Fin.snoc (xs ∘ f) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Renaming commutes with interpretation, for both individual and set variables. -/
theorem realize_rename {n m k l : Nat} (φ : Formula L n m)
    (f : Fin n → Fin k) (g : Fin m → Fin l)
    (xs : Fin k → M) (sets : Fin l → Set M) :
    (rename f g φ).Realize xs sets ↔ φ.Realize (xs ∘ f) (sets ∘ g) := by
  induction φ generalizing k l with
  | firstOrder φ => simp [rename, FirstOrder.Language.Formula.realize_relabel]
  | mem x X => rfl
  | falsum => rfl
  | imp φ ψ ihφ ihψ => simp only [rename, realize_imp, ihφ, ihψ]
  | allNode φ ih => simp only [rename, realize_allNode, ih, snoc_comp_lift]
  | allSet φ ih => simp only [rename, realize_allSet, ih, snoc_comp_lift]

@[simp] theorem realize_weakenNode (φ : Formula L n m) (x : M) :
    φ.weakenNode.Realize (Fin.snoc xs x) sets ↔ φ.Realize xs sets := by
  simp [weakenNode, realize_rename, Function.comp_def]

@[simp] theorem realize_weakenSet (φ : Formula L n m) (X : Set M) :
    φ.weakenSet.Realize xs (Fin.snoc sets X) ↔ φ.Realize xs sets := by
  simp [weakenSet, realize_rename, Function.comp_def]

end Formula

/-- Satisfaction of a sentence under full second-order semantics. -/
def Satisfies (φ : Sentence L) : Prop := φ.Realize (Fin.elim0 : Fin 0 → M) Fin.elim0

end DistributedSynthesis.MSO
