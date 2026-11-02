/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Semantics

/-! # Finite disjunctions and existential set blocks -/
namespace DistributedSynthesis.MSO.Formula

universe u v w
variable {L : FirstOrder.Language.{u,v}} {n m : Nat}

def anyOf (formulas : List (Formula L n m)) : Formula L n m :=
  formulas.foldr Formula.or .falsum

def ofBool (b : Bool) : Formula L n m := if b then truth else .falsum

/-- Existentially bind every free set variable, retaining the individual context. -/
def exAllSets : {m : Nat} → Formula L n m → Formula L n 0
  | 0, φ => φ
  | _+1, φ => exAllSets φ.exSet

variable {M : Type w} [L.Structure M] (nodes : Fin n → M) (sets : Fin m → Set M)

@[simp] theorem realize_anyOf (formulas : List (Formula L n m)) :
    (anyOf formulas).Realize nodes sets ↔ ∃ φ ∈ formulas, φ.Realize nodes sets := by
  induction formulas with
  | nil => simp [anyOf]
  | cons φ rest ih =>
      change (φ.or (anyOf rest)).Realize nodes sets ↔ _
      rw [realize_or, ih]
      simp

@[simp] theorem realize_ofBool (b : Bool) : (ofBool b : Formula L n m).Realize nodes sets ↔ b = true := by
  cases b <;> simp [ofBool]

@[simp] theorem realize_exAllSets : ∀ {m : Nat} (φ : Formula L n m),
    φ.exAllSets.Realize nodes Fin.elim0 ↔ ∃ sets, φ.Realize nodes sets := by
  intro m
  induction m with
  | zero =>
    intro φ
    constructor
    · intro h
      exact ⟨Fin.elim0,h⟩
    · rintro ⟨sets,h⟩
      have same : sets = Fin.elim0 := Subsingleton.elim _ _
      simpa only [same, exAllSets] using h
  | succ m ih =>
    intro φ
    rw [exAllSets, ih]
    simp only [realize_exSet]
    constructor
    · rintro ⟨sets,X,h⟩
      exact ⟨Fin.snoc sets X,h⟩
    · rintro ⟨sets,h⟩
      refine ⟨Fin.init sets,sets (Fin.last m),?_⟩
      simpa only [Fin.snoc_init_self] using h

end DistributedSynthesis.MSO.Formula
