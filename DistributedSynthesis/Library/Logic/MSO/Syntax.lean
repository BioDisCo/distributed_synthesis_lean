/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.ModelTheory.Syntax

/-! # Monadic second-order syntax

The first-order fragment is Mathlib's existing syntax, including its language,
terms, and binding operations. This extension adds node-set membership and
quantification over sets. The two indices count the individual and set variables
in scope; each quantifier appends its new variable at the last index.
-/
namespace DistributedSynthesis.MSO

universe u v
variable (L : FirstOrder.Language.{u, v})

/-- Full MSO over a first-order language. `firstOrder` embeds a finite syntactic
formula, not an arbitrary semantic predicate. -/
inductive Formula : Nat → Nat → Type (max u v)
  | firstOrder {n m} (φ : L.Formula (Fin n)) : Formula n m
  | mem {n m} (x : Fin n) (X : Fin m) : Formula n m
  | falsum {n m} : Formula n m
  | imp {n m} (φ ψ : Formula n m) : Formula n m
  | allNode {n m} (φ : Formula (n + 1) m) : Formula n m
  | allSet {n m} (φ : Formula n (m + 1)) : Formula n m

abbrev Sentence := Formula L 0 0

namespace Formula
variable {L} {n m : Nat}

protected def not (φ : Formula L n m) : Formula L n m := .imp φ .falsum
protected def and (φ ψ : Formula L n m) : Formula L n m := (Formula.imp φ ψ.not).not
protected def or (φ ψ : Formula L n m) : Formula L n m := .imp φ.not ψ
protected def iff (φ ψ : Formula L n m) : Formula L n m := (φ.imp ψ).and (ψ.imp φ)

def exNode (φ : Formula L (n + 1) m) : Formula L n m := (Formula.allNode φ.not).not
def exSet (φ : Formula L n (m + 1)) : Formula L n m := (Formula.allSet φ.not).not

def truth : Formula L n m := Formula.falsum.not

def allOf (formulas : List (Formula L n m)) : Formula L n m :=
  formulas.foldr Formula.and truth

/-- Extend a variable renaming across one binder using Mathlib's `Fin` operations. -/
def liftRenaming {n k : Nat} (f : Fin n → Fin k) : Fin (n + 1) → Fin (k + 1) :=
  Fin.lastCases (Fin.last k) (fun i => (f i).castSucc)

@[simp] theorem liftRenaming_last {n k : Nat} (f : Fin n → Fin k) :
    liftRenaming f (Fin.last n) = Fin.last k := by simp [liftRenaming]

@[simp] theorem liftRenaming_castSucc {n k : Nat} (f : Fin n → Fin k) (i : Fin n) :
    liftRenaming f i.castSucc = (f i).castSucc := by simp [liftRenaming]

/-- Capture-avoiding renaming for the two sorts of variables. -/
def rename : {n m k l : Nat} → (Fin n → Fin k) → (Fin m → Fin l) →
    Formula L n m → Formula L k l
  | _, _, _, _, f, _, .firstOrder φ => .firstOrder (φ.relabel f)
  | _, _, _, _, f, g, .mem x X => .mem (f x) (g X)
  | _, _, _, _, _, _, .falsum => .falsum
  | _, _, _, _, f, g, .imp φ ψ => .imp (rename f g φ) (rename f g ψ)
  | _, _, _, _, f, g, .allNode φ => .allNode (rename (liftRenaming f) g φ)
  | _, _, _, _, f, g, .allSet φ => .allSet (rename f (liftRenaming g) φ)

/-- Add an unused individual variable at the end of the context. -/
def weakenNode (φ : Formula L n m) : Formula L (n + 1) m := rename Fin.castSucc id φ

/-- Add an unused set variable at the end of the context. -/
def weakenSet (φ : Formula L n m) : Formula L n (m + 1) := rename id Fin.castSucc φ

end Formula
end DistributedSynthesis.MSO
