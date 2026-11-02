/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Semantics
import Mathlib.Logic.Relation

/-! # Reachability expressed in MSO

Reachability is expressed by membership in every successor-closed set containing
the starting point. The proof uses Mathlib's `Relation.ReflTransGen`, with no
finite-domain assumption. This will supply the ancestor relation on full trees.
-/
namespace DistributedSynthesis.MSO.Formula

universe u v w
variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
variable {n m : Nat}

open FirstOrder.Language

/-- Individual equality uses the existing first-order equality formula. -/
def equal (x y : Fin n) : Formula L n m :=
  .firstOrder ((Term.var x).equal (Term.var y))

/-- An application of an existing relation symbol to individual variables. -/
def relation {k : Nat} (r : L.Relations k) (args : Fin k → Fin n) : Formula L n m :=
  .firstOrder (r.formula (fun i => Term.var (args i)))

@[simp] theorem realize_equal (x y : Fin n) (xs : Fin n → M) (sets : Fin m → Set M) :
    (equal x y : Formula L n m).Realize xs sets ↔ xs x = xs y := by
  simp [equal]

@[simp] theorem realize_relation {k : Nat} (r : L.Relations k) (args : Fin k → Fin n)
    (xs : Fin n → M) (sets : Fin m → Set M) :
    (relation r args : Formula L n m).Realize xs sets ↔
      Structure.RelMap r (xs ∘ args) := by
  rfl

/-- The set variable `X` is closed under the binary relation `r`. -/
def closed (r : L.Relations 2) (X : Fin m) : Formula L n m :=
  .allNode (.allNode (
    (relation r ![(Fin.last n).castSucc, Fin.last (n + 1)]).imp
      ((Formula.mem (Fin.last n).castSucc X).imp (Formula.mem (Fin.last (n + 1)) X))))

@[simp] theorem realize_closed (r : L.Relations 2) (X : Fin m)
    (xs : Fin n → M) (sets : Fin m → Set M) :
    (closed r X : Formula L n m).Realize xs sets ↔
      ∀ a b : M, Structure.RelMap r ![a, b] → a ∈ sets X → b ∈ sets X := by
  have values (a b : M) :
      (Fin.snoc (Fin.snoc xs a) b ∘ ![(Fin.last n).castSucc, Fin.last (n + 1)]) = ![a, b] := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) i <;> simp
  simp only [closed, realize_allNode, realize_imp, realize_relation, values, realize_mem,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- Reflexive transitive reachability, as a formula with one bound set variable. -/
def reachable (r : L.Relations 2) (x y : Fin n) : Formula L n m :=
  .allSet (((Formula.mem x (Fin.last m)).and (closed r (Fin.last m))).imp
    (Formula.mem y (Fin.last m)))

/-- Full set quantification makes the closed-set definition exactly reachability. -/
theorem realize_reachable (r : L.Relations 2) (x y : Fin n)
    (xs : Fin n → M) (sets : Fin m → Set M) :
    (reachable r x y : Formula L n m).Realize xs sets ↔
      Relation.ReflTransGen (fun a b : M => Structure.RelMap r ![a, b]) (xs x) (xs y) := by
  simp only [reachable, realize_allSet, realize_imp, realize_and, realize_mem,
    realize_closed, Fin.snoc_last]
  constructor
  · intro every
    exact every {b | Relation.ReflTransGen (fun a b : M => Structure.RelMap r ![a, b]) (xs x) b}
      ⟨Relation.ReflTransGen.refl, fun _ _ edge reaches => reaches.tail edge⟩
  · intro reaches X start
    have preserve {a b : M}
        (path : Relation.ReflTransGen (fun a b : M => Structure.RelMap r ![a, b]) a b) :
        a ∈ X → b ∈ X := by
      induction path with
      | refl => exact id
      | tail _ edge ih => exact fun member => start.2 _ _ edge (ih member)
    exact preserve reaches start.1

end DistributedSynthesis.MSO.Formula
