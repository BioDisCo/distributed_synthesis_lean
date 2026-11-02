/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch

/-! Numeric bounded-walk computation for closing components. The semantic
correctness proof uses Mathlib's finite-path bound. No graph reachability
oracle is supplied as numeric input. -/
namespace Characterisation.EncodedClosingReachability
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Matrix := List (List Bool)
abbrev Data := Nat × Matrix
def lookup (matrix : Matrix) (i j : Nat) := (matrix.getD i []).getD j false
def tabulate (size : Nat) (f : Nat → Nat → Bool) : Matrix :=
  (List.range size).map (fun i => (List.range size).map (f i))
def diagonal (size : Nat) := tabulate size (fun i j => decide (i=j))
def Extend (d : Data) (previous : Matrix) (i j : Nat) : Prop :=
  i=j ∨ ∃ k < d.1, lookup d.2 i k = true ∧ lookup previous k j = true
instance (d : Data) (previous : Matrix) (i j : Nat) : Decidable (Extend d previous i j) := by
  unfold Extend
  infer_instance
def advance (d : Data) (previous : Matrix) := tabulate d.1 (fun i j => decide (Extend d previous i j))
def walks (d : Data) : Nat → Matrix
  | 0 => diagonal d.1
  | n+1 => advance d (walks d n)
def reachable (d : Data) (i j : Nat) := lookup (walks d d.1) i j

theorem lookup_primrec : Primrec (fun x : Matrix × Nat × Nat => lookup x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD false).comp
    ((Primrec.list_getD []).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

theorem tabulate_primrec {X : Type} [Primcodable X] {size : X → Nat} {f : X → Nat → Nat → Bool}
    (hs : Primrec size) (hf : Primrec (fun x : X × Nat × Nat => f x.1 x.2.1 x.2.2)) :
    Primrec (fun x => tabulate (size x) (f x)) := by
  apply Primrec.list_map (Primrec.list_range.comp hs)
  apply Primrec.list_map (Primrec.list_range.comp (hs.comp Primrec.fst))
  exact hf.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))

theorem diagonal_primrec : Primrec diagonal := tabulate_primrec Primrec.id
  (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide

theorem extend_primrec : PrimrecPred (fun x : Data × Matrix × Nat × Nat => Extend x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hd : Primrec (fun x : Data × Matrix × Nat × Nat => x.1) := Primrec.fst
  have hp : Primrec (fun x : Data × Matrix × Nat × Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun x : Data × Matrix × Nat × Nat => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun x : Data × Matrix × Nat × Nat => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  apply PrimrecPred.or (Primrec.eq.comp hi hj)
  apply FiniteSearch.exists_lt (Primrec.fst.comp hd)
  exact (Primrec.eq.comp
    (lookup_primrec.comp (((Primrec.snd.comp hd).comp Primrec.fst).pair
      ((hi.comp Primrec.fst).pair Primrec.snd))) (Primrec.const true)).and
    (Primrec.eq.comp (lookup_primrec.comp ((hp.comp Primrec.fst).pair
      (Primrec.snd.pair (hj.comp Primrec.fst)))) (Primrec.const true))

theorem advance_primrec : Primrec₂ advance := tabulate_primrec (Primrec.fst.comp Primrec.fst)
  (extend_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).decide

theorem walks_primrec : Primrec₂ walks := by
  have h := Primrec.nat_rec (diagonal_primrec.comp Primrec.fst)
    (advance_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq (fun d n => by induction n <;> simp_all [walks])

theorem reachable_primrec : Primrec (fun x : Data × Nat × Nat => reachable x.1 x.2.1 x.2.2) :=
  lookup_primrec.comp ((walks_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)

end Characterisation.EncodedClosingReachability
