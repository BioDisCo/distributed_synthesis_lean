/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReachability
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingComponents

/-! Exact finite graph reachability and closing component masks. Bounded
walk iteration uses Mathlib's path-length bound for completeness. -/
namespace Characterisation.EncodedClosingReachability
open DistributedSynthesis

theorem tabulate_lookup (size : Nat) (f : Nat → Nat → Bool) (i j : Fin size) :
    lookup (tabulate size f) i.val j.val = f i.val j.val := by
  simp [lookup,tabulate,List.getD_eq_getElem?_getD]

variable {X : Type} (G : SimpleGraph X) (d : Data) (number : X ≃ Fin d.1)
  (adjacent : ∀ u v, lookup d.2 (number u).val (number v).val = true ↔ G.Adj u v)

include adjacent in
theorem walks_correct (n : Nat) (u v : X) :
    lookup (walks d n) (number u).val (number v).val = true ↔
      ∃ p : G.Walk u v, p.length ≤ n := by
  induction n generalizing u v with
  | zero =>
    rw [walks,diagonal,tabulate_lookup,decide_eq_true_eq]
    constructor
    · intro h
      obtain rfl := number.injective (Fin.ext h)
      exact ⟨.nil,Nat.le_refl _⟩
    · rintro ⟨p,hp⟩
      obtain rfl := p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)
      rfl
  | succ n ih =>
    rw [walks,advance,tabulate_lookup,decide_eq_true_eq]
    constructor
    · rintro (same | ⟨k,hk,edge,tail⟩)
      · obtain rfl := number.injective (Fin.ext same)
        exact ⟨.nil,Nat.zero_le _⟩
      · let middle := number.symm ⟨k,hk⟩
        have hm : (number middle).val = k := by simp [middle]
        have hadj : G.Adj u middle := (adjacent u middle).mp (by simpa only [hm] using edge)
        obtain ⟨p,hp⟩ := (ih middle v).mp (by simpa only [hm] using tail)
        exact ⟨.cons hadj p,by simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hp⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => exact Or.inl rfl
      | @cons u w v edge p =>
        exact Or.inr ⟨(number w).val,(number w).isLt,(adjacent u w).mpr edge,
          (ih w v).mpr ⟨p,by simpa only [SimpleGraph.Walk.length_cons,Nat.add_le_add_iff_right] using hp⟩⟩

include adjacent in
theorem reachable_correct [Fintype X] (u v : X) :
    reachable d (number u).val (number v).val = true ↔ G.Reachable u v := by
  rw [reachable,walks_correct G d number adjacent]
  constructor
  · rintro ⟨p,_⟩
    exact ⟨p⟩
  · intro reachable
    apply reachable.elim_path
    intro p
    have count : Fintype.card X = d.1 := by simpa using Fintype.card_congr number
    exact ⟨p.val,Nat.le_of_lt (by simpa only [count] using p.property.length_lt)⟩

section Encoding
variable {N : Nat} (numbering : X ≃ Fin N) [DecidableRel G.Adj]

def encode : Data :=
  (N,List.ofFn (fun i => List.ofFn (fun j => decide (G.Adj (numbering.symm i) (numbering.symm j)))))

theorem encode_adjacent (u v : X) :
    lookup (encode G numbering).2 (numbering u).val (numbering v).val = true ↔ G.Adj u v := by
  simp [lookup,encode,List.getD_eq_getElem?_getD]

theorem reachable_encode [Fintype X] (u v : X) :
    reachable (encode G numbering) (numbering u).val (numbering v).val = true ↔ G.Reachable u v :=
  reachable_correct G (encode G numbering) numbering (encode_adjacent G numbering) u v

end Encoding

end Characterisation.EncodedClosingReachability
