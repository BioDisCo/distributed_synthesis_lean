/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanStates

/-! # Numeric increasing-order allocation for Piterman's second stage

The rank of a triggering node is its index in the normalized trigger list.
It receives the inactive node of the same rank and name `activeCount + rank`.
These operations are uniform numeric functions, and agree with the finite-set
order isomorphisms used by the existing executable allocation.
-/

namespace DistributedSynthesis.EncodedPitermanAllocation
open FiniteSubsets

def rank (n : Nat) (triggers : List Nat) (q : Nat) : Nat := (normalize n triggers).idxOf q

def child (n : Nat) (triggers inactive : List Nat) (q : Nat) : Nat :=
  if q ∈ normalize n triggers then
    EncodedPitermanStates.read (normalize n inactive) (rank n triggers q)
  else 0

def name (n : Nat) (active triggers : List Nat) (q : Nat) : Nat :=
  if q ∈ normalize n triggers then (normalize n active).length + rank n triggers q else 0

theorem rank_primrec : Primrec (fun x : Nat × List Nat × Nat => rank x.1 x.2.1 x.2.2) :=
  Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd)
    (normalize_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))

theorem child_primrec :
    Primrec (fun x : Nat × List Nat × List Nat × Nat => child x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hn : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.1) := Primrec.fst
  have ht : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact Primrec.ite (hm.comp (normalize_primrec.comp hn ht) hq)
    (EncodedPitermanStates.read_primrec.comp (normalize_primrec.comp hn hi)
      (rank_primrec.comp (hn.pair (ht.pair hq)))) (Primrec.const 0)

theorem name_primrec :
    Primrec (fun x : Nat × List Nat × List Nat × Nat => name x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hn : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.1) := Primrec.fst
  have ha : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun x : Nat × List Nat × List Nat × Nat => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact Primrec.ite (hm.comp (normalize_primrec.comp hn ht) hq)
    (Primrec.nat_add.comp (Primrec.list_length.comp (normalize_primrec.comp hn ha))
      (rank_primrec.comp (hn.pair (ht.pair hq)))) (Primrec.const 0)

theorem rank_correct {n : Nat} (s : Finset (Fin n)) (q : s) :
    rank n (encode s) q.val.val = ((s.orderIsoOfFin rfl).symm q).val := by
  rw [rank, normalize_encode_eq_sort, idxOf_map_val, Finset.orderIsoOfFin_symm_apply]

theorem read_correct {n : Nat} (s : Finset (Fin n)) (i : Fin s.card) :
    EncodedPitermanStates.read (normalize n (encode s)) i.val =
      ((s.orderIsoOfFin rfl) i).val.val := by
  rw [normalize_encode_eq_sort]
  simp only [EncodedPitermanStates.read, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simpa using i.isLt)]
  rfl

theorem child_correct {n : Nat} (triggers inactive : Finset (Fin n))
    (hspace : triggers.card ≤ inactive.card) (q : triggers) :
    child n (encode triggers) (encode inactive) q.val.val =
      ((inactive.orderIsoOfFin rfl)
        ⟨((triggers.orderIsoOfFin rfl).symm q).val,
          lt_of_lt_of_le ((triggers.orderIsoOfFin rfl).symm q).isLt hspace⟩).val.val := by
  have hq : q.val.val ∈ normalize n (encode triggers) := by
    rw [← mem_decode n _ q.val, decode_normalize, decode_encode]
    exact q.property
  rw [child, if_pos hq, rank_correct]
  exact read_correct inactive ⟨((triggers.orderIsoOfFin rfl).symm q).val,
    lt_of_lt_of_le ((triggers.orderIsoOfFin rfl).symm q).isLt hspace⟩

theorem name_correct {n : Nat} (active triggers : Finset (Fin n)) (q : triggers) :
    name n (encode active) (encode triggers) q.val.val =
      active.card + ((triggers.orderIsoOfFin rfl).symm q).val := by
  have hq : q.val.val ∈ normalize n (encode triggers) := by
    rw [← mem_decode n _ q.val, decode_normalize, decode_encode]
    exact q.property
  rw [name, if_pos hq, rank_correct, normalize_encode_eq_sort]
  simp

open NondetBuchiAutomaton.Piterman

variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (decAccept : DecidablePred A.accepting) (tree : CompactTreeData A)
  (hbound : ∀ node, tree.active node = true → (tree.name node).val < Fintype.card A.State)
  (hinjective : ∀ left right, tree.active left = true → tree.active right = true →
    tree.name left = tree.name right → left = right)
  (hconsecutive : ∀ k : Nat, k < Fintype.card A.State →
    (∃ node, tree.active node ∧ (tree.name node).val = k) →
    ∀ j : Nat, j < k → ∃ node, tree.active node ∧ (tree.name node).val = j)

/-- Agreement with the actual allocation used by the executable compiler,
including the fallback for nodes which do not trigger child creation. -/
theorem child_eq_plan (q : Node A) :
    child (2 * Fintype.card A.State)
      (encode (Computable.stage2Triggers A decAccept tree)) (encode (tree.inactiveNodes A)) q.val =
      ((Computable.stage2PlanOfBounds A decAccept tree hbound hinjective hconsecutive).freshChild q).val := by
  let triggers := Computable.stage2Triggers A decAccept tree
  have hspace : triggers.card ≤ (tree.inactiveNodes A).card := by
    rw [show triggers = tree.stage2Triggers A from Computable.stage2Triggers_eq A decAccept tree]
    exact CompactTreeData.stage2Triggers_card_le_inactiveNodes_of_active_card_le A tree
      (CompactTreeData.activeNodes_card_le_of_name_bound_injective A tree hbound hinjective)
  have hm : q.val ∈ normalize (2 * Fintype.card A.State) (encode triggers) ↔ q ∈ triggers := by
    rw [← mem_decode _ _ q, decode_normalize, decode_encode]
  dsimp only [triggers] at hm
  by_cases hq : q ∈ Computable.stage2Triggers A decAccept tree
  · have h := child_correct triggers (tree.inactiveNodes A) hspace ⟨q, hq⟩
    simpa only [triggers, Computable.stage2PlanOfBounds, dif_pos hq] using h
  · simp only [child, show ¬q.val ∈ normalize (2 * Fintype.card A.State)
        (encode (Computable.stage2Triggers A decAccept tree))
        from fun h => hq (hm.mp h), if_false,
      Computable.stage2PlanOfBounds, dif_neg hq, root]

theorem name_eq_plan (q : Node A) :
    name (2 * Fintype.card A.State)
      (encode (tree.activeNodes A)) (encode (Computable.stage2Triggers A decAccept tree)) q.val =
      ((Computable.stage2PlanOfBounds A decAccept tree hbound hinjective hconsecutive).freshName q).val := by
  let triggers := Computable.stage2Triggers A decAccept tree
  have hm : q.val ∈ normalize (2 * Fintype.card A.State) (encode triggers) ↔ q ∈ triggers := by
    rw [← mem_decode _ _ q, decode_normalize, decode_encode]
  dsimp only [triggers] at hm
  by_cases hq : q ∈ Computable.stage2Triggers A decAccept tree
  · have h := name_correct (tree.activeNodes A) triggers ⟨q, hq⟩
    simpa only [triggers, Computable.stage2PlanOfBounds, dif_pos hq] using h
  · simp only [name, show ¬q.val ∈ normalize (2 * Fintype.card A.State)
        (encode (Computable.stage2Triggers A decAccept tree))
        from fun h => hq (hm.mp h), if_false,
      Computable.stage2PlanOfBounds, dif_neg hq, root]

end DistributedSynthesis.EncodedPitermanAllocation
