/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanPruning

/-! # Numeric minimum-name recording for Piterman deletion stages

Names at or above the NBW state count do not lower the default sentinel.
Repeated entries and malformed node indices are normalized before the search.
-/

namespace DistributedSynthesis.EncodedPitermanMinima
open EncodedPitermanStates EncodedPitermanPruning

def minName (x : Input) (nodes : List Nat) : Nat :=
  FiniteSearch.minWith x.1 ((FiniteSubsets.normalize (bound x) nodes).map (name x))

theorem minName_primrec : Primrec₂ minName :=
  FiniteSearch.minWith_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.list_map (FiniteSubsets.normalize_primrec.comp (bound_primrec.comp Primrec.fst) Primrec.snd)
      (name_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State)) (tree : CompactTreeData A)

theorem minName_correct (nodes : Finset (Node A)) :
    minName (input A number tree) (FiniteSubsets.encode nodes) =
      (tree.minBoundedNameOf A nodes).val := by
  let values := (FiniteSubsets.normalize (2 * Fintype.card A.State)
    (FiniteSubsets.encode nodes)).map (name (input A number tree))
  have hm (r : Nat) : r ∈ values ↔ ∃ q ∈ nodes, (tree.name q).val = r := by
    dsimp only [values]
    rw [FiniteSubsets.normalize_encode_eq_sort]
    simp only [List.map_map, List.mem_map, Finset.mem_sort, Function.comp_apply, name_correct]
  have hmax : (tree.minBoundedNameOf A nodes).val ≤ Fintype.card A.State :=
    Nat.le_of_lt_succ (tree.minBoundedNameOf A nodes).isLt
  change FiniteSearch.minWith (Fintype.card A.State) values = _
  apply le_antisymm
  · by_cases hsmall : (tree.minBoundedNameOf A nodes).val < Fintype.card A.State
    · obtain ⟨q, hq, he⟩ := CompactTreeData.exists_node_name_eq_minBoundedNameOf_of_min_lt_card
        A tree nodes hsmall
      exact FiniteSearch.minWith_le_mem _ _ ((hm _).mpr ⟨q, hq, he⟩)
    · have he : (tree.minBoundedNameOf A nodes).val = Fintype.card A.State := by omega
      rw [he]
      exact FiniteSearch.minWith_le_default _ _
  · apply (FiniteSearch.le_minWith _ _ _).mpr
    refine ⟨hmax, ?_⟩
    intro r hr
    obtain ⟨q, hq, rfl⟩ := (hm r).mp hr
    by_cases hsmall : (tree.name q).val < Fintype.card A.State
    · exact CompactTreeData.minBoundedNameOf_le_of_mem A tree nodes hq hsmall
    · omega

end DistributedSynthesis.EncodedPitermanMinima
