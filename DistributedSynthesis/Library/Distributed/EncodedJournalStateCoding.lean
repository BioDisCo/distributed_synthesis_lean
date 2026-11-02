/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalTables
import DistributedSynthesis.Library.Distributed.EncodedJournalAssembly
import DistributedSynthesis.Library.Distributed.EncodedJournalSubsetsCorrect

/-! # Exact coding of outer journal states -/
namespace DistributedSynthesis.EncodedJournalStateCoding
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads EncodedJournalMachines
  EncodedJournalSubsets DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
abbrev Semantic := ((A).State × (A).State) ⊕
  (Fin (ordinarySize d) × Finset ((A).State × (A).State)) ⊕
  (Fin (ordinarySize d) × Finset ((A).State × (A).State)) ⊕
  ((Σ _ : Finset (ChainThread A), Fin (chainSize d)) × Finset (ChainThread A)) ⊕
  ((Σ _ : Finset (ChainThread A), Fin (chainSize d)) × Finset (ChainThread A)) ⊕ PUnit.{1}

def encode : Semantic d → EncodedJournalTransitions.State
  | Sum.inl atom => (0,pairedIndex d atom,[],[])
  | Sum.inr (Sum.inl (q,T)) => (1,q.val,atomEncode d T,[])
  | Sum.inr (Sum.inr (Sum.inl (q,T))) => (2,q.val,atomEncode d T,[])
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (q,T)))) => (3,q.2.val,chainEncode d T,chainEncode d q.1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (q,T))))) => (4,q.2.val,chainEncode d T,chainEncode d q.1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => EncodedJournalTransitions.sink

def bounded (n : Nat) (hn : 0 < n) (q : Nat) : Fin n := ⟨q % n,Nat.mod_lt _ hn⟩
theorem bounded_val (n : Nat) (hn : 0 < n) (q : Fin n) : bounded n hn q.val = q :=
  Fin.ext (Nat.mod_eq_of_lt q.isLt)
theorem atomCount_pos : 0 < atomCount d := Nat.mul_pos (stateCount_pos d) (stateCount_pos d)
theorem ordinarySize_pos : 0 < ordinarySize d := Nat.succ_pos _
theorem chainSize_pos : 0 < chainSize d := Nat.succ_pos _

def decode (q : EncodedJournalTransitions.State) : Semantic d :=
  if q.1 = 0 then Sum.inl ((atomEquiv d).symm (bounded (atomCount d) (atomCount_pos d) q.2.1))
  else if q.1 = 1 then Sum.inr (Sum.inl
    (bounded (ordinarySize d) (ordinarySize_pos d) q.2.1,FiniteSetCodes.decode (atomEquiv d) q.2.2.1))
  else if q.1 = 2 then Sum.inr (Sum.inr (Sum.inl
    (bounded (ordinarySize d) (ordinarySize_pos d) q.2.1,FiniteSetCodes.decode (atomEquiv d) q.2.2.1)))
  else if q.1 = 3 then Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (⟨FiniteSetCodes.decode (chainEquiv d) q.2.2.2,bounded (chainSize d) (chainSize_pos d) q.2.1⟩,
      FiniteSetCodes.decode (chainEquiv d) q.2.2.1))))
  else if q.1 = 4 then Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (⟨FiniteSetCodes.decode (chainEquiv d) q.2.2.2,bounded (chainSize d) (chainSize_pos d) q.2.1⟩,
      FiniteSetCodes.decode (chainEquiv d) q.2.2.1)))))
  else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))

theorem decode_encode (q : Semantic d) : decode d (encode d q) = q := by
  rcases q with q | q | q | q | q | q
  · change Sum.inl ((atomEquiv d).symm (bounded _ _ (atomEquiv d q).val)) = (Sum.inl q : Semantic d)
    rw [bounded_val,Equiv.symm_apply_apply]
  · rcases q with ⟨q,T⟩
    change Sum.inr (Sum.inl (bounded _ _ q.val,FiniteSetCodes.decode (atomEquiv d)
      (FiniteSetCodes.encode (atomEquiv d) T))) = (Sum.inr (Sum.inl (q,T)) : Semantic d)
    rw [bounded_val,FiniteSetCodes.decode_encode]
  · rcases q with ⟨q,T⟩
    change Sum.inr (Sum.inr (Sum.inl (bounded _ _ q.val,FiniteSetCodes.decode (atomEquiv d)
      (FiniteSetCodes.encode (atomEquiv d) T)))) = (Sum.inr (Sum.inr (Sum.inl (q,T))) : Semantic d)
    rw [bounded_val,FiniteSetCodes.decode_encode]
  · rcases q with ⟨⟨T,q⟩,S⟩
    change Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (⟨FiniteSetCodes.decode (chainEquiv d) (FiniteSetCodes.encode (chainEquiv d) T),bounded _ _ q.val⟩,
        FiniteSetCodes.decode (chainEquiv d) (FiniteSetCodes.encode (chainEquiv d) S))))) =
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨T,q⟩,S)))) : Semantic d)
    rw [FiniteSetCodes.decode_encode,FiniteSetCodes.decode_encode,bounded_val]
  · rcases q with ⟨⟨T,q⟩,S⟩
    change Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (⟨FiniteSetCodes.decode (chainEquiv d) (FiniteSetCodes.encode (chainEquiv d) T),bounded _ _ q.val⟩,
        FiniteSetCodes.decode (chainEquiv d) (FiniteSetCodes.encode (chainEquiv d) S)))))) =
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨T,q⟩,S))))) : Semantic d)
    rw [FiniteSetCodes.decode_encode,FiniteSetCodes.decode_encode,bounded_val]
  · cases q
    rfl

theorem encode_injective : Function.Injective (encode d) := by
  intro q r h
  exact (decode_encode d q).symm.trans ((congrArg (decode d) h).trans (decode_encode d r))

theorem encode_mem (q : Semantic d) : encode d q ∈ EncodedJournalTables.rawStates d := by
  rcases q with q | q | q | q | q | q
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨pairedIndex d q,List.mem_range.mpr (pairedIndex_lt d q),rfl⟩
  · have h : (q.1.val,atomEncode d q.2) ∈ EncodedJournalTables.ordinaryStates d :=
      List.mem_product.mpr ⟨List.mem_range.mpr q.1.isLt,FiniteSetCodes.codes_complete _ _⟩
    simp only [EncodedJournalTables.rawStates,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨_,h,rfl⟩)))))
  · have h : (q.1.val,atomEncode d q.2) ∈ EncodedJournalTables.ordinaryStates d :=
      List.mem_product.mpr ⟨List.mem_range.mpr q.1.isLt,FiniteSetCodes.codes_complete _ _⟩
    simp only [EncodedJournalTables.rawStates,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨_,h,rfl⟩))))
  · have h : (q.1.2.val,chainEncode d q.2,chainEncode d q.1.1) ∈ EncodedJournalTables.chainStates d :=
      List.mem_product.mpr ⟨List.mem_range.mpr q.1.2.isLt,
        List.mem_product.mpr ⟨FiniteSetCodes.codes_complete _ _,FiniteSetCodes.codes_complete _ _⟩⟩
    simp only [EncodedJournalTables.rawStates,List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨_,h,rfl⟩)))
  · have h : (q.1.2.val,chainEncode d q.2,chainEncode d q.1.1) ∈ EncodedJournalTables.chainStates d :=
      List.mem_product.mpr ⟨List.mem_range.mpr q.1.2.isLt,
        List.mem_product.mpr ⟨FiniteSetCodes.codes_complete _ _,FiniteSetCodes.codes_complete _ _⟩⟩
    simp only [EncodedJournalTables.rawStates,List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨_,h,rfl⟩))
  · exact List.mem_append_right _ (by simp [encode])

theorem codes_sound (c : EncodedJournalTransitions.State) (h : c ∈ EncodedJournalTables.rawStates d) :
    ∃ q : Semantic d, encode d q = c := by
  simp only [EncodedJournalTables.rawStates,List.mem_append,List.mem_map] at h
  rcases h with ((((ha | hl) | hr) | hrl) | hrr) | hs
  · obtain ⟨q,hq,rfl⟩ := ha
    refine ⟨Sum.inl ((atomEquiv d).symm ⟨q,List.mem_range.mp hq⟩),?_⟩
    simp only [encode,← atomEquiv_val,Equiv.apply_symm_apply]
  · obtain ⟨⟨q,T⟩,hq,rfl⟩ := hl
    obtain ⟨hbound,hT⟩ := List.mem_product.mp hq
    obtain ⟨T,rfl⟩ := FiniteSetCodes.codes_sound (atomEquiv d) T hT
    exact ⟨Sum.inr (Sum.inl (⟨q,List.mem_range.mp hbound⟩,T)),rfl⟩
  · obtain ⟨⟨q,T⟩,hq,rfl⟩ := hr
    obtain ⟨hbound,hT⟩ := List.mem_product.mp hq
    obtain ⟨T,rfl⟩ := FiniteSetCodes.codes_sound (atomEquiv d) T hT
    exact ⟨Sum.inr (Sum.inr (Sum.inl (⟨q,List.mem_range.mp hbound⟩,T))),rfl⟩
  · obtain ⟨⟨q,T,S⟩,hq,rfl⟩ := hrl
    obtain ⟨hbound,hT,hS⟩ := (List.mem_product.mp hq).imp_right List.mem_product.mp
    obtain ⟨T,rfl⟩ := FiniteSetCodes.codes_sound (chainEquiv d) T hT
    obtain ⟨S,rfl⟩ := FiniteSetCodes.codes_sound (chainEquiv d) S hS
    exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨S,⟨q,List.mem_range.mp hbound⟩⟩,T)))),rfl⟩
  · obtain ⟨⟨q,T,S⟩,hq,rfl⟩ := hrr
    obtain ⟨hbound,hT,hS⟩ := (List.mem_product.mp hq).imp_right List.mem_product.mp
    obtain ⟨T,rfl⟩ := FiniteSetCodes.codes_sound (chainEquiv d) T hT
    obtain ⟨S,rfl⟩ := FiniteSetCodes.codes_sound (chainEquiv d) S hS
    exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨S,⟨q,List.mem_range.mp hbound⟩⟩,T))))),rfl⟩
  · have hc : c = EncodedJournalTransitions.sink := by simpa using hs
    exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))),hc.symm⟩

noncomputable def number : Semantic d ≃ Fin (EncodedJournalTables.states d).length := by
  unfold EncodedJournalTables.states
  exact FiniteCodeNumbering.equiv (EncodedJournalTables.rawStates d) (encode d)
    (encode_injective d) (encode_mem d) (codes_sound d)

theorem number_val (q : Semantic d) : (number d q).val = EncodedJournalTables.name d (encode d q) := rfl

theorem get_number (q : Semantic d) :
    (EncodedJournalTables.states d)[(number d q).val]? = some (encode d q) := by
  rw [number_val]
  unfold EncodedJournalTables.states EncodedJournalTables.name
  exact FiniteCodeNumbering.get_name (EncodedJournalTables.rawStates d) (encode d) (encode_mem d) q

theorem states_pos : 0 < (EncodedJournalTables.states d).length :=
  Nat.zero_lt_of_lt (number d (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))).isLt
end DistributedSynthesis.EncodedJournalStateCoding
