/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLocalLeaderTest
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderMoves

/-! Complete numbering of the original narrowed leader/follower responses.
The follower sees the monitor state and current joint input; the leader's
response depends only on its current local input. -/
namespace Characterisation.EncodedLocalLeaderTest
open DistributedSynthesis
local instance : BEq Label := instBEqOfDecidableEq

variable (d : Data)
def monitor : BlockRecordMonitor (Fin (receiverInputs d)) (Fin (senderInputs d))
    (Fin (receiverOutputs d)) (Fin (senderOutputs d)) where
  State := Fin (states d)
  stateFinite := inferInstance
  initial := ⟨EncodedParityTables.initial (monitorData d) % states d,Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨EncodedParityTables.next (monitorData d) q.val
    (physicalIndex d a.1.1.val a.1.2.val a.2.1.val a.2.2.val),Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := EncodedParityTables.priority (monitorData d) q.val

abbrev SemanticLabel := NarrowedBlockLabel (Fin (receiverInputs d)) (Fin (senderInputs d))
  (Fin (receiverOutputs d)) (Fin (senderOutputs d)) (monitor d).State

def responseNumber : (monitor d).State × (Fin (receiverInputs d) × Fin (senderInputs d)) ≃ Fin (responseSize d) :=
  FiniteFunctionCodes.prod (Equiv.refl _) (FiniteFunctionCodes.prod (Equiv.refl _) (Equiv.refl _))

def labelEncode (l : SemanticLabel d) : Label :=
  (FiniteFunctionCodes.encode (Equiv.refl _) l.1,
    FiniteFunctionCodes.encode (responseNumber d) (fun qi => l.2 qi.1 qi.2))

theorem labelEncode_mem (l : SemanticLabel d) : labelEncode d l ∈ rawLabels d :=
  List.mem_product.mpr ⟨FiniteFunctionCodes.encode_mem _ _,FiniteFunctionCodes.encode_mem _ _⟩

theorem labelEncode_injective : Function.Injective (labelEncode d) := by
  intro l k eq
  apply Prod.ext
  · funext s
    apply Fin.ext
    have h := congrArg (fun x : Label => x.1.getD s.val 0) eq
    exact (FiniteFunctionCodes.eval_encode (Equiv.refl _) l.1 s).symm.trans
      (h.trans (FiniteFunctionCodes.eval_encode (Equiv.refl _) k.1 s))
  · funext q i
    apply Fin.ext
    have h := congrArg (fun x : Label => x.2.getD (responseNumber d (q,i)).val 0) eq
    simpa only [labelEncode,FiniteFunctionCodes.eval_encode] using h

theorem labelEncode_sound (code : Label) (member : code ∈ rawLabels d) :
    ∃ l : SemanticLabel d, labelEncode d l = code := by
  obtain ⟨hs,hr⟩ := List.mem_product.mp member
  obtain ⟨s,hs⟩ := (FiniteSearch.mem_tables_iff_policy code.1).mp hs
  obtain ⟨r,hr⟩ := (FiniteSearch.mem_tables_iff_policy code.2).mp hr
  refine ⟨(s,fun q i => r (responseNumber d (q,i))),?_⟩
  apply Prod.ext
  · exact hs
  · change List.ofFn (fun i => (r (responseNumber d ((responseNumber d).symm i))).val) = _
    simpa only [Equiv.apply_symm_apply] using hr

noncomputable def labelNumber : SemanticLabel d ≃ Fin (labels d).length :=
  FiniteCodeNumbering.equiv (rawLabels d) (labelEncode d) (labelEncode_injective d)
    (labelEncode_mem d) (labelEncode_sound d)

theorem labelNumber_val (l : SemanticLabel d) : (labelNumber d l).val =
    FiniteCodeNumbering.name (rawLabels d) (labelEncode d l) := rfl

theorem label_get (l : SemanticLabel d) : (labels d)[(labelNumber d l).val] = labelEncode d l := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (labelNumber d l).isLt).symm.trans
  change (FiniteCodeNumbering.unique (rawLabels d))[FiniteCodeNumbering.name (rawLabels d) (labelEncode d l)]? = _
  rw [FiniteCodeNumbering.name,List.getElem?_idxOf
    ((FiniteCodeNumbering.mem_unique _ _).mpr (labelEncode_mem d l))]

theorem next_encode (q : (monitor d).State) (l : SemanticLabel d)
    (r : Fin (receiverInputs d)) (s : Fin (senderInputs d)) :
    next d q.val (labelEncode d l) r.val s.val = ((monitor d).step q (narrowedRecord (monitor d) l q (r,s))).val := by
  unfold next labelEncode
  dsimp only
  have idx : responseIndex d q.val r.val s.val = (responseNumber d (q,(r,s))).val := rfl
  rw [idx,FiniteFunctionCodes.eval_encode]
  have sender := FiniteFunctionCodes.eval_encode (Equiv.refl (Fin (senderInputs d))) l.1 s
  simp only [Equiv.refl_apply] at sender
  rw [sender]
  rfl

theorem edges_encode (q t : (monitor d).State) (l : SemanticLabel d) (s : Fin (senderInputs d)) :
    (q.val,t.val) ∈ edges d (labelEncode d l) s.val ↔
      ∃ r : Fin (receiverInputs d), t = (monitor d).step q (narrowedRecord (monitor d) l q (r,s)) := by
  simp only [edges,List.mem_flatMap,List.mem_range,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨q',hq,r,hr,hq',ht⟩
    subst q'
    refine ⟨⟨r,hr⟩,Fin.ext ?_⟩
    exact ht.symm.trans (next_encode d q l ⟨r,hr⟩ s)
  · rintro ⟨r,rfl⟩
    exact ⟨q.val,q.isLt,r.val,r.isLt,rfl,next_encode d q l r s⟩

theorem priorities_get (q : (monitor d).State) : (priorities d).getD q.val 0 = (monitor d).priority q := by
  unfold priorities
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using q.isLt)]
  simp only [List.getElem_map,List.getElem_range]
  rfl

theorem priorities_range (p : Nat) : p ∈ priorities d ↔ p ∈ ThreadComputable.priorityRange (monitor d) := by
  simp only [priorities,List.mem_map,List.mem_range,ThreadComputable.priorityRange,Finset.mem_image,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨q,hq,hp⟩
    exact ⟨⟨q,hq⟩,hp⟩
  · rintro ⟨q,hp⟩
    exact ⟨q.val,q.isLt,hp⟩

end Characterisation.EncodedLocalLeaderTest
