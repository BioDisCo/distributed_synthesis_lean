/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabet
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderHandoverProgress

/-! Exact coverage of the existing numbered leader alphabet. Annotation
numbering is a proof parameter; executable enumeration uses only its finite
count. Empty families are retained and need no default annotation. -/
namespace Characterisation.EncodedLeaderAlphabet
open DistributedSynthesis

private theorem functionEncode_injective {X : Type} {n m : Nat} (e : X ≃ Fin n) :
    Function.Injective (FiniteFunctionCodes.encode (m:=m) e) := by
  intro f g equal
  funext x
  apply Fin.ext
  have h := congrArg (fun xs : List Nat => xs.getD (e x).val 0) equal
  simpa only [FiniteFunctionCodes.eval_encode] using h

private theorem functionEncode_sound {X Q : Type} {n m : Nat}
    (e : X ≃ Fin n) (number : Q ≃ Fin m) (xs : List Nat)
    (member : xs ∈ FiniteSearch.tables m n) :
    ∃ f : X → Q, FiniteFunctionCodes.encode e (number ∘ f) = xs := by
  obtain ⟨policy,equal⟩ := (FiniteSearch.mem_tables_iff_policy xs).mp member
  refine ⟨fun x => number.symm (policy (e x)),?_⟩
  simpa only [FiniteFunctionCodes.encode,Function.comp_apply,Equiv.apply_symm_apply] using equal

def matrixEncode {n : Nat} (shape : Fin n → Fin n → Bool) :=
  FiniteFunctionCodes.encode finProdFinEquiv (fun ij => finTwoEquiv.symm (shape ij.1 ij.2))

theorem matrixEncode_injective {n : Nat} : Function.Injective (@matrixEncode n) := by
  intro left right equal
  have functions := functionEncode_injective finProdFinEquiv equal
  funext i j
  exact finTwoEquiv.symm.injective (congrFun functions (i,j))

theorem matrixEncode_mem {n : Nat} (shape : Fin n → Fin n → Bool) :
    matrixEncode shape ∈ FiniteSearch.tables 2 (n*n) := FiniteFunctionCodes.encode_mem _ _

theorem matrixEncode_sound {n : Nat} (xs : List Nat)
    (member : xs ∈ FiniteSearch.tables 2 (n*n)) :
    ∃ shape : Fin n → Fin n → Bool, matrixEncode shape = xs := by
  obtain ⟨f,equal⟩ := functionEncode_sound finProdFinEquiv finTwoEquiv.symm xs member
  exact ⟨fun i j => f (i,j),equal⟩

variable {Q : Type} {B N C : Nat} (number : Q ≃ Fin N)

def headerEncode (header : SwitchInterface Q B) : Header :=
  (header.1.val,matrixEncode (header.2.1 .one),matrixEncode (header.2.1 .two),
    FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ header.2.2))

theorem headerEncode_injective : Function.Injective (headerEncode (B:=B) number) := by
  rintro ⟨n,left,label⟩ ⟨m,right,label'⟩ equal
  simp only [headerEncode,Prod.mk.injEq] at equal
  obtain ⟨hn,hleft,hright,hlabel⟩ := equal
  have hn' : n=m := Fin.ext hn
  cases hn'
  apply congrArg (Sigma.mk n)
  apply Prod.ext
  · funext p
    cases p
    · exact matrixEncode_injective hleft
    · exact matrixEncode_injective hright
  · have functions := functionEncode_injective (Equiv.refl _) hlabel
    funext i
    exact number.injective (congrFun functions i)

theorem headerEncode_mem (header : SwitchInterface Q B) :
    headerEncode number header ∈ headers (B,N,C) := by
  apply List.mem_flatMap.mpr
  refine ⟨header.1.val,List.mem_range.mpr header.1.isLt,?_⟩
  apply List.mem_map.mpr
  exact ⟨_,List.mem_product.mpr ⟨matrixEncode_mem _,List.mem_product.mpr
    ⟨matrixEncode_mem _,FiniteFunctionCodes.encode_mem _ _⟩⟩,rfl⟩

theorem headerEncode_sound (code : Header) (member : code ∈ headers (B,N,C)) :
    ∃ header : SwitchInterface Q B, headerEncode number header = code := by
  obtain ⟨n,hn,hm⟩ := List.mem_flatMap.mp member
  have mapped : ∃ data ∈ (FiniteSearch.tables 2 (n*n)).product
      ((FiniteSearch.tables 2 (n*n)).product (FiniteSearch.tables N n)), (n,data)=code := by
    exact List.mem_map.mp hm
  obtain ⟨⟨left,right,label⟩,hdata,hcode⟩ := mapped
  obtain ⟨hl,hrest⟩ := List.mem_product.mp hdata
  obtain ⟨hr,hq⟩ := List.mem_product.mp hrest
  obtain ⟨sl,hsl⟩ := matrixEncode_sound left hl
  obtain ⟨sr,hsr⟩ := matrixEncode_sound right hr
  obtain ⟨labelFn,hlabels⟩ := functionEncode_sound (Equiv.refl (Fin n)) number label hq
  let shape : InputShape (Fin n) := fun p => match p with | .one => sl | .two => sr
  refine ⟨⟨⟨n,List.mem_range.mp hn⟩,shape,labelFn⟩,?_⟩
  change (n,matrixEncode sl,matrixEncode sr,FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ labelFn)) = _
  rw [hsl,hsr,hlabels]
  exact hcode

def outcomeEncode (outcome : LeaderHandover Q B C) : Outcome :=
  (headerEncode number outcome.1,
    FiniteFunctionCodes.encode (Equiv.refl _) outcome.2.1,
    FiniteFunctionCodes.encode (Equiv.refl _) outcome.2.2)

theorem outcomeEncode_injective : Function.Injective (outcomeEncode (B:=B) (C:=C) number) := by
  rintro ⟨h,parent,minimum⟩ ⟨h',parent',minimum'⟩ equal
  simp only [outcomeEncode,Prod.mk.injEq] at equal
  obtain ⟨hh,hparent,hminimum⟩ := equal
  obtain rfl := headerEncode_injective number hh
  apply congrArg (Sigma.mk h)
  exact Prod.ext (functionEncode_injective (Equiv.refl _) hparent)
    (functionEncode_injective (Equiv.refl _) hminimum)

theorem outcomeEncode_mem (outcome : LeaderHandover Q B C) :
    outcomeEncode number outcome ∈ rawOutcomes (B,N,C) := by
  apply List.mem_flatMap.mpr
  refine ⟨headerEncode number outcome.1,headerEncode_mem number _,?_⟩
  apply List.mem_map.mpr
  exact ⟨_,List.mem_product.mpr ⟨FiniteFunctionCodes.encode_mem _ _,FiniteFunctionCodes.encode_mem _ _⟩,rfl⟩

theorem outcomeEncode_sound (code : Outcome) (member : code ∈ rawOutcomes (B,N,C)) :
    ∃ outcome : LeaderHandover Q B C, outcomeEncode number outcome = code := by
  obtain ⟨header,hh,hm⟩ := List.mem_flatMap.mp member
  obtain ⟨source,rfl⟩ := headerEncode_sound number header hh
  have mapped : ∃ data ∈ (FiniteSearch.tables (B+1) source.1.val).product
      (FiniteSearch.tables (C+1) source.1.val), (headerEncode number source,data)=code := by
    exact List.mem_map.mp hm
  obtain ⟨⟨parents,minima⟩,hdata,hcode⟩ := mapped
  obtain ⟨hp,hmin⟩ := List.mem_product.mp hdata
  obtain ⟨parent,hparent⟩ := functionEncode_sound (Equiv.refl (Fin source.1.val)) (Equiv.refl (Fin (B+1))) parents hp
  obtain ⟨minimum,hminimum⟩ := functionEncode_sound (Equiv.refl (Fin source.1.val)) (Equiv.refl (Fin (C+1))) minima hmin
  refine ⟨⟨source,parent,minimum⟩,?_⟩
  change (headerEncode number source,FiniteFunctionCodes.encode (Equiv.refl _) parent,
    FiniteFunctionCodes.encode (Equiv.refl _) minimum) = _
  rw [show FiniteFunctionCodes.encode (Equiv.refl _) parent = parents from hparent,
    show FiniteFunctionCodes.encode (Equiv.refl _) minimum = minima from hminimum]
  exact hcode

noncomputable def outcomeNumber : LeaderHandover Q B C ≃ Fin (outcomes (B,N,C)).length :=
  (FiniteCodeNumbering.equiv (rawOutcomes (B,N,C)) (outcomeEncode number)
    (outcomeEncode_injective number) (outcomeEncode_mem number) (outcomeEncode_sound number)).trans
      (finCongr (by rw [outcomes]))

theorem outcomeNumber_val (outcome : LeaderHandover Q B C) :
    (outcomeNumber number outcome).val = outcomeName (B,N,C) (outcomeEncode number outcome) := rfl

/-- Every target slot keeps the predecessor and minimum encoded in the same
handover; entries from different outcomes cannot be mixed. -/
theorem edge_encode (outcome : LeaderHandover Q B C) (old next : HandoverCode B C) :
    edge (outcomeEncode number outcome) (old.1.val,old.2.val) (next.1.val,next.2.val) = true ↔
      HandoverEdge old outcome () next := by
  simp only [edge,decide_eq_true_eq,HasEdge,HandoverEdge]
  constructor
  · rintro ⟨i,hi,hparent,hnext⟩
    let slot : Fin outcome.1.1.val := ⟨i,hi⟩
    change (FiniteFunctionCodes.encode (Equiv.refl _) outcome.2.1).getD i 0 = old.1.val at hparent
    have parent := FiniteFunctionCodes.eval_encode (Equiv.refl _) outcome.2.1 slot
    have minimum := FiniteFunctionCodes.eval_encode (Equiv.refl _) outcome.2.2 slot
    refine ⟨slot,Fin.ext (parent.symm.trans hparent),?_⟩
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hnext)
    · exact Fin.ext ((congrArg Prod.snd hnext).trans minimum)
  · rintro ⟨i,hparent,hnext⟩
    refine ⟨i.val,i.isLt,?_,?_⟩
    · change (FiniteFunctionCodes.encode (Equiv.refl _) outcome.2.1).getD i.val 0 = old.1.val
      exact (FiniteFunctionCodes.eval_encode (Equiv.refl _) outcome.2.1 i).trans (congrArg Fin.val hparent)
    · rw [hnext]
      exact Prod.ext rfl (FiniteFunctionCodes.eval_encode (Equiv.refl _) outcome.2.2 i).symm


/-- The empty family exists even if the annotation alphabet is empty. -/
def emptyOutcome (Q : Type) (B C : Nat) : LeaderHandover Q B C :=
  ⟨⟨0,(fun _ i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩,
    (fun i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩

theorem outcomes_pos (B N C : Nat) : 0 < (outcomes (B,N,C)).length := by
  apply List.length_pos_of_mem (a:=outcomeEncode (Equiv.refl (Fin N)) (emptyOutcome (Fin N) B C))
  rw [outcomes,FiniteCodeNumbering.mem_unique]
  exact outcomeEncode_mem _ _

section Moves
attribute [local instance] Classical.propDecidable

noncomputable local instance : DecidableEq (LeaderHandover Q B C) := by
  unfold LeaderHandover SwitchInterface InputShape
  infer_instance

def procCode : Proc → Bool | .one => false | .two => true

theorem procCode_injective : Function.Injective procCode := by
  intro p q equal
  cases p <;> cases q <;> simp_all [procCode]

noncomputable def moveEncode (move : Proc × Finset (LeaderHandover Q B C)) : Move :=
  (procCode move.1,FiniteSetCodes.encode (outcomeNumber number) move.2)

theorem moveEncode_injective : Function.Injective (moveEncode (B:=B) (C:=C) number) := by
  intro left right equal
  apply Prod.ext
  · exact procCode_injective (congrArg Prod.fst equal)
  · exact FiniteSetCodes.encode_injective (outcomeNumber number) (congrArg Prod.snd equal)

theorem moveEncode_mem (move : Proc × Finset (LeaderHandover Q B C)) :
    moveEncode number move ∈ rawMoves (B,N,C) := by
  apply List.mem_product.mpr
  refine ⟨?_,FiniteSetCodes.codes_complete (outcomeNumber number) move.2⟩
  cases move.1 <;> simp [procCode]

theorem moveEncode_sound (code : Move) (member : code ∈ rawMoves (B,N,C)) :
    ∃ move : Proc × Finset (LeaderHandover Q B C), moveEncode number move = code := by
  obtain ⟨_,hm⟩ := List.mem_product.mp member
  obtain ⟨permitted,equal⟩ := FiniteSetCodes.codes_sound (outcomeNumber (B:=B) (C:=C) number) code.2 hm
  cases flag : code.1
  · refine ⟨(.one,permitted),?_⟩
    exact Prod.ext flag.symm equal
  · refine ⟨(.two,permitted),?_⟩
    exact Prod.ext flag.symm equal

noncomputable def moveNumber : (Proc × Finset (LeaderHandover Q B C)) ≃ Fin (moves (B,N,C)).length :=
  (FiniteCodeNumbering.equiv (rawMoves (B,N,C)) (moveEncode number)
    (moveEncode_injective number) (moveEncode_mem number) (moveEncode_sound number)).trans
      (finCongr (by rw [moves]))

theorem moveNumber_val (move : Proc × Finset (LeaderHandover Q B C)) :
    (moveNumber number move).val = moveName (B,N,C) (moveEncode number move) := rfl

theorem offered_encode (move : Proc × Finset (LeaderHandover Q B C)) (outcome : LeaderHandover Q B C) :
    offered (moveEncode number move) (outcomeNumber number outcome).val = true ↔ outcome ∈ move.2 := by
  change decide ((outcomeNumber number outcome).val ∈ FiniteSetCodes.encode (outcomeNumber number) move.2) = true ↔ _
  rw [decide_eq_true_eq,FiniteSetCodes.mem_encode]

end Moves

end Characterisation.EncodedLeaderAlphabet
