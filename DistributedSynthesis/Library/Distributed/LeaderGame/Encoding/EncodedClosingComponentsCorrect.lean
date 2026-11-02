/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingComponents
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReachabilityCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingBoundaryCertificates

/-! Numeric component selection agrees with the original closing-component
and complete-enumeration checks, even for arbitrary source matrices. -/
namespace Characterisation.EncodedClosingComponents
open DistributedSynthesis

variable {X : Type} {N : Nat} (number : X ≃ Fin N) (shape : InputShape X) (alive : X → Bool)

def encode : Data :=
  (N,List.ofFn (fun i => let xy := (FiniteFunctionCodes.prod number number).symm i
    (shape .one xy.1 xy.2,shape .two xy.1 xy.2)),List.ofFn (fun i => alive (number.symm i)))

theorem views_encode (x y : X) :
    views (encode number shape alive) (number x).val (number y).val = (shape .one x y,shape .two x y) := by
  have h := EncodedClosingBanks.table_eval (FiniteFunctionCodes.prod number number)
    (fun xy => (shape .one xy.1 xy.2,shape .two xy.1 xy.2)) (false,false) (x,y)
  simpa only [views,encode,FiniteFunctionCodes.prod,Equiv.trans_apply,Equiv.prodCongr_apply,
    finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using h

theorem live_encode (x : X) : live (encode number shape alive) (number x).val = alive x :=
  EncodedClosingBanks.table_eval number alive false x

theorem adjacent_encode (x y : X) :
    Adjacent (encode number shape alive) (number x).val (number y).val ↔
      (closingObservationGraph shape alive).Adj x y := by
  have ne : (number x).val ≠ (number y).val ↔ x ≠ y := by
    rw [Fin.val_injective.ne_iff,number.injective.ne_iff]
  simp only [Adjacent,live_encode,views_encode,ne,closingObservationGraph]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro (h | h | h | h)
    · exact ⟨.one,Or.inl h⟩
    · exact ⟨.two,Or.inl h⟩
    · exact ⟨.one,Or.inr h⟩
    · exact ⟨.two,Or.inr h⟩
  · rintro ⟨p,h⟩
    cases p <;> tauto

theorem mask_encode [Fintype X] [DecidableEq X] (root x : X) :
    mask (encode number shape alive) (number root).val (number x).val =
      closingComponentMask shape alive root x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [mask,Bool.and_eq_true,live_encode,closingComponentMask,Bool.and_eq_true,decide_eq_true_eq]
  apply and_congr_right
  intro _
  apply EncodedClosingReachability.reachable_correct (closingObservationGraph shape alive)
    (graphData (encode number shape alive)) number
  intro u v
  change EncodedClosingReachability.lookup
    (EncodedClosingReachability.tabulate N (fun i j => decide (Adjacent (encode number shape alive) i j)))
    (number u).val (number v).val = true ↔ _
  rw [EncodedClosingReachability.tabulate_lookup,decide_eq_true_eq,adjacent_encode]

section Enumeration
variable {S : Type} {M : Nat} (slots : S ≃ Fin M) (keep : S → X)

theorem mem_keep_encode (x : X) :
    (number x).val ∈ FiniteFunctionCodes.encode slots (number ∘ keep) ↔ ∃ s, keep s=x := by
  simp only [FiniteFunctionCodes.encode,List.mem_ofFn,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨slots.symm i,number.injective (Fin.ext hi)⟩
  · rintro ⟨s,rfl⟩
    exact ⟨slots s,by simp⟩

theorem keep_encode_injective_iff :
    (∀ i < (FiniteFunctionCodes.encode slots (number ∘ keep)).length,
      ∀ j < (FiniteFunctionCodes.encode slots (number ∘ keep)).length,
      (FiniteFunctionCodes.encode slots (number ∘ keep)).getD i 0 =
      (FiniteFunctionCodes.encode slots (number ∘ keep)).getD j 0 → i=j) ↔ Function.Injective keep := by
  constructor
  · intro checked s t same
    apply slots.injective
    apply Fin.ext
    apply checked (slots s).val (by simp [FiniteFunctionCodes.encode])
      (slots t).val (by simp [FiniteFunctionCodes.encode])
    rw [FiniteFunctionCodes.eval_encode,FiniteFunctionCodes.eval_encode]
    exact congrArg (fun x => (number x).val) same
  · intro injective i hi j hj equal
    let s := slots.symm ⟨i,by simpa only [FiniteFunctionCodes.encode,List.length_ofFn] using hi⟩
    let t := slots.symm ⟨j,by simpa only [FiniteFunctionCodes.encode,List.length_ofFn] using hj⟩
    have hs : (slots s).val = i := by simp [s]
    have ht : (slots t).val = j := by simp [t]
    have es := FiniteFunctionCodes.eval_encode slots (number ∘ keep) s
    have et := FiniteFunctionCodes.eval_encode slots (number ∘ keep) t
    rw [hs] at es
    rw [ht] at et
    have same : s=t := injective (number.injective (Fin.ext (es.symm.trans (equal.trans et))))
    exact hs.symm.trans ((congrArg (fun x => (slots x).val) same).trans ht)

theorem enumeration_encode [Fintype X] [Fintype S] [DecidableEq X] (root : X) :
    enumeration (encode number shape alive) (number root).val
      (FiniteFunctionCodes.encode slots (number ∘ keep)) = true ↔
      checkClosingEnumeration (closingComponentMask shape alive root) keep = true := by
  rw [enumeration,decide_eq_true_eq,checkClosingEnumeration,decide_eq_true_eq]
  have bounded : ∀ i ∈ FiniteFunctionCodes.encode slots (number ∘ keep), i < N :=
    ((FiniteSearch.mem_tables_iff _ _ _).mp (FiniteFunctionCodes.encode_mem slots (number ∘ keep))).2
  change (∀ i ∈ _, i < N) ∧ _ ↔ _
  rw [and_iff_right bounded,keep_encode_injective_iff]
  apply and_congr_right
  intro _
  constructor
  · intro checked x
    have hx := checked (number x).val (number x).isLt
    rwa [mask_encode,mem_keep_encode] at hx
  · intro checked i hi
    let x := number.symm ⟨i,hi⟩
    have hx : (number x).val=i := by simp [x]
    rw [← hx,mask_encode,mem_keep_encode]
    exact checked x

end Enumeration
end Characterisation.EncodedClosingComponents
