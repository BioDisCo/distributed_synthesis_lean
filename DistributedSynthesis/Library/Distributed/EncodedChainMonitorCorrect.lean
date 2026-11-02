/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainMonitor
import DistributedSynthesis.Library.Distributed.EncodedChainThreadsCorrect
import DistributedSynthesis.Formalizations.Theorem.ThmGlobalChainChecker
import DistributedSynthesis.Library.Automata.EncodedParityOperations

/-! # Set-started chain monitor correspondence -/
namespace DistributedSynthesis.EncodedChainMonitor
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount d)))
local instance : Inhabited (Fin (inputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (inputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩

def decodedSet (T : List Nat) : Finset (ChainThread A) :=
  Finset.univ.filter (fun th => chainIndex d th ∈ T)
theorem mem_decodedSet (T : List Nat) (th : ChainThread A) :
    th ∈ decodedSet d T ↔ chainIndex d th ∈ T := by simp only [decodedSet,Finset.mem_filter,Finset.mem_univ,true_and]

def stateCode : Option (Option (ChainThread A)) → Nat
  | none => 0
  | some none => 1
  | some (some th) => chainIndex d th+2
def monitorEquiv : Option (Option (ChainThread A)) ≃ Fin (stateCount d) :=
  (((chainEquiv d).optionCongr.trans (finSuccEquiv (chainCount d)).symm).optionCongr).trans
    (finSuccEquiv (chainCount d+1)).symm
theorem monitorEquiv_val (q : Option (Option (ChainThread A))) : (monitorEquiv d q).val = stateCode d q := by
  cases q with
  | none => rfl
  | some q => cases q with
    | none => rfl
    | some th =>
      simp only [monitorEquiv,Equiv.trans_apply,Equiv.optionCongr_apply,Option.map_some,
        finSuccEquiv_symm_some,Fin.val_succ,chainEquiv_val,stateCode,Nat.add_assoc]
      exact (congrArg Fin.val (finSuccEquiv_symm_some ((chainEquiv d th).succ))).trans (by rfl)
theorem monitorCard : Fintype.card (Option (Option (ChainThread A))) = stateCount d := by
  simpa using Fintype.card_congr (monitorEquiv d)
def monitorNumber : Option (Option (ChainThread A)) ≃ Fin (Fintype.card (Option (Option (ChainThread A)))) :=
  (monitorEquiv d).trans (finCongr (monitorCard d).symm)
theorem monitorNumber_val (q : Option (Option (ChainThread A))) :
    (monitorNumber d q).val = stateCode d q := monitorEquiv_val d q
theorem stateCode_lt (q : Option (Option (ChainThread A))) : stateCode d q < stateCount d := by
  rw [← monitorEquiv_val]
  exact (monitorEquiv d q).isLt

def side : Fin (inputTwo d) ⊕ Fin (inputOne d) → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true
def sender : Fin (inputTwo d) ⊕ Fin (inputOne d) → Nat
  | Sum.inl j => j.val
  | Sum.inr i => i.val
def context (T : List Nat) (mode : Bool) (c : EncodedJournalLabels.Code)
    (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) : Context := ((d,T),(mode,side d b,c,sender d b))

theorem step_correct (T : List Nat) (mode : Bool) (c : EncodedJournalLabels.Code)
    (b : Fin (inputTwo d) ⊕ Fin (inputOne d)) (q : Option (Option (ChainThread A)))
    (i : Fin (inputOne d)) (j : Fin (inputTwo d)) (guess : ChainThread A) :
    next (context d T mode c b,stateCode d q,(i.val,j.val,chainIndex d guess)) =
      stateCode d ((chainSetMonitor A (decodedSet d T)).step q
        (narrowedRecord (chainSetMonitor A (decodedSet d T))
          (packChainSetLabel (semanticLabel d c mode)) q (((i,j),guess),b))) := by
  cases q with
  | none =>
    by_cases hg : chainIndex d guess ∈ T
    · rw [chainSetMonitor_step_start_mem _ _ _ ((mem_decodedSet d T guess).mpr hg)]
      cases b with
      | inl s =>
        have h := EncodedChainThreads.next_correct d c mode false guess i s
        simpa only [next,context,side,sender,stateCode,chainMove,chosen,Bool.cond_false,hg,
          not_true_eq_false,and_false,or_false,if_false,if_true,Nat.zero_ne_one,
          semanticBranch] using congrArg (·+2) h
      | inr s =>
        have h := EncodedChainThreads.next_correct d c mode true guess s j
        simpa only [next,context,side,sender,stateCode,chainMove,chosen,Bool.cond_true,hg,
          not_true_eq_false,and_false,or_false,if_false,if_true,Nat.zero_ne_one,
          semanticBranch] using congrArg (·+2) h
    · rw [chainSetMonitor_step_start_notMem _ _ _ (fun h => hg ((mem_decodedSet d T guess).mp h))]
      simp only [next,context,stateCode,hg,not_false_eq_true,and_self,or_true,if_true]
  | some q =>
    cases q with
    | none => rw [chainSetMonitor_step_dead]; rfl
    | some th =>
      rw [chainSetMonitor_step_active]
      have h0 : chainIndex d th+2 ≠ 0 := by omega
      have h1 : chainIndex d th+2 ≠ 1 := by omega
      cases b with
      | inl s =>
        have h := EncodedChainThreads.next_correct d c mode false th i s
        simpa only [next,context,side,sender,stateCode,chainMove,chosen,Bool.cond_false,h0,h1,
          false_and,false_or,if_false,Nat.add_sub_cancel,semanticBranch] using congrArg (·+2) h
      | inr s =>
        have h := EncodedChainThreads.next_correct d c mode true th s j
        simpa only [next,context,side,sender,stateCode,chainMove,chosen,Bool.cond_true,h0,h1,
          false_and,false_or,if_false,Nat.add_sub_cancel,semanticBranch] using congrArg (·+2) h

theorem priority_correct (T : List Nat) (q : Option (Option (ChainThread A))) :
    priority d (stateCode d q) = (chainSetMonitor A (decodedSet d T)).priority q := by
  cases q with
  | none => rfl
  | some q => cases q with
    | none => rfl
    | some th =>
      have h : ¬ chainIndex d th+2 < 2 := by omega
      simp only [priority,stateCode,h,if_false,Nat.add_sub_cancel,current_index,pairedIndex_div]
      rfl

theorem priorities_correct (T : List Nat) (q : Option (Option (ChainThread A))) :
    (priorities d).getD (stateCode d q) 0 = (chainSetMonitor A (decodedSet d T)).priority q := by
  unfold priorities
  rw [EncodedParityOperations.lookup_range (priority d) ⟨stateCode d q,stateCode_lt d q⟩]
  exact priority_correct d T q
theorem mem_receivers (r : Receiver) : r ∈ receivers d ↔
    r.1 < inputOne d ∧ r.2.1 < inputTwo d ∧ r.2.2 < chainCount d := by
  rcases r with ⟨i,j,g⟩
  exact List.mem_product.trans (and_congr List.mem_range
    (List.mem_product.trans (and_congr List.mem_range List.mem_range)))

theorem mem_edges (c : Context) (q t : Nat) : (q,t) ∈ edges c ↔
    q < stateCount c.1.1 ∧ ∃ r ∈ receivers c.1.1, next (c,q,r) = t := by
  simp only [edges,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨q,hq,r,hr,rfl,he⟩; exact ⟨hq,r,hr,he⟩
  · rintro ⟨hq,r,hr,he⟩; exact ⟨q,hq,r,hr,rfl,he⟩

theorem stateCode_injective : Function.Injective (stateCode d) := by
  intro q r h
  apply (monitorEquiv d).injective
  apply Fin.ext
  simpa only [monitorEquiv_val] using h

theorem edges_correct (T : List Nat) (mode : Bool) (c : EncodedJournalLabels.Code)
    (b : Fin (inputTwo d) ⊕ Fin (inputOne d))
    (q t : Option (Option (ChainThread A))) :
    (stateCode d q,stateCode d t) ∈ edges (context d T mode c b) ↔
      ∃ r : (Fin (inputOne d) × Fin (inputTwo d)) × ChainThread A,
        t = (chainSetMonitor A (decodedSet d T)).step q
          (narrowedRecord (chainSetMonitor A (decodedSet d T))
            (packChainSetLabel (semanticLabel d c mode)) q (r,b)) := by
  rw [mem_edges]
  change (stateCode d q < stateCount d ∧ ∃ r ∈ receivers d,
    next (context d T mode c b,stateCode d q,r) = stateCode d t) ↔ _
  rw [and_iff_right (stateCode_lt d q)]
  constructor
  · rintro ⟨⟨i,j,g⟩,hr,he⟩
    obtain ⟨hi,hj,hg⟩ := (mem_receivers d _).mp hr
    let guess := (chainEquiv d).symm ⟨g,hg⟩
    have hguess : chainIndex d guess = g := by
      rw [← chainEquiv_val]
      exact congrArg Fin.val ((chainEquiv d).apply_symm_apply ⟨g,hg⟩)
    have hstep := step_correct d T mode c b q ⟨i,hi⟩ ⟨j,hj⟩ guess
    rw [hguess] at hstep
    exact ⟨((⟨i,hi⟩,⟨j,hj⟩),guess),stateCode_injective d (he.symm.trans hstep)⟩
  · rintro ⟨⟨⟨i,j⟩,guess⟩,rfl⟩
    exact ⟨(i.val,j.val,chainIndex d guess),(mem_receivers d _).mpr
      ⟨i.isLt,j.isLt,chainIndex_lt d guess⟩,step_correct d T mode c b q i j guess⟩

theorem priorities_range (T : List Nat) (p : Nat) :
    p ∈ priorities d ↔ p ∈ ThreadComputable.priorityRange (chainSetMonitor A (decodedSet d T)) := by
  simp only [priorities,List.mem_map,List.mem_range,ThreadComputable.priorityRange,
    Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨n,hn,hp⟩
    let q := (monitorEquiv d).symm ⟨n,hn⟩
    have hq : stateCode d q = n := by
      rw [← monitorEquiv_val]
      exact congrArg Fin.val ((monitorEquiv d).apply_symm_apply ⟨n,hn⟩)
    refine ⟨q,?_⟩
    rw [← priority_correct d T q,hq]
    exact hp
  · rintro ⟨q,rfl⟩
    exact ⟨stateCode d q,stateCode_lt d q,priority_correct d T q⟩
end DistributedSynthesis.EncodedChainMonitor
