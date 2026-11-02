/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAnnotations
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedAlphabetCompatibility
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphRules

/-! Exact correspondence with the numbered game's existing annotation
update and reset. The graph transition table depends only on the fixed
adversary; the objective table and finite alphabets may vary by instance. -/
namespace Characterisation.EncodedLeaderAnnotations
open DistributedSynthesis

variable {GQ I₁ I₂ O₁ O₂ : Type} {d K C S N E V : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (M : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (graphNumber : GraphRootState GQ d K ≃ Fin S) (objectiveNumber : M.State ≃ Fin N)
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (output : (O₁ × O₂) ≃ Fin V)
variable (objectiveData : EncodedParityTables.Data)

noncomputable def chosenGraphSteps : List Nat :=
  FiniteFunctionCodes.encode (FiniteFunctionCodes.prod graphNumber EncodedClosingScans.graphNumber)
    (fun p => graphNumber (chooseGraphRootNext recognizer p.1 p.2))

noncomputable def dataEncode : Data :=
  (S,N,C,chosenGraphSteps recognizer graphNumber,
    List.ofFn (fun i => (graphCode (env.symm i).2.2).val),V,objectiveData)

local notation "input" => dataEncode (C:=C) (V:=V) recognizer graphNumber env objectiveData (N:=N)
local notation "number" => leaderAnnotationNumber (C:=C) M graphNumber objectiveNumber

omit [Fintype GQ] [DecidableEq GQ] in
theorem number_val (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M) :
    (number q).val = (q.2 ()).val + (C+1)*((objectiveNumber q.1.2).val+N*(graphNumber q.1.1).val) := rfl

include objectiveNumber in
theorem objectiveCount_pos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (objectiveNumber M.initial).isLt

theorem graphState_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M) :
    graphState input (number q).val = (graphNumber q.1.1).val := by
  rw [graphState,number_val]
  change (_+(C+1)*_)/(C+1)/N = _
  rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _),Nat.div_eq_of_lt (q.2 ()).isLt,Nat.zero_add,
    Nat.add_mul_div_left _ _ (objectiveCount_pos M objectiveNumber),Nat.div_eq_of_lt (objectiveNumber q.1.2).isLt,Nat.zero_add]

theorem objectiveState_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M) :
    objectiveState input (number q).val = (objectiveNumber q.1.2).val := by
  rw [objectiveState,number_val]
  change (_+(C+1)*_)/(C+1)%N = _
  rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _),Nat.div_eq_of_lt (q.2 ()).isLt,Nat.zero_add,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (objectiveNumber q.1.2).isLt]

theorem minimum_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M) :
    minimum input (number q).val = (q.2 ()).val := by
  rw [minimum,number_val]
  exact (Nat.add_mul_mod_self_left ..).trans (Nat.mod_eq_of_lt (q.2 ()).isLt)

theorem reset_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M) :
    reset input (number q).val = (number (resetLeaderMinimum M q)).val := by
  rw [reset,number_val,number_val]
  change C+(C+1)*((_+(C+1)*_)/(C+1)) = C+(C+1)*_
  rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _),Nat.div_eq_of_lt (q.2 ()).isLt,Nat.zero_add]
  rfl

theorem minima_encode : minima input = FiniteFunctionCodes.encode number (fun q => q.2 ()) := by
  unfold minima
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  have h := minimum_encode (V:=V) recognizer M graphNumber objectiveNumber env objectiveData ((number).symm i)
  simpa only [Equiv.apply_symm_apply] using h

theorem graphNext_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M)
    (r : I₁ × I₂ × Graph) (o : O₁ × O₂) :
    graphNext input (number q).val ((env r).val*V+(output o).val) =
      (graphNumber (chooseGraphRootNext recognizer q.1.1 r.2.2)).val := by
  rw [graphNext,graphState_encode]
  have positive : 0 < V := lt_of_le_of_lt (Nat.zero_le _) (output o).isLt
  have split : ((env r).val*V+(output o).val)/V = (env r).val := by
    rw [Nat.add_comm,Nat.mul_comm,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt (output o).isLt,Nat.zero_add]
  change (chosenGraphSteps recognizer graphNumber).getD
    ((graphNumber q.1.1).val*3+(List.ofFn (fun i => (graphCode (env.symm i).2.2).val)).getD
      (((env r).val*V+(output o).val)/V) 0) 0 = _
  rw [split,EncodedClosingBanks.table_eval env (fun r => (graphCode r.2.2).val) 0 r]
  have h := FiniteFunctionCodes.eval_encode
    (FiniteFunctionCodes.prod graphNumber EncodedClosingScans.graphNumber)
    (fun p => graphNumber (chooseGraphRootNext recognizer p.1 p.2)) (q.1.1,r.2.2)
  have index : (FiniteFunctionCodes.prod graphNumber EncodedClosingScans.graphNumber (q.1.1,r.2.2)).val =
      (graphNumber q.1.1).val*3+(graphCode r.2.2).val := by
    change (graphCode r.2.2).val+3*(graphNumber q.1.1).val = _
    ring
  rw [index] at h
  exact h

variable (rank : M.State → Fin (C+1))
variable (transition : ∀ q r o, EncodedParityTables.next objectiveData (objectiveNumber q).val
  ((env r).val*V+(output o).val) = (objectiveNumber (M.step q (r,o))).val)
variable (priority : ∀ q, EncodedParityTables.priority objectiveData (objectiveNumber q).val = (rank q).val)

include transition priority in
theorem step_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M)
    (r : I₁ × I₂ × Graph) (o : O₁ × O₂) :
    step input (number q).val ((env r).val*V+(output o).val) =
      (number (leaderAnnotationStep recognizer M rank q r o)).val := by
  rw [step,minimum_encode,graphNext_encode]
  have next : objectiveNext input (number q).val ((env r).val*V+(output o).val) =
      (objectiveNumber (M.step q.1.2 (r,o))).val := by
    rw [objectiveNext,objectiveState_encode]
    exact transition _ _ _
  rw [next,number_val]
  change min _ (EncodedParityTables.priority objectiveData (objectiveNumber (M.step q.1.2 (r,o))).val) + _ = _
  rw [priority]
  rfl

theorem compile_next (data : Data) (alphabet q a : Nat) (stateBound : q < count data) (letterBound : a < alphabet) :
    EncodedParityTables.next (compile data alphabet) q a = step data q a % (count data-1+1) := by
  have row : ((List.range alphabet).map (fun a => (List.range (count data)).map (fun q => step data q a))).getD a [] =
      (List.range (count data)).map (fun q => step data q a) := by
    rw [List.getD_eq_getElem _ _ (by simpa using letterBound)]
    simp only [List.getElem_map,List.getElem_range]
  unfold EncodedParityTables.next compile EncodedParityTables.rows
  rw [row,List.getD_eq_getElem _ _ (by simpa using stateBound)]
  simp only [List.getElem_map,List.getElem_range,EncodedParityTables.size]

include transition priority in
/-- The generated numeric transition table implements the actual numbered
annotation update used by the graph collector. -/
theorem compile_encode (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) M)
    (r : I₁ × I₂ × Graph) (o : O₁ × O₂) :
    EncodedParityTables.next (compile input (E*V)) (number q).val ((env r).val*V+(output o).val) =
      (number (leaderAnnotationStep recognizer M rank q r o)).val := by
  have positive : 0 < count input := lt_of_le_of_lt (Nat.zero_le _) (number q).isLt
  have letterBound : (env r).val*V+(output o).val < E*V := by
    have h := (FiniteFunctionCodes.prod env output (r,o)).isLt
    change (output o).val+V*(env r).val < E*V at h
    simpa only [Nat.add_comm,Nat.mul_comm] using h
  rw [compile_next _ _ _ _ (number q).isLt letterBound,step_encode recognizer M graphNumber objectiveNumber env output objectiveData rank transition priority]
  have size : count input-1+1 = count input := by omega
  rw [size]
  exact Nat.mod_eq_of_lt (number (leaderAnnotationStep recognizer M rank q r o)).isLt

end Characterisation.EncodedLeaderAnnotations
