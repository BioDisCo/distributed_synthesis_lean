/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingScanTables
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphRules
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingGraphCoupling

/-! Exact generation and checking of the old graph scans. The numeric
checker compares the original initial states and every original graph-root
step. Live and boundary flags are read from the same scan. -/
namespace Characterisation.EncodedClosingScans
open DistributedSynthesis

variable {H I₁ I₂ GQ : Type} {R E S d K D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype GQ] [DecidableEq GQ]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (states : GraphRootState GQ d K ≃ Fin S) (initial : H → GraphRootState GQ d K)

def dataEncode (D : Nat) : Data :=
  ((R,E,D),rulesEncode recognizer states,List.ofFn (fun i => (graphCode (env.symm i).2.2).val),
    FiniteFunctionCodes.encode root (states ∘ initial))

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem lastGraph_encode (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)) :
    lastGraph (dataEncode root env recognizer states initial D)
      (scenarioEncode (D:=D) root env ⟨⟨n.val+1,by omega⟩,s⟩) = (graphCode s.2.2.2).val := by
  unfold lastGraph
  simp only [scenarioEncode,EncodedClosingLayers.encode,List.length_ofFn,Nat.add_sub_cancel]
  have last : (List.ofFn (fun i => (env (closingLayerWord (n.val+1) s i)).val)).getD n.val 0 =
      (env s.2).val := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    rw [List.getElem_ofFn]
    change (env (Fin.lastCases s.2 (closingLayerWord n.val s.1) (Fin.last n.val))).val = _
    rw [Fin.lastCases_last]
  rw [last]
  exact EncodedClosingBanks.table_eval env (fun r => (graphCode r.2.2).val) 0 s.2

omit [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype GQ] [DecidableEq GQ] in
theorem entry_zero (table : ClosingGraphTable H I₁ I₂ GQ d K D) (h : H) :
    entry (R,E,D) (tableEncode root env states table) ((root h).val,[]) =
      (states (table ⟨0,by omega⟩ h)).val :=
  entry_encode root env states table ⟨0,by omega⟩ h

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem step_encode (table : ClosingGraphTable H I₁ I₂ GQ d K D)
    (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)) :
    StepChecked (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      (scenarioEncode (D:=D) root env ⟨⟨n.val+1,by omega⟩,s⟩) ↔
      checkGraphRootStep recognizer (table ⟨n.val,by omega⟩ s.1) s.2.2.2
        (table ⟨n.val+1,by omega⟩ s) = true := by
  unfold StepChecked
  have length : (scenarioEncode (D:=D) root env ⟨⟨n.val+1,by omega⟩,s⟩).2.length = n.val+1 :=
    List.length_ofFn
  rw [length]
  simp only [Nat.zero_lt_succ,true_implies]
  rw [scenarioEncode_parent root env (show n.val+1 ≤ D by omega) s]
  change allowed (rulesEncode recognizer states)
    (entry (R,E,D) _ _) (lastGraph (dataEncode root env recognizer states initial D) _) (entry (R,E,D) _ _) = true ↔ _
  rw [entry_encode,entry_encode,lastGraph_encode,allowed_encode]

/-- The entire generated scan checker equals the original finite checker. -/
theorem check_encode (table : ClosingGraphTable H I₁ I₂ GQ d K D) :
    check (dataEncode root env recognizer states initial D) (tableEncode root env states table) = true ↔
      checkClosingGraphTable recognizer initial table = true := by
  rw [check,decide_eq_true_eq,checkClosingGraphTable,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨sourceChecked,stepsChecked⟩
    constructor
    · intro h
      apply states.injective
      apply Fin.ext
      have checked := sourceChecked (root h).val (root h).isLt
      change entry (R,E,D) (tableEncode root env states table) ((root h).val,[]) =
        (FiniteFunctionCodes.encode root (states ∘ initial)).getD (root h).val 0 at checked
      rwa [entry_zero,FiniteFunctionCodes.eval_encode] at checked
    · intro n s
      apply (step_encode root env recognizer states initial table n s).mp
      apply stepsChecked
      rw [domain,FiniteCodeNumbering.mem_unique]
      exact scenarioEncode_mem root env ⟨⟨n.val+1,by omega⟩,s⟩
  · rintro ⟨sourceChecked,stepsChecked⟩
    constructor
    · intro i hi
      let h := root.symm ⟨i,hi⟩
      have hr : (root h).val=i := by simp [h]
      have value := entry_zero root env states table h
      rw [sourceChecked,hr] at value
      have initialCode := FiniteFunctionCodes.eval_encode root (states ∘ initial) h
      rw [hr] at initialCode
      exact value.trans initialCode.symm
    · intro code member
      rw [domain,FiniteCodeNumbering.mem_unique] at member
      obtain ⟨⟨⟨n,hn⟩,s⟩,rfl⟩ := scenarioEncode_sound (D:=D) root env code member
      cases n with
      | zero =>
        intro positive
        simp only [scenarioEncode,EncodedClosingLayers.encode,List.length_ofFn] at positive
        omega
      | succ n => exact (step_encode root env recognizer states initial table ⟨n,by omega⟩ s).mpr (stepsChecked ⟨n,by omega⟩ s)

theorem scans_encode (table : ClosingGraphTable H I₁ I₂ GQ d K D) :
    tableEncode root env states table ∈ scans (dataEncode root env recognizer states initial D) ↔
      checkClosingGraphTable recognizer initial table = true := by
  rw [scans,List.mem_filter]
  have member : tableEncode root env states table ∈ candidates (dataEncode root env recognizer states initial D) :=
    tableEncode_mem root env states table
  rw [and_iff_right member,check_encode]

/-- Every generated scan is an original checked scan, and every original
checked scan occurs. No finite graph-state choices are omitted. -/
theorem scans_sound (code : List Nat) (member : code ∈ scans (dataEncode root env recognizer states initial D)) :
    ∃ table : ClosingGraphTable H I₁ I₂ GQ d K D,
      tableEncode root env states table = code ∧ checkClosingGraphTable recognizer initial table = true := by
  obtain ⟨table,equal⟩ := tableEncode_sound root env states code (List.mem_filter.mp member).1
  refine ⟨table,equal,?_⟩
  exact (scans_encode root env recognizer states initial table).mp (equal ▸ member)

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem live_encode (table : ClosingGraphTable H I₁ I₂ GQ d K D)
    (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val) :
    live (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      (scenarioEncode root env ⟨n,s⟩) = closingGraphLiveTable table n s := by
  change liveRule (rulesEncode recognizer states) (entry (R,E,D) _ _) = _
  rw [entry_encode,liveRule_encode]
  rfl

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem boundary_encode (table : ClosingGraphTable H I₁ I₂ GQ d K D)
    (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)) :
    boundary (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      (scenarioEncode (D:=D) root env ⟨⟨n.val+1,by omega⟩,s⟩) =
      closingGraphBoundary recognizer table (n.val+1) s := by
  rw [boundary]
  have nonempty : (scenarioEncode (D:=D) root env ⟨⟨n.val+1,by omega⟩,s⟩).2 ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [scenarioEncode,EncodedClosingLayers.encode,List.length_ofFn,List.length_nil] at length
    omega
  rw [if_neg nonempty,scenarioEncode_parent root env (show n.val+1 ≤ D by omega) s]
  change boundaryRule (rulesEncode recognizer states) (entry (R,E,D) _ _)
    (lastGraph (dataEncode root env recognizer states initial D) _) = _
  rw [entry_encode,lastGraph_encode,boundaryRule_encode]
  simp only [closingGraphBoundary,closingGraphAt,dif_pos (show n.val < D+1 by omega)]

end Characterisation.EncodedClosingScans
