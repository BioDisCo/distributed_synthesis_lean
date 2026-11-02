/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphClosingOffers
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphCollector
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingRestrictionCorrect

/-! Exactness of the full generated graph collector, including active-root
restriction and both directions of graph-scan enumeration. -/
namespace Characterisation.EncodedGraphCollector
open DistributedSynthesis

section ActiveRoots
variable {H : Type} {R : Nat} [Fintype H]
variable (root : H ≃ Fin R) (active : H → Bool) (template : EncodedScheduledCollector.Data)
variable (rootCount : EncodedClosingBanks.roots (EncodedScheduledCollector.bankData template.1) = R)

def encodeActivity : Data := (template,List.ofFn (fun i => active (root.symm i)))
def rootCode (h : ActiveClosingRoots active) := (root h.val).val

omit [Fintype H] in
theorem rootCode_injective : Function.Injective (rootCode root active) := by
  intro h k same
  exact Subtype.ext (root.injective (Fin.ext same))

include rootCount in
omit [Fintype H] in
theorem rootCode_mem (h : ActiveClosingRoots active) :
    rootCode root active h ∈ raw (encodeActivity root active template) := by
  rw [raw,List.mem_filter]
  refine ⟨List.mem_range.mpr ?_,?_⟩
  · change (root h.val).val < EncodedClosingBanks.roots (EncodedScheduledCollector.bankData template.1)
    rw [rootCount]
    exact (root h.val).isLt
  · exact (EncodedClosingBanks.table_eval root active false h.val).trans h.property

include rootCount in
omit [Fintype H] in
theorem rootCode_sound (code : Nat) (member : code ∈ raw (encodeActivity root active template)) :
    ∃ h : ActiveClosingRoots active, rootCode root active h = code := by
  obtain ⟨bounded,alive⟩ := List.mem_filter.mp member
  have lt : code < R := by
    have h := List.mem_range.mp bounded
    change code < EncodedClosingBanks.roots (EncodedScheduledCollector.bankData template.1) at h
    rwa [rootCount] at h
  let h := root.symm ⟨code,lt⟩
  have number : (root h).val = code := by simp [h]
  refine ⟨⟨h,?_⟩,number⟩
  have correct := EncodedClosingBanks.table_eval root active false h
  rw [number] at correct
  exact correct.symm.trans alive

noncomputable def activeNumber : ActiveClosingRoots active ≃ Fin (keep (encodeActivity root active template)).length :=
  (FiniteCodeNumbering.equiv (raw (encodeActivity root active template)) (rootCode root active)
    (rootCode_injective root active) (rootCode_mem root active template rootCount)
    (rootCode_sound root active template rootCount)).trans (finCongr (by rw [keep]))

omit [Fintype H] in
theorem keep_encode : keep (encodeActivity root active template) =
    FiniteFunctionCodes.encode (activeNumber root active template rootCount) (root ∘ Subtype.val) := by
  apply List.ext_getElem
  · simp only [FiniteFunctionCodes.encode,List.length_ofFn]
  · intro i hi hj
    let index : Fin (keep (encodeActivity root active template)).length := ⟨i,hi⟩
    let selected := activeNumber root active template rootCount
    have h := FiniteCodeNumbering.get_name (raw (encodeActivity root active template)) (rootCode root active)
      (rootCode_mem root active template rootCount) (selected.symm index)
    have index_eq : FiniteCodeNumbering.name (raw (encodeActivity root active template))
        (rootCode root active (selected.symm index)) = i := by
      change (selected (selected.symm index)).val = i
      rw [Equiv.apply_symm_apply]
    rw [← keep,index_eq,List.getElem?_eq_getElem hi] at h
    simpa only [FiniteFunctionCodes.encode,List.getElem_ofFn] using Option.some.inj h

end ActiveRoots

section Collector
variable {H I₁ I₂ O₁ O₂ Q GQ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q] [Fintype GQ]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [DecidableEq GQ]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) (start : H → Q) (transitions : EncodedParityTables.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (states : GraphRootState GQ d K ≃ Fin S) (source : H → GraphRootState GQ d K)
variable (firstWindow : Bool) (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1)) (active : H → Bool)

/-- The outer collector fills the graph scan itself; its unused template
scan is the empty numeric list. -/
noncomputable def dataEncode : Data :=
  ((EncodedScheduledCollector.replayDataEncode root env one two output outOne outTwo number shape bank start transitions,
    FiniteFunctionCodes.encode root slot,FiniteFunctionCodes.encode number minimum,
    EncodedClosingScans.dataEncode root env recognizer states source (D+1),[],firstWindow,B),
    List.ofFn (fun i => active (root.symm i)))

local notation "input" => dataEncode root env one two output outOne outTwo number shape bank start transitions
  recognizer states source firstWindow slot minimum active

omit [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
    [DecidableEq Q] in
theorem withScan_encode (table : ClosingGraphTable H I₁ I₂ GQ d K (D+1)) :
    withScan input.1 (EncodedClosingScans.tableEncode root env states table) =
      EncodedScheduledCollector.dataEncode root env one two output outOne outTwo number shape bank start transitions
        recognizer states source table firstWindow slot minimum := rfl

variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(output o).val) = (number (step q r o)).val)

include transition in
/-- The generated collector is exactly the original graph-coupled collector.
No precomputed component, stopping flag, or closing-outcome table is an
input to the numeric algorithm. -/
theorem collect_encode (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode number outcome ∈ collect input ↔
      outcome ∈ graphClosingOffers recognizer source active shape firstWindow step start
        (closingPolicyOfBank bank) slot minimum := by
  let selected := activeNumber root active input.1 (by rfl)
  have roots : keep input = FiniteFunctionCodes.encode selected (root ∘ Subtype.val) :=
    keep_encode root active input.1 (by rfl)
  have perScan (table : ClosingGraphTable H I₁ I₂ GQ d K (D+1)) :
      EncodedLeaderAlphabet.outcomeEncode number outcome ∈
        EncodedScheduledCollector.collect
          (EncodedClosingRestriction.apply (withScan input.1 (EncodedClosingScans.tableEncode root env states table)) (keep input)) ↔
      outcome ∈ scheduledClosingOffers (restrictInputShape shape (Subtype.val : ActiveClosingRoots active → H)) firstWindow
        (restrictClosingFlags Subtype.val (closingGraphBoundaryTable recognizer table))
        (restrictClosingFlags Subtype.val (closingGraphLiveTable table)) step (start ∘ Subtype.val)
        (restrictClosingPolicy Subtype.val (closingPolicyOfBank bank)) (slot ∘ Subtype.val) minimum := by
    rw [withScan_encode,roots]
    exact EncodedClosingRestriction.collect_encode root selected Subtype.val env one two output outOne outTwo number
      shape bank start transitions recognizer states source table firstWindow slot minimum step transition outcome
  rw [collect,List.mem_flatMap,mem_graphClosingOffers_iff]
  constructor
  · rintro ⟨code,member,offered⟩
    obtain ⟨table,equal,checked⟩ := EncodedClosingScans.scans_sound root env recognizer states source code member
    rw [← equal] at offered
    exact ⟨table,checked,(perScan table).mp offered⟩
  · rintro ⟨table,checked,offered⟩
    exact ⟨EncodedClosingScans.tableEncode root env states table,
      (EncodedClosingScans.scans_encode root env recognizer states source table).mpr checked,
      (perScan table).mpr offered⟩

end Collector
end Characterisation.EncodedGraphCollector
