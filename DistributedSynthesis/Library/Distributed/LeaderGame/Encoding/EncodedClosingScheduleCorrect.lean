/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingSchedule
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingScansCorrect
import DistributedSynthesis.Library.Distributed.LeaderPhases.CanonicalClosingSchedule

/-! Numeric stopping flags agree with the original first-boundary convention
at every physical depth, including the initial and empty windows. -/
namespace Characterisation.EncodedClosingScans
open DistributedSynthesis

variable {H I₁ I₂ GQ : Type} {R E S d K D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype GQ] [DecidableEq GQ]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (states : GraphRootState GQ d K ≃ Fin S) (initial : H → GraphRootState GQ d K)
variable (table : ClosingGraphTable H I₁ I₂ GQ d K D)

section
omit [Fintype H] [Fintype I₁] [Fintype I₂]

theorem boundaryFlag_encode (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val) :
    boundary (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      (scenarioEncode root env ⟨n,s⟩) =
      closingFlagAt (closingGraphBoundaryTable recognizer table) n.val s := by
  rw [closingFlagAt,dif_pos n.isLt]
  rcases n with ⟨n,hn⟩
  cases n with
  | zero => simp [boundary,scenarioEncode,EncodedClosingLayers.encode,closingGraphBoundaryTable,closingGraphBoundary]
  | succ n => exact boundary_encode root env recognizer states initial table ⟨n,by omega⟩ s

theorem active_encode (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    active (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      (scenarioEncode (D:=D) root env ⟨⟨n,by omega⟩,s⟩) =
      closingActive (closingFlagAt (closingGraphBoundaryTable recognizer table)) n s := by
  induction n using Nat.twoStepInduction with
  | zero => exact active_short _ _ _ (by simp [scenarioEncode,EncodedClosingLayers.encode])
  | one => exact active_short _ _ _ (by simp [scenarioEncode,EncodedClosingLayers.encode])
  | more n _ ih =>
    rw [active_parent _ _ _ (by simp [scenarioEncode,EncodedClosingLayers.encode]),
      scenarioEncode_parent root env (show n+1+1 ≤ D by omega) s,ih (by omega),boundaryFlag_encode]
    rfl

theorem firstExit_encode (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val) :
    firstExit (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      (scenarioEncode root env ⟨n,s⟩) =
      closingFirstExit (closingFlagAt (closingGraphBoundaryTable recognizer table)) n.val s := by
  rw [firstExit,active_encode root env recognizer states initial table n.val (by omega),boundaryFlag_encode]
  rcases n with ⟨n,hn⟩
  cases n with
  | zero => simp [closingFirstExit,closingFlagAt,closingGraphBoundaryTable,closingGraphBoundary]
  | succ n => rfl

theorem eligible_encode (firstWindow : Bool) (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val) :
    eligible (dataEncode root env recognizer states initial D) (tableEncode root env states table)
      firstWindow (scenarioEncode root env ⟨n,s⟩) =
      (closingWindowScheduled firstWindow D n.val &&
        closingFlagAt (closingGraphLiveTable table) n.val s &&
        closingFirstExit (closingFlagAt (closingGraphBoundaryTable recognizer table)) n.val s) := by
  rw [eligible,live_encode,firstExit_encode]
  simp only [scheduled,dataEncode,scenarioEncode,EncodedClosingLayers.encode,List.length_ofFn,
    closingWindowScheduled,closingFlagAt,dif_pos n.isLt]

end

end Characterisation.EncodedClosingScans
