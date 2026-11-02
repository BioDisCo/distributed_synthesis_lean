/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CoupledRootMemory

/-! Bounded closing scans carry one checked graph state at each private-input
scenario. Their live and boundary flags are computed from these states. -/
namespace Characterisation
open DistributedSynthesis

abbrev ClosingGraphTable (H I₁ I₂ Q : Type) (d K D : Nat) :=
  (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → GraphRootState Q d K

instance closingGraphTable_fintype {H I₁ I₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype Q]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] (d K D : Nat) :
    Fintype (ClosingGraphTable H I₁ I₂ Q d K D) := by
  unfold ClosingGraphTable
  infer_instance

def closingGraphAt {H I₁ I₂ Q : Type} {d K D : Nat}
    (table : ClosingGraphTable H I₁ I₂ Q d K D) (n : Nat) (s : ClosingLayer H I₁ I₂ n) : GraphRootState Q d K :=
  if within : n < D+1 then table ⟨n,within⟩ s else none

def checkClosingGraphTable {H I₁ I₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype Q] [DecidableEq Q] {d K D : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (source : H → GraphRootState Q d K) (table : ClosingGraphTable H I₁ I₂ Q d K D) : Bool :=
  decide (∀ h, table ⟨0,by omega⟩ h = source h) &&
  decide (∀ (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)),
    checkGraphRootStep M (table ⟨n.val,by omega⟩ s.1) s.2.2.2 (table ⟨n.val+1,by omega⟩ s) = true)

theorem closingGraphAt_rep {H I₁ I₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype Q] [DecidableEq Q] {d K D : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (past : H → EnvHistory I₁ I₂) (source : H → GraphRootState Q d K)
    (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (source h))
    (table : ClosingGraphTable H I₁ I₂ Q d K D) (checked : checkClosingGraphTable M source table = true)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    GraphRootRep P M (History.graphSequence (closingLayerHistory past n s)) (closingGraphAt table n s) := by
  have checks : (∀ h, table ⟨0,by omega⟩ h = source h) ∧
      ∀ (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)),
        checkGraphRootStep M (table ⟨n.val,by omega⟩ s.1) s.2.2.2 (table ⟨n.val+1,by omega⟩ s) = true := by
    simpa only [checkClosingGraphTable,Bool.and_eq_true,decide_eq_true_eq] using checked
  induction n with
  | zero =>
    simp only [closingGraphAt,dif_pos (show 0 < D+1 by omega),checks.1,closingLayerHistory]
    exact sourceExact s
  | succ n ih =>
    have stepCheck : checkGraphRootStep M (closingGraphAt table n s.1) s.2.2.2
        (closingGraphAt table (n+1) s) = true := by
      simpa only [closingGraphAt,dif_pos (show n < D+1 by omega),dif_pos (show n+1 < D+1 by omega)] using
        checks.2 ⟨n,by omega⟩ s
    have result := graphRootStep_correct M P closed recognizes _ (closingGraphAt table n s.1)
      (ih (by omega) s.1 checks) s.2.2.2 (closingGraphAt table (n+1) s) stepCheck
    simpa only [closingLayerHistory,scenarioHistory,History.graphSequence,List.map_append,List.map_cons,List.map_nil] using result

def closingGraphBoundary {H I₁ I₂ Q : Type} {d K D : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (table : ClosingGraphTable H I₁ I₂ Q d K D) : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool
  | 0, _ => false
  | n+1, s => graphRootBoundary M (closingGraphAt table n s.1) s.2.2.2

def closingGraphBoundaryTable {H I₁ I₂ Q : Type} {d K D : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (table : ClosingGraphTable H I₁ I₂ Q d K D) : ClosingFlagTable H I₁ I₂ D :=
  fun n s => closingGraphBoundary M table n.val s

def closingGraphLiveTable {H I₁ I₂ Q : Type} {d K D : Nat}
    (table : ClosingGraphTable H I₁ I₂ Q d K D) : ClosingFlagTable H I₁ I₂ D :=
  fun n s => (table n s).isSome

theorem graphRootRep_live_iff {Q : Type} {d K : Nat}
    (M : Recognizer Graph Q) (P : List Graph → Prop) (g : List Graph)
    (state : GraphRootState Q d K) (rep : GraphRootRep P M g state) : state.isSome = true ↔ P g := by
  cases state with
  | none => exact ⟨Bool.noConfusion,fun live => False.elim (rep live)⟩
  | some st => exact ⟨fun _ => rep.1,fun _ => rfl⟩

section Exact
variable {H I₁ I₂ Q : Type} [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype Q] [DecidableEq Q] {d K D : Nat}
variable (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (past : H → EnvHistory I₁ I₂) (source : H → GraphRootState Q d K)
variable (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (source h))
variable (table : ClosingGraphTable H I₁ I₂ Q d K D) (checked : checkClosingGraphTable M source table = true)

include closed recognizes sourceExact checked in
theorem closingGraphLiveTable_exact (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val) :
    closingGraphLiveTable table n s = true ↔ P (History.graphSequence (closingLayerHistory past n.val s)) := by
  have rep := closingGraphAt_rep M P closed recognizes past source sourceExact table checked n.val (by omega) s
  have live := graphRootRep_live_iff M P _ _ rep
  simpa only [closingGraphAt,dif_pos n.isLt,closingGraphLiveTable] using live

include closed recognizes sourceExact checked in
/-- Positive-depth flags agree with actual boundaries on every live closing
scenario. The zero-depth marker is ignored by the first-exit convention. -/
theorem closingGraphBoundary_exact_on_live (n : Nat) (bound : n+1 ≤ D)
    (s : ClosingLayer H I₁ I₂ (n+1)) (live : P (History.graphSequence (closingLayerHistory past (n+1) s))) :
    closingGraphBoundary M table (n+1) s = leaderBoundary P d (closingLayerHistory past (n+1) s) := by
  have rep := closingGraphAt_rep M P closed recognizes past source sourceExact table checked n (by omega) s.1
  exact graphRootBoundary_exact M P closed recognizes (closingLayerHistory past n s.1) (closingGraphAt table n s.1) rep
    ⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩ live

end Exact
end Characterisation
