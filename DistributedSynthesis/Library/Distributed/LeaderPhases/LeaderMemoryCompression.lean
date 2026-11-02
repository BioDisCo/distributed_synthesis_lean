/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingClosingPlans

/-! Preserve finite rolling commitments while narrowing an unbounded leader
phase. Memory checks are coupled to the physical parity monitor before the
existing universal-thread table construction is applied. This does not yet
choose the global game or its next-boundary obligations. -/
namespace Characterisation
open DistributedSynthesis

def phaseMemoryRun {Letter Memory : Type} (initial : Memory)
    (next : Memory → Letter → Memory) (play : Nat → Letter) : Nat → Memory
  | 0 => initial
  | n+1 => next (phaseMemoryRun initial next play n) (play n)

section Guard
variable {RIn SIn ROut Extra SOut Memory : Type} [Fintype Memory]
variable (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
variable (project : Extra → ROut) (initial : Memory)
variable (next : Memory → RealizedBlockRound RIn SIn Extra SOut → Memory)
variable (valid : Memory → RealizedBlockRound RIn SIn Extra SOut → Bool)

def phasePhysicalPlay (play : Nat → RealizedBlockRound RIn SIn Extra SOut) :
    Nat → RealizedBlockRound RIn SIn ROut SOut :=
  fun t => ((play t).1,project (play t).2.1,(play t).2.2)

def leaderMemoryMonitor : BlockRecordMonitor.{0,0,0,0,0} RIn SIn Extra SOut where
  State := M.State × Memory × Bool
  stateFinite := inferInstance
  initial := (M.initial,initial,true)
  step := fun q r => (M.step q.1 (r.1,project r.2.1,r.2.2),next q.2.1 r,q.2.2 && valid q.2.1 r)
  priority := fun q => if q.2.2 then M.priority q.1 + 2 else 1

theorem leaderMemoryMonitor_run (play : Nat → RealizedBlockRound RIn SIn Extra SOut) (n : Nat) :
    ((leaderMemoryMonitor M project initial next valid).run play n).1 =
      M.run (phasePhysicalPlay project play) n ∧
    ((leaderMemoryMonitor M project initial next valid).run play n).2.1 =
      phaseMemoryRun initial next play n := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    constructor
    · exact congrArg (fun q => M.step q ((play n).1,project (play n).2.1,(play n).2.2)) ih.1
    · exact congrArg (fun q => next q (play n)) ih.2

theorem leaderMemoryMonitor_false_persists
    (play : Nat → RealizedBlockRound RIn SIn Extra SOut) (n : Nat)
    (failed : ((leaderMemoryMonitor M project initial next valid).run play n).2.2 = false) :
    ∀ k, ((leaderMemoryMonitor M project initial next valid).run play (n+k)).2.2 = false := by
  intro k
  induction k with
  | zero => simpa using failed
  | succ k ih =>
    rw [Nat.add_succ,BlockRecordMonitor.run]
    change (((leaderMemoryMonitor M project initial next valid).run play (n+k)).2.2 && _) = false
    rw [ih]
    rfl

theorem leaderMemoryMonitor_safe_of_wins
    (play : Nat → RealizedBlockRound RIn SIn Extra SOut)
    (wins : (leaderMemoryMonitor M project initial next valid).WinsPlay play) (n : Nat) :
    ((leaderMemoryMonitor M project initial next valid).run play n).2.2 = true := by
  by_contra bad
  have failed := Bool.eq_false_of_not_eq_true bad
  have persist := leaderMemoryMonitor_false_persists M project initial next valid play n failed
  apply not_natSeqMinEvenParity_of_eventually_one _ n ?_ wins
  intro k lower
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lower
  change (if _ then _ else 1) = 1
  rw [persist j]
  rfl

/-- No promise can be dropped even once. A failed finite memory check is
permanently rejecting; otherwise the physical parity condition is unchanged. -/
theorem leaderMemoryMonitor_wins_iff
    (play : Nat → RealizedBlockRound RIn SIn Extra SOut) :
    (leaderMemoryMonitor M project initial next valid).WinsPlay play ↔
      M.WinsPlay (phasePhysicalPlay project play) ∧
      ∀ n, valid (phaseMemoryRun initial next play n) (play n) = true := by
  have parity : (∀ n, ((leaderMemoryMonitor M project initial next valid).run play n).2.2 = true) →
      ((leaderMemoryMonitor M project initial next valid).WinsPlay play ↔
        M.WinsPlay (phasePhysicalPlay project play)) := by
    intro safe
    unfold BlockRecordMonitor.WinsPlay
    have priorities :
        (fun n => (leaderMemoryMonitor M project initial next valid).priority
          ((leaderMemoryMonitor M project initial next valid).run play n)) =
        fun n => M.priority (M.run (phasePhysicalPlay project play) n) + 2 := by
      funext n
      change (if _ then _ else _) = _
      rw [safe n,if_pos rfl,(leaderMemoryMonitor_run M project initial next valid play n).1]
    rw [priorities]
    exact natSeqMinEvenParity_add_const (d:=2) ⟨1,rfl⟩
  constructor
  · intro wins
    have safe := leaderMemoryMonitor_safe_of_wins M project initial next valid play wins
    refine ⟨(parity safe).mp wins,?_⟩
    intro n
    have checks := safe (n+1)
    change (_ && valid _ (play n)) = true at checks
    simp only [Bool.and_eq_true] at checks
    have current := checks.2
    rwa [(leaderMemoryMonitor_run M project initial next valid play n).2] at current
  · rintro ⟨physical,checks⟩
    have safe : ∀ n, ((leaderMemoryMonitor M project initial next valid).run play n).2.2 = true := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change (_ && valid _ (play n)) = true
        rw [ih,(leaderMemoryMonitor_run M project initial next valid play n).2,checks n]
        rfl
    exact (parity safe).mpr physical

variable [Fintype RIn] [Fintype SIn] [Fintype Extra] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited RIn] [Inhabited SIn] [Inhabited Extra]

/-- One fixed finite table type suffices for an arbitrarily long one-way
phase, preserving both all-thread parity and every finite memory check.
The singleton family reuses the existing simultaneous table construction;
it gives no hidden index to the leader. -/
theorem leaderMemory_finite_table
    (receiver : ReceiverBlockStrategy RIn SIn Extra)
    (sender : SenderBlockStrategy SIn SOut)
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay project (pairPlay receiver sender env)))
    (checks : ∀ env n, valid (phaseMemoryRun initial next (pairPlay receiver sender env) n)
      (pairPlay receiver sender env n) = true) :
    ∃ table : FiniteRootFamilyTable (fun _ : Unit => leaderMemoryMonitor M project initial next valid),
      NarrowedAllThreadsWin (leaderMemoryMonitor M project initial next valid)
        (finiteRootMemberController (fun _ : Unit => leaderMemoryMonitor M project initial next valid)
          table.toTransitionRationalTree ()).labeledTree := by
  let family := fun _ : Unit => leaderMemoryMonitor M project initial next valid
  have wins : ∀ (_ : Unit) env, (family ()).WinsPlay (pairPlay receiver sender env) := by
    intro _ env
    exact (leaderMemoryMonitor_wins_iff M project initial next valid _).mpr ⟨physical env,checks env⟩
  let table := finiteRootFamilyTable family (fun _ => receiver) sender wins
  exact ⟨table,finiteRootMemberController_allThreadsWin family _
    (finiteRootFamilyTable_wins family (fun _ => receiver) sender wins) ()⟩

end Guard

end Characterisation
