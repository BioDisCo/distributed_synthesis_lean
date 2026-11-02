/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.FiniteOrbitParity
import DistributedSynthesis.Formalizations.Lemma.LemParityTreePositionalization
import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton

/-! # Finite search for deterministic parity-tree nonemptiness

The algorithm enumerates state-based label policies and state-based branch
policies. Positionality justifies both finite searches; each pair generates
a deterministic orbit, tested by `FiniteOrbitParity.parityDecidable`.
-/

namespace DistributedSynthesis.TreeNonemptiness

variable {Q D : Type*} [Fintype Q] [Fintype D]

theorem branch_length {B : Type*} (branch : Nat → B) (n : Nat) :
    (branchNode branch n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [branchNode, ih]

/-- A finite-state path has complementary parity after a priority shift by one. -/
theorem shifted_parity_iff_not (priority : Q → Nat) (path : Nat → Q) :
    NatSeqMinEvenParity (fun n => priority (path n) + 1) ↔
      ¬ NatSeqMinEvenParity (fun n => priority (path n)) := by
  let A : DetParityAutomaton Q :=
    { State := Q, stateFinite := inferInstance, initial := path 0,
      step := fun _ q => q, priority := priority }
  have hr : ∀ n, A.run (fun n => path (n + 1)) n = path n := by
    intro n
    cases n <;> rfl
  have h := A.shiftPriority_one_accepts_iff_not_accepts (fun n => path (n + 1))
  change NatSeqMinEvenParity (fun n => (A.shiftPriority 1).priority
      ((A.shiftPriority 1).run (fun n => path (n + 1)) n)) ↔
    ¬ NatSeqMinEvenParity (fun n => A.priority (A.run (fun n => path (n + 1)) n)) at h
  simpa only [DetParityAutomaton.shiftPriority_run, hr] using h

/-- An existential parity-winning path can choose its next direction by state. -/
theorem exists_positional_path (initial : Q) (next : Q → D → Q)
    (priority : Q → Nat) (path : Nat → Q) (moves : Nat → D)
    (hinit : path 0 = initial)
    (hstep : ∀ n, path (n + 1) = next (path n) (moves n))
    (hparity : NatSeqMinEvenParity (fun n => priority (path n))) :
    ∃ policy : Q → D,
      NatSeqMinEvenParity (fun n => priority (((fun q => next q (policy q))^[n]) initial)) := by
  let step : Q → D → Unit → Q := fun q d _ => next q d
  have ha : ∃ tree, (ParityPrescription.automaton initial step priority).acceptsTree tree := by
    refine ⟨fun node => moves node.length, fun node => path node.length, ⟨?_, ?_⟩, ?_⟩
    · exact hinit
    · intro node d
      simpa [step] using hstep node.length
    · intro branch
      simpa only [branch_length] using hparity
  obtain ⟨policy, hp⟩ := ParityPrescription.exists_positional initial step priority ha
  have hr : ∀ n,
      ParityPrescription.stateAt initial step policy (branchNode (fun _ => ()) n) =
        ((fun q => next q (policy q))^[n]) initial := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [branchNode, ParityPrescription.stateAt_append, ih,
        Function.iterate_succ_apply']
  exact ⟨policy, by simpa only [hr] using hp (fun _ => ())⟩

/-- Universal parity on all paths is equivalent to its finite policy tests. -/
theorem all_paths_iff (initial : Q) (next : Q → D → Q) (priority : Q → Nat) :
    (∀ (path : Nat → Q) (moves : Nat → D), path 0 = initial →
      (∀ n, path (n + 1) = next (path n) (moves n)) →
      NatSeqMinEvenParity (fun n => priority (path n))) ↔
    ∀ policy : Q → D,
      NatSeqMinEvenParity (fun n => priority (((fun q => next q (policy q))^[n]) initial)) := by
  constructor
  · intro h policy
    exact h (fun n => ((fun q => next q (policy q))^[n]) initial)
      (fun n => policy (((fun q => next q (policy q))^[n]) initial)) rfl
      (fun n => Function.iterate_succ_apply' _ n initial)
  · intro h path moves hinit hstep
    by_contra hbad
    obtain ⟨policy, hp⟩ := exists_positional_path initial next
      (fun q => priority q + 1) path moves hinit hstep
      ((shifted_parity_iff_not priority path).mpr hbad)
    exact ((shifted_parity_iff_not priority _).mp hp) (h policy)

section Monitor

variable {Branch Label : Type*}
variable (M : DeterministicBlockMonitor Branch Label)


/-- Fixing a label policy and branch policy leaves a deterministic state orbit. -/
def policyStep (labels : M.State → Label) (directions : M.State → Branch) :
    M.State → M.State := fun q => M.step q (labels q) (directions q)

theorem nonempty_iff : (∃ tree, M.toRunAutomaton.acceptsTree tree) ↔
    ∃ labels : M.State → Label, ∀ directions : M.State → Branch,
      NatSeqMinEvenParity (fun n => M.priority ((policyStep M labels directions)^[n] M.initial)) := by
  letI := M.branchFinite
  letI := M.alphabetFinite
  constructor
  · intro h
    obtain ⟨labels, hp⟩ :=
      ParityPrescription.exists_positional M.initial M.step M.priority h
    refine ⟨labels, (all_paths_iff M.initial (fun q d => M.step q (labels q) d) M.priority).mp ?_⟩
    intro path moves hinit hstep
    have hr : ∀ n,
        ParityPrescription.stateAt M.initial M.step labels (branchNode moves n) = path n := by
      intro n
      induction n with
      | zero => exact hinit.symm
      | succ n ih =>
        rw [branchNode, ParityPrescription.stateAt_append, ih, hstep]
    simpa only [hr] using hp moves
  · rintro ⟨labels, hp⟩
    have hall := (all_paths_iff M.initial (fun q d => M.step q (labels q) d) M.priority).mpr hp
    let run := ParityPrescription.stateAt M.initial M.step labels
    refine ⟨fun node => labels (run node), run, ⟨rfl, ?_⟩, ?_⟩
    · intro node d
      exact ParityPrescription.stateAt_append M.initial M.step labels node d
    · intro branch
      exact hall (fun n => run (branchNode branch n)) branch rfl
        (fun n => ParityPrescription.stateAt_append M.initial M.step labels
          (branchNode branch n) (branch n))

/-- Exhaustive finite nonemptiness decision, including empty branch/label alphabets. -/
def nonemptyDecidable [DecidableEq M.State] :
    Decidable (∃ tree, M.toRunAutomaton.acceptsTree tree) := by
  letI := M.branchFinite
  letI := M.alphabetFinite
  letI (labels : M.State → Label) (directions : M.State → Branch) :=
    FiniteOrbitParity.parityDecidable (policyStep M labels directions) M.initial M.priority
  exact decidable_of_iff
    (∃ labels : M.State → Label, ∀ directions : M.State → Branch,
      NatSeqMinEvenParity (fun n => M.priority ((policyStep M labels directions)^[n] M.initial)))
    (nonempty_iff M).symm

def nonempty [DecidableEq M.State] : Bool :=
  @decide (∃ tree, M.toRunAutomaton.acceptsTree tree) (nonemptyDecidable M)

theorem nonempty_correct [DecidableEq M.State] :
    nonempty M = true ↔ ∃ tree, M.toRunAutomaton.acceptsTree tree := by
  unfold nonempty
  exact @decide_eq_true_iff _ (nonemptyDecidable M)

end Monitor

end DistributedSynthesis.TreeNonemptiness
