/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Decide2
import DistributedSynthesis.Library.Distributed.DecisionTasks.TypedTasks
import DistributedSynthesis.Library.Distributed.DecisionTasks.TwoProcessModel
import DistributedSynthesis.Library.Automata.LTLComputable

/-!
# Deciding finite two-process tasks under LTL graph assumptions

The task backend uses initial inputs, four communication graphs, and irrevocable
decisions. The compiler is the existing local LTL-to-parity compiler. The bridge
below proves that the two libraries use the same runs and minimum-even parity
semantics; the final decision procedure has no compiler-correctness hypothesis.
-/

namespace DistributedSynthesis.DecisionTasks.TwoProcess

open Source

/-- Present a local deterministic parity automaton to the task backend. -/
def taskMonitor (A : DetParityAutomaton Letter) : ColAut.Adv A.State where
  step := A.step
  init := A.initial
  prio := A.priority

theorem monitor_run (A : DetParityAutomaton Letter) (w : OmegaWord Letter) (n : ℕ) :
    ColAut.advRun (taskMonitor A) w n = A.run w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A.step (ColAut.advRun (taskMonitor A) w n) (w n) =
        A.step (A.run w n) (w n)
      rw [ih]

theorem monitor_accepts (A : DetParityAutomaton Letter) (σ : ℕ → Event Bool) :
    σ ∈ ColAut.advOf (taskMonitor A) ↔ A.Accepts (letter σ) := by
  change Source.FiniteParity.ColourWins
    (fun n => A.priority (ColAut.advRun (taskMonitor A) (letter σ) n)) false ↔ _
  simp_rw [monitor_run]
  rw [Source.FiniteParity.colourWins_false_iff]
  rfl

variable {AP : Type} [DecidableEq AP]

/-- LTL graph language. The first reception bit says `false` hears `true`;
the second says `true` hears `false`. Neither bit observes outgoing delivery. -/
def adversary (interp : AP → Letter → Prop) (φ : DistributedSynthesis.LTL AP) :
    Set (ℕ → Event Bool) :=
  {σ | DistributedSynthesis.LTL.Satisfies interp (letter σ) φ}

theorem compiled_adversary (interp : AP → Letter → Prop)
    (dec : ∀ ap g, Decidable (interp ap g)) (φ : DistributedSynthesis.LTL AP) :
    ColAut.advOf (taskMonitor (LTLComputable.compile interp dec φ)) =
      adversary interp φ := by
  ext σ
  exact (monitor_accepts _ σ).trans (LTLComputable.correct interp dec φ (letter σ))

/-- Existence of an arbitrary-state distributed algorithm satisfying the task. -/
def Solvable {V O : Type} (interp : AP → Letter → Prop)
    (φ : DistributedSynthesis.LTL AP) (T : Source.Task Bool V O) : Prop :=
  ∃ (St : Type) (A : Algorithm Bool V St) (out : Bool → St → Option O),
    A.SolvesTask out T (adversary interp φ)

/-- An executable decision procedure, including the verified local LTL compiler.
The input/output alphabets and the task table are finite data; state spaces of
candidate distributed algorithms are unrestricted. -/
def decidableSolvable {V O : Type}
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (interp : AP → Letter → Prop) (dec : ∀ ap g, Decidable (interp ap g))
    (φ : DistributedSynthesis.LTL AP) (T : Source.Task Bool V O)
    [∀ I o, Decidable (T.allows I o)] : Decidable (Solvable interp φ T) := by
  let A := LTLComputable.compile interp dec φ
  letI : DecidableEq A.State := LTLComputable.stateDecidableEq interp dec φ
  have h := Source.decidableSolvesTaskAdv (taskMonitor A) T
  rw [compiled_adversary interp dec φ] at h
  exact h

/-- Boolean interface to the decision procedure. -/
def solve {V O : Type}
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (interp : AP → Letter → Prop) (dec : ∀ ap g, Decidable (interp ap g))
    (φ : DistributedSynthesis.LTL AP) (T : Source.Task Bool V O)
    [∀ I o, Decidable (T.allows I o)] : Bool :=
  @decide (Solvable interp φ T) (decidableSolvable interp dec φ T)

theorem solve_correct {V O : Type}
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (interp : AP → Letter → Prop) (dec : ∀ ap g, Decidable (interp ap g))
    (φ : DistributedSynthesis.LTL AP) (T : Source.Task Bool V O)
    [∀ I o, Decidable (T.allows I o)] :
    solve interp dec φ T = true ↔ Solvable interp φ T := by
  exact iff_of_eq (@decide_eq_true_eq _ (decidableSolvable interp dec φ T))

section SeparateAlphabets

variable {I O : Bool → Type}
variable [∀ p, Fintype (I p)] [∀ p, DecidableEq (I p)] [∀ p, Nonempty (I p)]
variable [∀ p, Fintype (O p)] [∀ p, DecidableEq (O p)] [∀ p, Nonempty (O p)]

/-- Separate-alphabet tasks with a deterministic parity automaton as input. -/
def decidableParityTask (A : DetParityAutomaton Letter) [DecidableEq A.State]
    (T : DecisionTasks.Task Bool I O) [∀ x o, Decidable (T.allows x o)] :
    Decidable (T.Solvable (ColAut.advOf (taskMonitor A))) := by
  letI (x : Bool → ∀ p, I p) (o : Bool → ∀ p, O p) : Decidable (T.packed.allows x o) :=
    inferInstanceAs (Decidable (T.allows (fun p => x p p) (fun p => o p p)))
  letI := Source.decidableSolvesTaskAdv (taskMonitor A) T.packed
  exact decidable_of_iff _ (T.packed_solvable_iff _)

def solveParityTask (A : DetParityAutomaton Letter) [DecidableEq A.State]
    (T : DecisionTasks.Task Bool I O) [∀ x o, Decidable (T.allows x o)] : Bool :=
  @decide _ (decidableParityTask A T)

theorem solveParityTask_correct (A : DetParityAutomaton Letter) [DecidableEq A.State]
    (T : DecisionTasks.Task Bool I O) [∀ x o, Decidable (T.allows x o)] :
    solveParityTask A T = true ↔ T.Solvable (ColAut.advOf (taskMonitor A)) :=
  @decide_eq_true_iff _ (decidableParityTask A T)

/-- The paper's decision problem, with distinct alphabets at the two processes. -/
def decidableTask (interp : AP → Letter → Prop) (dec : ∀ ap g, Decidable (interp ap g))
    (φ : DistributedSynthesis.LTL AP) (T : DecisionTasks.Task Bool I O)
    [∀ x o, Decidable (T.allows x o)] : Decidable (T.Solvable (adversary interp φ)) := by
  let A := LTLComputable.compile interp dec φ
  letI : DecidableEq A.State := LTLComputable.stateDecidableEq interp dec φ
  have h := decidableParityTask A T
  rw [compiled_adversary interp dec φ] at h
  exact h

def solveTask (interp : AP → Letter → Prop) (dec : ∀ ap g, Decidable (interp ap g))
    (φ : DistributedSynthesis.LTL AP) (T : DecisionTasks.Task Bool I O)
    [∀ x o, Decidable (T.allows x o)] : Bool :=
  @decide (T.Solvable (adversary interp φ)) (decidableTask interp dec φ T)

theorem solveTask_correct (interp : AP → Letter → Prop)
    (dec : ∀ ap g, Decidable (interp ap g)) (φ : DistributedSynthesis.LTL AP)
    (T : DecisionTasks.Task Bool I O) [∀ x o, Decidable (T.allows x o)] :
    solveTask interp dec φ T = true ↔ T.Solvable (adversary interp φ) :=
  @decide_eq_true_iff _ (decidableTask interp dec φ T)

end SeparateAlphabets

section SharedGraphs

variable {I O : Proc → Type}
variable [∀ p, Fintype (I p)] [∀ p, DecidableEq (I p)] [∀ p, Nonempty (I p)]
variable [∀ p, Fintype (O p)] [∀ p, DecidableEq (O p)] [∀ p, Nonempty (O p)]

/-- The graph-word language of a parity automaton, using the shared processes. -/
def graphParityAdversary (A : DetParityAutomaton (Option Graph)) :
    Set (ℕ → DecisionTasks.Event Proc) := {σ | A.Accepts (graphWord σ)}

/-- The paper's LTL graph adversary, over the shared graph alphabet with silence. -/
def graphAdversary (interp : AP → Option Graph → Prop) (φ : LTL AP) :
    Set (ℕ → DecisionTasks.Event Proc) := {σ | LTL.Satisfies interp (graphWord σ) φ}

/-- The public graph-language interface of the existing verified compiler. -/
theorem compiled_graph_adversary (interp : AP → Option Graph → Prop)
    (dec : ∀ ap g, Decidable (interp ap g)) (φ : LTL AP) :
    graphParityAdversary (LTLComputable.compile interp dec φ) = graphAdversary interp φ := by
  ext σ
  exact LTLComputable.correct interp dec φ (graphWord σ)

omit [DecidableEq AP] in
theorem graphAdversary_iff (interp : AP → Option Graph → Prop) (φ : LTL AP)
    (σ : ℕ → DecisionTasks.Event Proc) :
    σ ∈ graphAdversary interp φ ↔
      ∃ w : ℕ → Option Graph, LTL.Satisfies interp w φ ∧ graphEvent ∘ w = σ := by
  constructor
  · intro h
    exact ⟨graphWord σ, h, graphEvent_graphWord σ⟩
  · rintro ⟨w, h, rfl⟩
    simpa only [graphAdversary, Set.mem_setOf_eq, graphWord_graphEvent] using h

theorem graphParityAdversary_transport (A : DetParityAutomaton (Option Graph)) :
    ProcessTransport.adversary processEquiv (graphParityAdversary A) =
      ColAut.advOf (taskMonitor (A.comap graphLetter.symm)) := by
  ext σ
  rw [monitor_accepts, DetParityAutomaton.comap_accepts_iff]
  change A.Accepts (graphWord (ProcessTransport.event processEquiv.symm ∘ σ)) ↔ _
  have hw : graphWord (ProcessTransport.event processEquiv.symm ∘ σ) =
      OmegaWord.map graphLetter.symm (letter σ) := by
    unfold graphWord
    congr 2
    funext n
    exact ProcessTransport.event_inverse processEquiv.symm (σ n)
  rw [hw]

/-- An executable decider on the project's `Proc` and `Graph` types.
The two processes may have different finite nonempty input and output alphabets. -/
def decidableGraphParityTask (A : DetParityAutomaton (Option Graph)) [DecidableEq A.State]
    (T : DecisionTasks.Task Proc I O) [∀ x o, Decidable (T.allows x o)] :
    Decidable (T.Solvable (graphParityAdversary A)) := by
  letI : DecidableEq (A.comap graphLetter.symm).State := inferInstanceAs (DecidableEq A.State)
  letI (x : Bool → ∀ p, I p) (o : Bool → ∀ p, O p) :
      Decidable ((ProcessTransport.task processEquiv T.packed).allows x o) :=
    inferInstanceAs (Decidable (T.allows (fun p => x (processEquiv p) p)
      (fun p => o (processEquiv p) p)))
  letI := Source.decidableSolvesTaskAdv (taskMonitor (A.comap graphLetter.symm))
    (ProcessTransport.task processEquiv T.packed)
  have h := (ProcessTransport.solvable_iff processEquiv T.packed
    (graphParityAdversary A)).trans (T.packed_solvable_iff _)
  rw [graphParityAdversary_transport] at h
  exact decidable_of_iff _ h

def solveGraphParityTask (A : DetParityAutomaton (Option Graph)) [DecidableEq A.State]
    (T : DecisionTasks.Task Proc I O) [∀ x o, Decidable (T.allows x o)] : Bool :=
  @decide _ (decidableGraphParityTask A T)

theorem solveGraphParityTask_correct (A : DetParityAutomaton (Option Graph))
    [DecidableEq A.State] (T : DecisionTasks.Task Proc I O)
    [∀ x o, Decidable (T.allows x o)] :
    solveGraphParityTask A T = true ↔ T.Solvable (graphParityAdversary A) :=
  @decide_eq_true_iff _ (decidableGraphParityTask A T)

/-- The public LTL endpoint uses the existing verified compiler on `Option Graph`. -/
def decidableGraphTask (interp : AP → Option Graph → Prop)
    (dec : ∀ ap g, Decidable (interp ap g)) (φ : LTL AP)
    (T : DecisionTasks.Task Proc I O) [∀ x o, Decidable (T.allows x o)] :
    Decidable (T.Solvable (graphAdversary interp φ)) := by
  let A := LTLComputable.compile interp dec φ
  letI : DecidableEq A.State := LTLComputable.stateDecidableEq interp dec φ
  have h := decidableGraphParityTask A T
  rw [compiled_graph_adversary interp dec φ] at h
  exact h

def solveGraphTask (interp : AP → Option Graph → Prop)
    (dec : ∀ ap g, Decidable (interp ap g)) (φ : LTL AP)
    (T : DecisionTasks.Task Proc I O) [∀ x o, Decidable (T.allows x o)] : Bool :=
  @decide _ (decidableGraphTask interp dec φ T)

theorem solveGraphTask_correct (interp : AP → Option Graph → Prop)
    (dec : ∀ ap g, Decidable (interp ap g)) (φ : LTL AP)
    (T : DecisionTasks.Task Proc I O) [∀ x o, Decidable (T.allows x o)] :
    solveGraphTask interp dec φ T = true ↔ T.Solvable (graphAdversary interp φ) :=
  @decide_eq_true_iff _ (decidableGraphTask interp dec φ T)

end SharedGraphs

end DistributedSynthesis.DecisionTasks.TwoProcess
