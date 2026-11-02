/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks

open DistributedSynthesis.DecisionTasks

namespace DistributedSynthesis.Tests.DecisionTasks

abbrev Inputs : Bool → Type := fun _ => Bool

def ownTask : Task Bool Inputs Inputs where
  allows x o := o = x

def ownProtocol : Protocol Bool Inputs Bool where
  init _ x := x
  trans _ st _ := st

theorem own_run (σ : ℕ → Source.Event Bool) (x : ∀ p, Inputs p) (r : ℕ) (p : Bool) :
    ownProtocol.run σ x r p = x p := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih

/-- The model permits separate local outputs; it does not impose consensus. -/
theorem own_inputs_solvable (adv : Set (ℕ → Source.Event Bool)) : ownTask.Solvable adv := by
  refine ⟨Bool, ownProtocol, fun _ st => some st, ?_⟩
  constructor
  · intro σ hσ x p
    exact ⟨0, x p, rfl⟩
  · intro σ hσ x p r r' hrr o ho
    simpa only [own_run] using ho
  · intro σ hσ x o ho
    change o = x
    funext p
    obtain ⟨r,hr⟩ := ho p
    rw [own_run] at hr
    exact (Option.some.inj hr).symm

def silentRun : ℕ → Source.Event Bool := fun _ => Source.silentEvent

/-- Off-diagonal input data cannot affect a process during permanent silence. -/
theorem private_input_silent {St : Type} (A : Protocol Bool Inputs St)
    (x y : ∀ p, Inputs p) (p : Bool) (h : x p = y p) (r : ℕ) :
    A.run silentRun x r p = A.run silentRun y r p := by
  induction r with
  | zero => simp only [Protocol.run, h]
  | succ r ih =>
    simp only [Protocol.run, silentRun, Source.silentEvent_inN, Set.image_singleton, ih]

def exchangeTask : Task Bool Inputs Inputs where
  allows x o := ∀ p, o p = x (!p)

/-- Exchange is impossible when the silent word is admissible, for arbitrary state spaces. -/
theorem exchange_impossible_silent :
    ¬ exchangeTask.Solvable ({silentRun} : Set (ℕ → Source.Event Bool)) := by
  rintro ⟨St,A,out,h⟩
  have value : ∀ (x : ∀ p, Inputs p) p r b,
      out p (A.run silentRun x r p) = some b → b = x (!p) := by
    intro x p r b hb
    choose rs os hos using h.term silentRun (Set.mem_singleton _) x
    have legal := h.allows silentRun (Set.mem_singleton _) x os (fun q => ⟨rs q, hos q⟩)
    have h1 := h.irrev silentRun (Set.mem_singleton _) x p r (max r (rs p))
      (le_max_left _ _) b hb
    have h2 := h.irrev silentRun (Set.mem_singleton _) x p (rs p) (max r (rs p))
      (le_max_right _ _) (os p) (hos p)
    exact (Option.some.inj (h1.symm.trans h2)).trans (legal p)
  let x : ∀ p, Inputs p := fun _ => false
  let y : ∀ p, Inputs p := fun p => p
  obtain ⟨r,b,hb⟩ := h.term silentRun (Set.mem_singleton _) x false
  have hx : b = false := value x false r b hb
  have hr := private_input_silent A x y false rfl r
  have hy : b = true := value y false r b (hr ▸ hb)
  exact Bool.false_ne_true (hx.symm.trans hy)

/-- Full histories encode precisely all information available to arbitrary-state algorithms. -/
theorem equal_hist_equal_state {V St : Type} (A : Source.Algorithm Bool V St)
    (σ τ : ℕ → Source.Event Bool) (I J : Bool → V) (r : ℕ) (p : Bool)
    (h : Source.hist σ I r p = Source.hist τ J r p) :
    A.run σ I r p = A.run τ J r p := by
  have hf := Source.fullEq_of_hist_eq h
  exact Source.run_eq_of_viewEq A hf.view hf.own hf.2.2


end DistributedSynthesis.Tests.DecisionTasks

namespace DistributedSynthesis.Tests.DecisionTasks

open DistributedSynthesis.DecisionTasks.TwoProcess

def tableTask (table : (Proc → Bool) → (Proc → Bool) → Bool) :
    Task Proc (fun _ => Bool) (fun _ => Bool) where
  allows x o := table x o = true

instance (table : (Proc → Bool) → (Proc → Bool) → Bool) (x o : Proc → Bool) :
    Decidable ((tableTask table).allows x o) :=
  inferInstanceAs (Decidable (table x o = true))

/-- Compiler acceptance checks that the actual finite-data frontend is executable.
The potentially very large task search is not evaluated by this regression. -/
def finiteInputSolver (table : (Proc → Bool) → (Proc → Bool) → Bool)
    (formula : LTL Proc) : Bool :=
  solveGraphTask edgeInterp edgeDecidable formula (tableTask table)

def finiteParitySolver (table : (Proc → Bool) → (Proc → Bool) → Bool)
    (A : DetParityAutomaton (Option Graph)) [DecidableEq A.State] : Bool :=
  solveGraphParityTask A (tableTask table)

abbrev differentInputs : Proc → Type
  | .one => Bool
  | .two => Fin 3

abbrev differentOutputs : Proc → Type
  | .one => Fin 3
  | .two => Bool

instance (p : Proc) : Fintype (differentInputs p) := by cases p <;> exact inferInstance
instance (p : Proc) : DecidableEq (differentInputs p) := by cases p <;> exact inferInstance
instance (p : Proc) : Nonempty (differentInputs p) := by cases p <;> exact inferInstance
instance (p : Proc) : Fintype (differentOutputs p) := by cases p <;> exact inferInstance
instance (p : Proc) : DecidableEq (differentOutputs p) := by cases p <;> exact inferInstance
instance (p : Proc) : Nonempty (differentOutputs p) := by cases p <;> exact inferInstance

def differentExchange : Task Proc differentInputs differentOutputs where
  allows x o := o .one = x .two ∧ o .two = x .one

instance (x : ∀ p, differentInputs p) (o : ∀ p, differentOutputs p) :
    Decidable (differentExchange.allows x o) :=
  inferInstanceAs (Decidable (o .one = x .two ∧ o .two = x .one))

/-- Concrete different per-process alphabets, through both public frontends. -/
def differentInputSolver (formula : LTL Proc) : Bool :=
  solveGraphTask edgeInterp edgeDecidable formula differentExchange

def differentParitySolver (A : DetParityAutomaton (Option Graph))
    [DecidableEq A.State] : Bool := solveGraphParityTask A differentExchange

example : graphLetter none = (false, false) := rfl
example : graphLetter (some .right) = (false, true) := rfl
example : graphLetter (some .left) = (true, false) := rfl
example : graphLetter (some .both) = (true, true) := rfl
example : processEquiv .one = false := rfl
example : processEquiv .two = true := rfl

end DistributedSynthesis.Tests.DecisionTasks

namespace DistributedSynthesis.Tests.DecisionTasks

open Source

/-- Initial output evaluation can be suppressed without changing solvability. -/
theorem suppress_initial_output {V O : Type} [Nonempty O]
    {adv : Set (ℕ → Source.Event Bool)} {T : Source.Task Bool V O}
    (h : ∃ (St : Type) (A : Algorithm Bool V St) (out : Bool → St → Option O),
      A.SolvesTask out T adv) :
    ∃ out : Bool → Hist V → Option O,
      (histAlg V).SolvesTask out T adv ∧ (∀ p x, out p (.init p x) = none) := by
  obtain ⟨S⟩ := solvesTask_iff_outputScheme.mp h
  have hS := solvesTask_of_outputScheme S
  let delayed : Bool → Hist V → Option O :=
    fun p st => if st.depth = 0 then none else outMap adv S.out p st
  have delayed_run (σ : ℕ → Source.Event Bool) (x : Bool → V) (r : ℕ) (p : Bool) :
      delayed p (Protocol.run (histAlg V) σ x r p) =
        if r = 0 then none else outMap adv S.out p (Protocol.run (histAlg V) σ x r p) := by
    have hrun : Protocol.run (histAlg V) σ x r p = hist σ x r p := histAlg_run σ x r p
    rw [hrun]
    simp only [delayed, hist_depth]
  refine ⟨delayed, ?_, fun _ _ => rfl⟩
  constructor
  · intro σ hσ x p
    obtain ⟨r,o,ho⟩ := hS.term σ hσ x p
    refine ⟨r+1,o,?_⟩
    rw [delayed_run, if_neg (Nat.succ_ne_zero r)]
    exact hS.irrev σ hσ x p r (r+1) (Nat.le_succ r) o ho
  · intro σ hσ x p r r' hrr o ho
    rw [delayed_run] at ho ⊢
    by_cases hr : r = 0
    · simp [hr] at ho
    rw [if_neg hr] at ho
    have hr' : r' ≠ 0 := by omega
    rw [if_neg hr']
    exact hS.irrev σ hσ x p r r' hrr o ho
  · intro σ hσ x o ho
    apply hS.allows σ hσ x o
    intro p
    obtain ⟨r,hr⟩ := ho p
    rw [delayed_run] at hr
    by_cases hz : r = 0
    · simp [hz] at hr
    rw [if_neg hz] at hr
    exact ⟨r,hr⟩


end DistributedSynthesis.Tests.DecisionTasks
