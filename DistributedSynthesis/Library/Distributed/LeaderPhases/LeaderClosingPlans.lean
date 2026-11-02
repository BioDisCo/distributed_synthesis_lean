/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderStrategyTree

/-! Finite contingent plans for a bounded closing stretch. A semantic plan
records responses for every future input/graph prefix. It does not assume
that the leader knows which hidden past history occurred. -/
namespace Characterisation
open DistributedSynthesis

abbrev ClosingScenario (I₁ I₂ : Type*) (D : Nat) := WindowScenario Unit I₁ I₂ D
abbrev LeaderClosingPlan (I₁ I₂ O₁ O₂ : Type*) (D : Nat) :=
  ClosingScenario I₁ I₂ D → O₁ × O₂

instance leaderClosingPlan_finite {I₁ I₂ O₁ O₂ : Type*}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂] (D : Nat) :
    Finite (LeaderClosingPlan I₁ I₂ O₁ O₂ D) := by
  unfold LeaderClosingPlan ClosingScenario WindowScenario
  infer_instance

def closingPlanOfStrategy {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂) (D : Nat) :
    LeaderClosingPlan I₁ I₂ O₁ O₂ D := fun s =>
  (σ.one (currentView .one (windowHistory (fun _ : Unit => h) D s)),
    σ.two (currentView .two (windowHistory (fun _ : Unit => h) D s)))

/-- Every actual strategy supplies a finite plan, with responses at every
intermediate output position. This is semantic extraction, not a selection
rule available to a leader who does not know h. -/
theorem closingPlanOfStrategy_coherent {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂) (D : Nat) :
    WindowCoherent (fun _ : Unit => h) D (closingPlanOfStrategy σ h D) := by
  constructor
  · intro s t eq
    exact congrArg σ.one eq
  · intro s t eq
    exact congrArg σ.two eq

/-- Restrict a prospective word to the prefix needed for the current output.
Only inputs and graphs already seen in that prefix index the entry. -/
def closingPrefix {I₁ I₂ : Type*} {D n : Nat} (bound : n ≤ D)
    (future : Fin n → I₁ × I₂ × Graph) (i : Fin n) : ClosingScenario I₁ I₂ D :=
  ((),⟨⟨i.val,by omega⟩,fun j => future ⟨j.val,by
    have hi := i.isLt
    have hj : j.val < i.val + 1 := j.isLt
    omega⟩⟩)

def closingOutputs {I₁ I₂ O₁ O₂ : Type*} {D n : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (future : Fin n → I₁ × I₂ × Graph) : Fin n → O₁ × O₂ :=
  fun i => plan (closingPrefix bound future i)

/-- Equal finite plans preserve the whole bounded output word, not just
its final value. -/
theorem closingOutputs_equal {I₁ I₂ O₁ O₂ : Type*} {D n : Nat}
    (first second : LeaderClosingPlan I₁ I₂ O₁ O₂ D) (same : first = second)
    (bound : n ≤ D) (future : Fin n → I₁ × I₂ × Graph) :
    closingOutputs first bound future = closingOutputs second bound future := by
  rw [same]

/-- Monitor evaluation includes the input pair, graph and both outputs in
each letter. It can represent an objective automaton together with a running
minimum priority and the adversary automaton. -/
def closingMonitor {I₁ I₂ O₁ O₂ Q : Type*} {D n : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (start : Q) (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (future : Fin n → I₁ × I₂ × Graph) : Q :=
  (List.ofFn (fun i => (future i,closingOutputs plan bound future i))).foldl
    (fun q letter => step q letter.1 letter.2) start

/-- Replacing a closing plan by an equal finite description preserves any
such deterministic monitor, including the segment's minimum priority. -/
theorem closingMonitor_equal {I₁ I₂ O₁ O₂ Q : Type*} {D n : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (start : Q) (first second : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (same : first = second) (bound : n ≤ D) (future : Fin n → I₁ × I₂ × Graph) :
    closingMonitor step start first bound future = closingMonitor step start second bound future := by
  rw [same]

/-- Every family of past histories has only finitely many D-round response
behaviours, even if the family contains unboundedly many histories. This
counts behaviours, not histories or the information known to the leader. -/
theorem finitely_many_closing_behaviours {H I₁ I₂ O₁ O₂ : Type*}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) (D : Nat) :
    Finite {plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D //
      ∃ h, closingPlanOfStrategy σ (past h) D = plan} := by
  infer_instance

/-- Entries agree whenever the corresponding received input/graph prefixes
agree, regardless of how those prefixes are continued later. -/
theorem closingOutputs_causal {I₁ I₂ O₁ O₂ : Type*} {D n m : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (bn : n ≤ D) (bm : m ≤ D)
    (first : Fin n → I₁ × I₂ × Graph) (second : Fin m → I₁ × I₂ × Graph)
    (i : Fin n) (j : Fin m) (time : i.val = j.val)
    (prefixEq : ∀ a : Fin (i.val+1),
      first ⟨a.val,by omega⟩ = second ⟨a.val,by omega⟩) :
    closingOutputs plan bn first i = closingOutputs plan bm second j := by
  rcases i with ⟨iv, hi⟩
  rcases j with ⟨jv, hj⟩
  change iv = jv at time
  subst jv
  apply congrArg plan
  apply Prod.ext
  · rfl
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext a
  exact prefixEq a

/-- Advance a contingent plan after one environment round. This is an
algebraic update; its argument includes information not always visible to
both processes. -/
def prependClosingScenario {I₁ I₂ : Type*} {D : Nat}
    (round : I₁ × I₂ × Graph) (s : ClosingScenario I₁ I₂ D) :
    ClosingScenario I₁ I₂ (D+1) :=
  ((), ⟨⟨s.2.1.val+1, by have := s.2.1.isLt; omega⟩,
    Fin.cases round s.2.2⟩)

def advanceClosingPlan {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (round : I₁ × I₂ × Graph) : LeaderClosingPlan I₁ I₂ O₁ O₂ D :=
  fun s => plan (prependClosingScenario round s)

theorem prependClosingScenario_history {I₁ I₂ : Type*} {D : Nat}
    (h : EnvHistory I₁ I₂) (round : I₁ × I₂ × Graph)
    (s : ClosingScenario I₁ I₂ D) :
    windowHistory (fun _ : Unit => h) (D+1) (prependClosingScenario round s) =
    windowHistory (fun _ : Unit => h ++ [⟨round.1,round.2.1,round.2.2,(),()⟩]) D s := by
  simp [windowHistory, prependClosingScenario, List.ofFn_succ, List.append_assoc]

/-- Advancing a locally consistent plan preserves local consistency at the
updated history, including the ambiguity between one-way and both-way
reception. -/
theorem advanceClosingPlan_coherent {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (h : EnvHistory I₁ I₂) (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (coherent : WindowCoherent (fun _ : Unit => h) (D+1) plan)
    (round : I₁ × I₂ × Graph) :
    WindowCoherent
      (fun _ : Unit => h ++ [⟨round.1,round.2.1,round.2.2,(),()⟩]) D
      (advanceClosingPlan plan round) := by
  constructor
  · intro s t same
    apply coherent.1 (prependClosingScenario round s) (prependClosingScenario round t)
    simpa only [prependClosingScenario_history] using same
  · intro s t same
    apply coherent.2 (prependClosingScenario round s) (prependClosingScenario round t)
    simpa only [prependClosingScenario_history] using same

/-- The remaining entries are exactly the plan extracted at the updated
history. This enforces consistency on the overlap of consecutive plans. -/
theorem advanceClosingPlan_ofStrategy {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂)
    (round : I₁ × I₂ × Graph) :
    advanceClosingPlan (closingPlanOfStrategy σ h (D+1)) round =
    closingPlanOfStrategy σ (h ++ [⟨round.1,round.2.1,round.2.2,(),()⟩]) D := by
  funext s
  unfold advanceClosingPlan closingPlanOfStrategy
  rw [prependClosingScenario_history]

end Characterisation
