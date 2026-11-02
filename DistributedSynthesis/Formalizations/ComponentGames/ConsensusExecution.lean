/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusSearchTermination
import DistributedSynthesis.Library.Distributed.InputAlphabetRelabeling

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2000000
variable {V : Type}

/-- Read the first own input from a full view. -/
def firstPayload : {p : Proc} → View V V p → Option (PSum V V)
  | _, .empty _ => none
  | _, .noRecv v i => (firstPayload v).or (some i)
  | _, .recv v i _ _ => (firstPayload v).or (some i)

/-- Locally simulate the view obtained by repeating initial proposals. -/
def proposalView : {p : Proc} → View V V p → View V V p
  | _, .empty p => .empty p
  | _, .noRecv v i => .noRecv (proposalView v) ((firstPayload v).getD i)
  | _, .recv v i w j => .recv (proposalView v) ((firstPayload v).getD i)
      (proposalView w) ((firstPayload w).getD j)

/-- Reuse the library's view depth after erasing private-input values. -/
def viewDepth {p : Proc} (v : View V V p) : Nat :=
  FullViewPath.depth (InputAlphabetRelabeling.view (fun _ => ()) (fun _ => ()) v)

theorem viewDepth_history (h : EnvHistory V V) (p : Proc) :
    viewDepth (currentView p h) = List.length h := by
  induction h using List.reverseRecOn with
  | nil => cases p <;> rfl
  | append_singleton h r ih =>
    change viewDepth (currentView p (History.append h r)) = _
    cases p
    all_goals simp only [currentView_one_append,currentView_two_append]
    all_goals cases r.graph <;> simp_all [viewDepth,InputAlphabetRelabeling.view,FullViewPath.depth]

def proposalPayload (x : Proc → V) : Proc → PSum V V
  | .one => .inl (x .one)
  | .two => .inr (x .two)

theorem firstPayload_environment (env : EnvironmentSequence V V) (n : Nat) (p : Proc) :
    firstPayload (currentView p (branchNode (environmentWord env) n)) =
      if n = 0 then none else some (proposalPayload (proposals env) p) := by
  induction n with
  | zero => cases p <;> rfl
  | succ n ih =>
    change firstPayload (currentView p (History.append _ _)) = _
    cases p
    all_goals simp only [currentView_one_append,currentView_two_append]
    all_goals cases g : (environmentWord env n).graph
    all_goals simp only [firstPayload,ih]
    all_goals cases n <;> simp [environmentWord,proposals,proposalPayload]

theorem proposalView_environment (env : EnvironmentSequence V V) (n : Nat) (p : Proc) :
    proposalView (currentView p (branchNode (environmentWord env) n)) =
      currentView p (proposalHistory (proposals env) (graphPrefix (fun t => (env t).graph) n)) := by
  induction n generalizing p with
  | zero => cases p <;> rfl
  | succ n ih =>
    rw [graphPrefix_succ,proposalHistory_append]
    change proposalView (currentView p (History.append _ _)) = currentView p (History.append _ _)
    cases p
    all_goals simp only [currentView_one_append,currentView_two_append]
    all_goals cases g : (env n).graph
    all_goals simp only [environmentWord,g,proposalView,Proc.other,ih,firstPayload_environment]
    all_goals cases n <;> simp [proposals,proposalPayload]

/-- A fixed-round table is executed at R and then retained by reading the
round-R view from perfect recall. -/
def retainTable (R : Nat) (table : StrategyPair V V V V) : StrategyPair V V (Option V) (Option V) :=
  ⟨fun v => if R ≤ viewDepth v then some (table.one (proposalView (lagView (viewDepth v-R) v))) else none,
   fun v => if R ≤ viewDepth v then some (table.two (proposalView (lagView (viewDepth v-R) v))) else none⟩

def tableOutcome (table : StrategyPair V V V V) (env : EnvironmentSequence V V) (R : Nat) : Proc → V
  | .one => table.one (currentView .one (proposalHistory (proposals env) (graphPrefix (fun t => (env t).graph) R)))
  | .two => table.two (currentView .two (proposalHistory (proposals env) (graphPrefix (fun t => (env t).graph) R)))

theorem roundView_environment (env : EnvironmentSequence V V) (n R : Nat)
    (le : R ≤ n) (p : Proc) :
    lagView (n-R) (currentView p (branchNode (environmentWord env) n)) =
      currentView p (branchNode (environmentWord env) R) := by
  have len : List.length (branchNode (environmentWord env) n) = n := by simp [branchNode_eq_ofFn]
  rw [lagView_take p _ (n-R) (by rw [len]; omega),len,Nat.sub_sub_self le,take_branchNode _ _ _ le]

theorem retainTable_output (R : Nat) (table : StrategyPair V V V V)
    (env : EnvironmentSequence V V) (n : Nat) (p : Proc) :
    outputAt (retainTable R table) env n p =
      if R ≤ n+1 then some (tableOutcome table env R p) else none := by
  rw [outputAt_view]
  have len : List.length (branchNode (environmentWord env) (n+1)) = n+1 := by simp [branchNode_eq_ofFn]
  cases p
  all_goals simp only [strategyOutput,retainTable,viewDepth_history,len]
  all_goals split <;> rename_i bound
  all_goals first
    | rfl
    | rw [roundView_environment _ _ _ bound,proposalView_environment]; rfl

theorem retainTable_solves (R : Nat) (positive : 0 < R) (table : StrategyPair V V V V)
    (A : Set (Nat → Graph))
    (correct : ∀ env, (fun n => (env n).graph) ∈ A →
      (task V).allows (proposals env) (tableOutcome table env R)) :
    SolvesBy (retainTable R table) A R := by
  constructor
  · intro env _ p n m le v decided
    rw [retainTable_output] at decided ⊢
    split at decided
    · rename_i bound
      rw [if_pos (by omega)]
      exact decided
    · contradiction
  · intro env admitted o decisions
    have eq : o = tableOutcome table env R := by
      funext p
      obtain ⟨n,decided⟩ := decisions p
      rw [retainTable_output] at decided
      split at decided
      · exact (Option.some.inj decided).symm
      · contradiction
    rw [eq]
    exact correct env admitted
  · intro env _ p
    refine ⟨R-1,by omega,tableOutcome table env R p,?_⟩
    rw [retainTable_output,if_pos (by omega)]

variable (M : DetParityAutomaton Graph) [DecidableEq M.State]

/-- The reverse direction of the manuscript's finite test, now on genuine
reactive executions with unrestricted later private inputs. -/
theorem solves_of_checkState (q : M.State) (R : Nat) (positive : 0 < R)
    (success : checkState M q R = true) :
    ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ (stateLanguage M q) R := by
  obtain ⟨table,correct⟩ := (checkState_exact M q R).mp success
  refine ⟨retainTable R table,retainTable_solves R positive table (stateLanguage M q) ?_⟩
  intro env admitted
  let c : TestCase R := ⟨proposals env,⟨graphPrefix (fun t => (env t).graph) R,by simp [graphPrefix]⟩⟩
  have live : liveState M ((prefixRecognizer M).evalFrom q c.2.val) = true := by
    apply (liveState_correct M _).mpr
    refine ⟨OmegaWord.drop (fun t => (env t).graph) R,?_⟩
    rw [show (prefixRecognizer M).evalFrom q c.2.val = M.runFrom q (fun t => (env t).graph) R from
      prefixRecognizer_eval M q (fun t => (env t).graph) R]
    exact (M.acceptsFrom_runFrom_drop_iff q _ R).mpr admitted
  exact correct c live

theorem checkState_iff_solves (q : M.State) (R : Nat) (positive : 0 < R) :
    checkState M q R = true ↔
      ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool), SolvesBy σ (stateLanguage M q) R := by
  constructor
  · exact solves_of_checkState M q R positive
  · rintro ⟨σ,solves⟩
    exact checkState_of_solves M q R positive σ solves

end Characterisation.ComponentGames.Consensus
