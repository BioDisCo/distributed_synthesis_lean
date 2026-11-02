/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentGames.ConsensusGap

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
variable {V : Type}

/-- The manuscript's unbounded-time consensus requirements on actual
reactive executions. Later private inputs remain unrestricted. -/
structure Solves (σ : StrategyPair V V (Option V) (Option V))
    (A : Set (Nat → Graph)) : Prop where
  irrevocable : ∀ env, (fun n => (env n).graph) ∈ A → ∀ p n m, n ≤ m → ∀ v,
    outputAt σ env n p = some v → outputAt σ env m p = some v
  valid : ∀ env, (fun n => (env n).graph) ∈ A → ∀ o : Proc → V,
    (∀ p, ∃ n, outputAt σ env n p = some (o p)) → (task V).allows (proposals env) o
  terminates : ∀ env, (fun n => (env n).graph) ∈ A → ∀ p,
    ∃ n v, outputAt σ env n p = some v

theorem SolvesBy.solves {σ : StrategyPair V V (Option V) (Option V)}
    {A : Set (Nat → Graph)} {R : Nat} (h : SolvesBy σ A R) : Solves σ A where
  irrevocable := h.irrevocable
  valid := h.valid
  terminates := by
    intro env admitted p
    obtain ⟨n,_,v,value⟩ := h.bound env admitted p
    exact ⟨n,v,value⟩

/-- Retain the first local decision using the own-history chain already
stored in the full view. No extra information is supplied to a process. -/
def retainDecision (candidate : (p : Proc) → View V V p → Option V) :
    {p : Proc} → View V V p → Option V
  | _, .empty _ => none
  | p, .noRecv v i => (retainDecision candidate v).or (candidate p (.noRecv v i))
  | p, .recv v i w j => (retainDecision candidate v).or (candidate p (.recv v i w j))

def retainedStrategy (candidate : (p : Proc) → View V V p → Option V) :
    StrategyPair V V (Option V) (Option V) := ⟨retainDecision candidate,retainDecision candidate⟩

theorem retainDecision_append (candidate : (p : Proc) → View V V p → Option V)
    (h : EnvHistory V V) (r : RoundRecord V V Graph Unit Unit) (p : Proc) :
    retainDecision candidate (currentView p (h++[r])) =
      (retainDecision candidate (currentView p h)).or (candidate p (currentView p (h++[r]))) := by
  cases p <;> cases g : r.graph <;>
    simp only [show h++[r] = History.append h r from rfl,
      currentView_one_append,currentView_two_append,g,retainDecision]

theorem retainDecision_witness (candidate : (p : Proc) → View V V p → Option V)
    (env : EnvironmentSequence V V) (p : Proc) (n : Nat) (v : V)
    (value : retainDecision candidate (currentView p (branchNode (environmentWord env) n)) = some v) :
    ∃ k, 0 < k ∧ k ≤ n ∧ candidate p (currentView p (branchNode (environmentWord env) k)) = some v := by
  induction n with
  | zero =>
    cases p <;> change (none : Option V) = some v at value <;> contradiction
  | succ n ih =>
    change retainDecision candidate (currentView p (_ ++ [_])) = _ at value
    rw [retainDecision_append] at value
    cases old : retainDecision candidate (currentView p (branchNode (environmentWord env) n)) with
    | none => exact ⟨n+1,by omega,le_rfl,by simpa only [old,Option.none_or] using value⟩
    | some u =>
      have eq : u = v := Option.some.inj (by simpa only [old,Option.some_or] using value)
      subst u
      obtain ⟨k,positive,before,decided⟩ := ih old
      exact ⟨k,positive,by omega,decided⟩

theorem retainDecision_stable (candidate : (p : Proc) → View V V p → Option V)
    (env : EnvironmentSequence V V) (p : Proc) (n m : Nat) (before : n ≤ m) (v : V)
    (value : retainDecision candidate (currentView p (branchNode (environmentWord env) n)) = some v) :
    retainDecision candidate (currentView p (branchNode (environmentWord env) m)) = some v := by
  induction m, before using Nat.le_induction with
  | base => exact value
  | succ m _ ih =>
    change retainDecision candidate (currentView p (_ ++ [_])) = _
    rw [retainDecision_append,ih,Option.some_or]

theorem retainDecision_exists (candidate : (p : Proc) → View V V p → Option V)
    (env : EnvironmentSequence V V) (p : Proc) (n : Nat) (v : V)
    (value : candidate p (currentView p (branchNode (environmentWord env) (n+1))) = some v) :
    ∃ w, retainDecision candidate (currentView p (branchNode (environmentWord env) (n+1))) = some w := by
  change ∃ w, retainDecision candidate (currentView p (_ ++ [_])) = some w
  change candidate p (currentView p (branchNode (environmentWord env) n ++ [environmentWord env n])) = some v at value
  rw [retainDecision_append,value]
  cases retainDecision candidate (currentView p (branchNode (environmentWord env) n)) <;> simp

theorem retained_output (candidate : (p : Proc) → View V V p → Option V)
    (env : EnvironmentSequence V V) (n : Nat) (p : Proc) :
    outputAt (retainedStrategy candidate) env n p =
      retainDecision candidate (currentView p (branchNode (environmentWord env) (n+1))) := by
  rw [outputAt_view]
  cases p <;> rfl

/-- If every tentative decision is the same valid proposal and a tentative
decision eventually occurs locally, retaining the first one solves consensus. -/
theorem retained_solves (candidate : (p : Proc) → View V V p → Option V)
    (A : Set (Nat → Graph))
    (consistent : ∀ env, (fun n => (env n).graph) ∈ A → ∃ v,
      (v = proposals env .one ∨ v = proposals env .two) ∧ ∀ n p w,
        candidate p (currentView p (branchNode (environmentWord env) (n+1))) = some w → w = v)
    (terminates : ∀ env, (fun n => (env n).graph) ∈ A → ∀ p, ∃ n v,
      candidate p (currentView p (branchNode (environmentWord env) (n+1))) = some v) :
    Solves (retainedStrategy candidate) A := by
  constructor
  · intro env _ p n m before v value
    rw [retained_output] at value ⊢
    exact retainDecision_stable candidate env p (n+1) (m+1) (by omega) v value
  · intro env admitted o decisions
    obtain ⟨v,valid,common⟩ := consistent env admitted
    have eq (p : Proc) : o p = v := by
      obtain ⟨n,value⟩ := decisions p
      rw [retained_output] at value
      obtain ⟨k,positive,_,decided⟩ := retainDecision_witness candidate env p (n+1) (o p) value
      exact common (k-1) p (o p) (by simpa only [Nat.sub_add_cancel positive] using decided)
    exact ⟨(eq .one).trans (eq .two).symm, by simpa only [eq .one] using valid⟩
  · intro env admitted p
    obtain ⟨n,v,value⟩ := terminates env admitted p
    obtain ⟨w,decided⟩ := retainDecision_exists candidate env p n v value
    exact ⟨n,w,by rw [retained_output]; exact decided⟩

end Characterisation.ComponentGames.Consensus
