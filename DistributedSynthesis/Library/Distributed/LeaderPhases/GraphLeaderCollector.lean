/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphClosingOfferCompleteness
import DistributedSynthesis.Library.Distributed.LeaderPhases.OfferPreservingReadback

/-! Put the graph-coupled collector into finite leader-phase memory. At
each cut it reads the already-carried closing bank, not a newly guessed
certificate. The physical one-way round updates every field together. -/
namespace Characterisation
open DistributedSynthesis

abbrev GraphLeaderMemory (H GQ Q I₁ I₂ O₁ O₂ : Type) (d K : Nat) :=
  CoupledRootMemory H GQ Q d K × ClosingPlanBank H I₁ I₂ O₁ O₂ d × Bool

section
variable {H GQ Q I₁ I₂ O₁ O₂ : Type} {d K : Nat}

def graphLeaderBankRun (advance : GraphRootState GQ d K → GraphRootState GQ d K)
    (source : H → GraphRootState GQ d K) : Nat → H → GraphRootState GQ d K
  | 0 => source
  | n+1 => fun h => advance (graphLeaderBankRun advance source n h)

def graphLeaderRound (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) O₁) :
    H → RoundRecord I₁ I₂ Graph Unit Unit :=
  fun _ => ⟨letter.1.2,letter.1.1,.right,(),()⟩

def graphLeaderOutput (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) O₁) :
    H → O₁ × O₂ := fun h => (letter.2.2,letter.2.1.1 h)

variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)

def graphLeaderNext (state : GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) O₁) :
    GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K :=
  (coupledRootNext M step state.1 (graphLeaderRound letter,graphLeaderOutput letter,
    fun h => advance (state.1.1 h)),letter.2.1.2,false)

/-- Graph bank, activity, objective replay, carried plans, and initial-window
bit all refer to the same physical cut. In particular, the next bank is not
used to manufacture an offer for the preceding cut. -/
theorem graphLeaderMemory_run
    (source : H → GraphRootState GQ d K) (initial : H → Q)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) O₁)
    (n : Nat) :
    phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
      (graphLeaderNext M step advance) play n =
      ((graphLeaderBankRun advance source n,
        rootActivityRun (fun i h => graphRootStop M (graphLeaderBankRun advance source i h) .right) n,
        rootMonitorRun step initial (fun i => graphLeaderRound (play i)) (fun i => graphLeaderOutput (play i)) n),
        phaseMemoryRun bank rollingLeaderNext play n,decide (n = 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [phaseMemoryRun,ih]
    rfl

variable [Fintype H] [DecidableEq H] [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]

instance graphLeaderMemory_fintype : Fintype (GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K) := by
  letI : Fintype (ClosingPlanBank H I₁ I₂ O₁ O₂ d) := closingPlanBank_fintype d
  unfold GraphLeaderMemory
  infer_instance

/-- This has the collector signature of `finite_phase_preserving_offers`.
All graph scans and certificate numberings are enumerated internally from
the finite current state. The current input is irrelevant to offers from
this cut: their closing policies already cover every next input and graph. -/
def graphLeaderCollect {B C : Nat} (shape : InputShape H)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (state : GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K)
    (_letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) O₁) :
    Finset (LeaderHandover Q B C) :=
  graphClosingOffers M state.1.1 state.1.2.1 shape state.2.2 step state.1.2.2
    (closingPolicyOfBank state.2.1) slot minimum

theorem graphLeaderCollect_at_cut {B C : Nat} (shape : InputShape H)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (source : H → GraphRootState GQ d K) (initial : H → Q)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d)
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) O₁)
    (n : Nat) :
    graphLeaderCollect M step shape slot minimum
      (phaseMemoryRun ((source,(fun _ => true),initial),bank,true)
        (graphLeaderNext M step advance) play n) (play n) =
      graphClosingOffers M (graphLeaderBankRun advance source n)
        (rootActivityRun (fun i h => graphRootStop M (graphLeaderBankRun advance source i h) .right) n)
        shape (decide (n = 0)) step
        (rootMonitorRun step initial (fun i => graphLeaderRound (play i)) (fun i => graphLeaderOutput (play i)) n)
        (closingPolicyOfBank (phaseMemoryRun bank rollingLeaderNext play n)) slot minimum := by
  rw [graphLeaderMemory_run]
  rfl

end

section GraphCorrectness
variable {H GQ I₁ I₂ : Type} {d K : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)

include closed recognizes bounded in
/-- An internal deterministic graph update exists and is correct from every
represented source. This reuses the earlier finite graph-transition proof;
it does not require graph certificates as private-input outputs. -/
theorem graphLeaderBankRun_rep
    (history : Nat → H → EnvHistory I₁ I₂)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (rightward : ∀ n h, (round n h).graph = .right)
    (source : H → GraphRootState GQ d K)
    (start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (source h))
    (n : Nat) (h : H) :
    GraphRootRep P M (History.graphSequence (history n h))
      (graphLeaderBankRun (fun state => chooseGraphRootNext M state .right) source n h) := by
  induction n with
  | zero => exact start h
  | succ n ih =>
    have possible := graphRootStep_exists M P closed recognizes _ _ ih .right bounded
    have checked := chooseGraphRootNext_checked M _ .right possible
    have next := graphRootStep_correct M P closed recognizes _ _ ih .right _ checked
    simpa only [extension,History.graphSequence,List.map_append,List.map_cons,List.map_nil,
      rightward,graphLeaderBankRun] using next

include closed recognizes bounded in
theorem graphLeaderBankRun_checked
    (history : Nat → H → EnvHistory I₁ I₂)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (rightward : ∀ n h, (round n h).graph = .right)
    (source : H → GraphRootState GQ d K)
    (start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (source h))
    (n : Nat) (h : H) :
    checkGraphRootStep M
      (graphLeaderBankRun (fun state => chooseGraphRootNext M state .right) source n h)
      (round n h).graph
      (graphLeaderBankRun (fun state => chooseGraphRootNext M state .right) source (n+1) h) = true := by
  rw [rightward]
  have rep := graphLeaderBankRun_rep M P closed recognizes bounded history round extension rightward source start n h
  exact chooseGraphRootNext_checked M _ .right
    (graphRootStep_exists M P closed recognizes _ _ rep .right bounded)

include closed recognizes bounded in
/-- The internally generated graph bank supplies the live activity invariant
needed by collector soundness and completeness at every physical cut. -/
theorem graphLeaderBankRun_activity
    (a : Nat) (history : Nat → H → EnvHistory I₁ I₂)
    (prefixes : ∀ i j, i ≤ j → ∀ h, (history j h).take (a+i) = history i h)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (rightward : ∀ n h, (round n h).graph = .right)
    (source : H → GraphRootState GQ d K)
    (start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (source h))
    (n : Nat) :
    SourceActivityOnLive P d a (a+n) (history n)
      (rootActivityRun (fun i h => graphRootStop M
        (graphLeaderBankRun (fun state => chooseGraphRootNext M state .right) source i h) .right) n) := by
  have checked := graphLeaderBankRun_checked M P closed recognizes bounded history round extension rightward source start
  have result := graphRootBank_activity_exact M P closed recognizes a history prefixes round extension
    (graphLeaderBankRun (fun state => chooseGraphRootNext M state .right) source) start checked n
  simpa only [rightward] using result

end GraphCorrectness
end Characterisation
