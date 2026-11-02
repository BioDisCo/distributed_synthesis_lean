/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderWitnesses
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA

/-! Concrete physical objectives for joint one-way phases. Boolean closure
retains the adversary's infinite acceptance, and finite conjunction checks
every possible initial root under its own residual objective state. -/
namespace Characterisation
open DistributedSynthesis

/-- The original adversary is retained as an omega-language, including when
it is not closed. This automaton is also suitable for the global phase-minimum
construction, whose physical winning premise then ranges over all words. -/
noncomputable def guardedPhysicalObjective {I₁ I₂ O₁ O₂ : Type}
    (adversary : DetParityAutomaton Graph)
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)) :
    DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂) :=
  (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
    (A := ((adversary.comap (fun letter : ContinuationLetter I₁ I₂ O₁ O₂ => letter.1.2.2)).toMuller.compl).union
      objective.toMuller)).dpa

theorem guardedPhysicalObjective_accepts_iff {I₁ I₂ O₁ O₂ : Type}
    (adversary : DetParityAutomaton Graph)
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (word : Nat → ContinuationLetter I₁ I₂ O₁ O₂) :
    (guardedPhysicalObjective adversary objective).Accepts word ↔
      (adversary.Accepts (fun n => (word n).1.2.2) → objective.Accepts word) := by
  rw [guardedPhysicalObjective, DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation.correct,
    DetMullerAutomaton.union_accepts_iff, DetMullerAutomaton.compl_accepts_iff,
    DetParityAutomaton.toMuller_accepts_iff, DetParityAutomaton.toMuller_accepts_iff,
    DetParityAutomaton.comap_accepts_iff]
  tauto

noncomputable def phaseObjectiveConjunction {H Letter : Type}
    (objectives : H → DetParityAutomaton Letter) : List H → DetMullerAutomaton Letter
  | [] => DetParityAutomaton.top.toMuller
  | h :: rest => (objectives h).toMuller.inter (phaseObjectiveConjunction objectives rest)

theorem phaseObjectiveConjunction_accepts_iff {H Letter : Type}
    (objectives : H → DetParityAutomaton Letter) (roots : List H) (word : Nat → Letter) :
    (phaseObjectiveConjunction objectives roots).Accepts word ↔
      ∀ h ∈ roots, (objectives h).Accepts word := by
  induction roots with
  | nil => simp [phaseObjectiveConjunction, DetParityAutomaton.toMuller_accepts_iff]
  | cons h rest ih =>
    simp only [phaseObjectiveConjunction, DetMullerAutomaton.inter_accepts_iff,
      DetParityAutomaton.toMuller_accepts_iff, ih, List.mem_cons, forall_eq_or_imp]

def jointPhaseLetter {H G I₁ I₂ O₁ O₂ : Type} (group : H → G)
    (letter : RealizedBlockRound I₂ I₁ (H → O₂) (G → O₁)) (h : H) :
    ContinuationLetter I₁ I₂ O₁ O₂ :=
  ((letter.1.2, letter.1.1, .right), (letter.2.2 (group h), letter.2.1 h))

section Objective
variable {H G I₁ I₂ O₁ O₂ : Type} [Fintype H]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (initial : H → objective.State) (group : H → G)

noncomputable def jointPhaseDPA :
    DetParityAutomaton (RealizedBlockRound I₂ I₁ (H → O₂) (G → O₁)) := by
  classical
  exact (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
    (A := phaseObjectiveConjunction (fun h =>
      (objective.withInitial (initial h)).comap (fun letter => jointPhaseLetter group letter h))
      Finset.univ.toList)).dpa

theorem jointPhaseDPA_accepts_iff (play : Nat → RealizedBlockRound I₂ I₁ (H → O₂) (G → O₁)) :
    (jointPhaseDPA objective initial group).Accepts play ↔
      ∀ h, objective.AcceptsFrom (initial h) (fun n => jointPhaseLetter group (play n) h) := by
  classical
  rw [jointPhaseDPA, DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation.correct,
    phaseObjectiveConjunction_accepts_iff]
  simp only [Finset.mem_toList, Finset.mem_univ, forall_const,
    DetParityAutomaton.comap_accepts_iff, DetParityAutomaton.withInitial_accepts_iff]
  rfl

/-- All-root acceptance on hypothetical infinite rightward continuations is
stronger than needed after a handover, but the original winning strategy
satisfies it. It therefore suffices for finite-phase extraction and gives
the required acceptance whenever the actual phase never ends. -/
noncomputable def jointPhaseObjective : BlockRecordMonitor I₂ I₁ (H → O₂) (G → O₁) where
  State := (jointPhaseDPA objective initial group).State
  stateFinite := inferInstance
  initial := (jointPhaseDPA objective initial group).initial
  step := (jointPhaseDPA objective initial group).step
  priority := (jointPhaseDPA objective initial group).priority

theorem jointPhaseObjective_wins_iff (play : Nat → RealizedBlockRound I₂ I₁ (H → O₂) (G → O₁)) :
    (jointPhaseObjective objective initial group).WinsPlay play ↔
      ∀ h, objective.AcceptsFrom (initial h) (fun n => jointPhaseLetter group (play n) h) := by
  have runs : ∀ n, (jointPhaseObjective objective initial group).run play n =
      (jointPhaseDPA objective initial group).run play n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (jointPhaseDPA objective initial group).step _ _ = _
      rw [ih]
      rfl
  rw [← jointPhaseDPA_accepts_iff objective initial group play,
    DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  unfold BlockRecordMonitor.WinsPlay
  simp only [runs]
  rfl

end Objective

theorem continuationScenario_right_history {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (h : H) (env : Nat → I₂ × I₁) (n : Nat) :
    closingLayerHistory past n
      (continuationScenario h (fun i => ((env i).2, (env i).1, Graph.right)) n) =
      rollingSourceHistory past (branchNode env n) h := by
  induction n with
  | zero => simp [continuationScenario, closingLayerHistory, rollingSourceHistory, rightInputHistory, branchNode]
  | succ n ih =>
    change closingLayerHistory past n
      (continuationScenario h (fun i => ((env i).2, (env i).1, Graph.right)) n) ++ [_] = _
    rw [ih, branchNode, rollingSourceHistory_snoc]
    rfl

/-- Read the objective on the same physical outputs supplied by joint
readback. The suffix position n is evaluated at the full history of depth
|past h|+n+1; no physical position is contracted. -/
theorem jointPhaseTrace_of_outputs {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (past : H → EnvHistory I₁ I₂) (group : H → G)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (σ : StrategyPair I₁ I₂ O₁ O₂)
    (implements : ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (group h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h)
    (env : Nat → I₂ × I₁) (h : H) :
    (fun n => jointPhaseLetter group
      (phasePhysicalPlay Prod.fst (pairPlay receiver leader env) n) h) =
      continuationTrace (strategyContinuationPolicy σ past) h
        (fun n => ((env n).2, (env n).1, .right)) := by
  funext n
  unfold continuationTrace strategyContinuationPolicy
  rw [continuationScenario_right_history, branchNode]
  have outputs := implements (branchNode env n) (env n) h
  exact Prod.ext rfl (Prod.ext outputs.1.symm outputs.2.symm)

theorem jointPhaseObjective_original_wins {H G I₁ I₂ O₁ O₂ : Type} [Fintype H]
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (initial : H → objective.State) (group : H → G)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (base : G → View I₁ I₂ .one) (same : ∀ h, currentView .one (past h) = base (group h))
    (winning : ContinuationWins objective.AcceptsFrom initial (strategyContinuationPolicy σ past))
    (D : Nat) :
    ∀ env, (jointPhaseObjective objective initial group).WinsPlay (phasePhysicalPlay Prod.fst
      (pairPlay (rollingOriginalReceiver σ past D) (jointOriginalLeader σ base) env)) := by
  intro env
  apply (jointPhaseObjective_wins_iff objective initial group _).mpr
  intro h
  have implements : ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        jointOriginalLeader σ base (senderWord node) r.2 (group h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) =
        (rollingOriginalReceiver σ past D node r).1 h := by
    intro node r h
    refine ⟨?_, rfl⟩
    exact (rollingOriginalLeader_correct σ (fun _ : Unit => past h) (base (group h))
      (fun _ => same h) node r ()).symm
  rw [jointPhaseTrace_of_outputs past group _ _ σ implements env h]
  exact winning h (fun n => ((env n).2, (env n).1, .right))

/-- An accepting joint table gives acceptance of an actual endless phase
under its local readback. The residual state is carried from the preceding
execution; it is not recomputed from hypothetical earlier outputs of σ. -/
theorem jointPhaseObjective_readback {H G I₁ I₂ O₁ O₂ : Type} {D : Nat} [Fintype H]
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (initial : H → objective.State) (past : H → EnvHistory I₁ I₂) (group : H → G)
    (receiver : ReceiverBlockStrategy I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D))
    (leader : SenderBlockStrategy I₁ (G → O₁)) (σ : StrategyPair I₁ I₂ O₁ O₂)
    (implements : ∀ node r h,
      σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (group h) ∧
      σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h)
    (winning : ∀ env, (jointPhaseObjective objective initial group).WinsPlay
      (phasePhysicalPlay Prod.fst (pairPlay receiver leader env))) :
    ∀ h (env : Nat → I₂ × I₁), objective.AcceptsFrom (initial h)
      (continuationTrace (strategyContinuationPolicy σ past) h
        (fun n => ((env n).2, (env n).1, .right))) := by
  intro h env
  have result := (jointPhaseObjective_wins_iff objective initial group _).mp (winning env) h
  rwa [jointPhaseTrace_of_outputs past group receiver leader σ implements env h] at result

end Characterisation
