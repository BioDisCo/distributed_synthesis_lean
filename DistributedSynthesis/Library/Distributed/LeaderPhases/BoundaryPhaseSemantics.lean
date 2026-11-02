/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundarySummaryTransfer

/-! Exact phase semantics under a change of boundary realization. A move
restricts the possible whole first handovers and the objective on a phase
that never ends. The strategy is chosen once, before all these demands.
These predicates are semantic; no decision procedure is asserted here. -/
namespace Characterisation
open DistributedSynthesis

def PhaseNeverEnds {H I₁ I₂ : Type} (P : List Graph → Prop) (d : Nat)
    (past : H → EnvHistory I₁ I₂) (h : H) (env : Nat → I₁ × I₂ × Graph) : Prop :=
  ∀ n, P (History.graphSequence (closingLayerHistory past n (continuationScenario h env n))) ∧
    closingFirstExit (fun m s => leaderBoundary P d (closingLayerHistory past m s))
      n (continuationScenario h env n) = false

/-- A complete handover at the first boundary. The certificate retains the
whole target component, its observation matrix, replayed labels, and parents.
The unbounded phase duration n is explicit and is not a public observation. -/
def FirstPhaseHandover {H I₁ I₂ O₁ O₂ Q : Type} {B C : Nat}
    (P : List Graph → Prop) (d : Nat) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (outcome : LeaderHandover Q B C) : Prop :=
  ∃ (n : Nat) (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B n n),
    P (History.graphSequence (closingLayerHistory past n root)) ∧
    closingFirstExit (fun m s => leaderBoundary P d (closingLayerHistory past m s)) n root = true ∧
    ClosingOfferRealizes P past step initial (fun m s => out m.val s) (Nat.le_refl n) root move ∧
    certificateHandover slot minimum move = outcome

/-- Every actual whole handover must be permitted. This is combined with
acceptance of every live continuation
whose current phase never ends. No infinite-phase demand is imposed on a
branch after it has handed control to the next leader. -/
def PhaseMoveRealized {H I₁ I₂ O₁ O₂ Q R : Type} {B C : Nat}
    (P : List Graph → Prop) (d : Nat) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (accept : R → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop) (incoming : H → R)
    (permitted : Set (LeaderHandover Q B C)) (out : ContinuationPolicy H I₁ I₂ O₁ O₂) : Prop :=
  (∀ outcome, FirstPhaseHandover P d past step initial slot minimum out outcome → outcome ∈ permitted) ∧
  ∀ h env, PhaseNeverEnds P d past h env → accept (incoming h) (continuationTrace out h env)

section Transfer
variable {H GQ I₁ I₂ : Type} {d K : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (past other : H → EnvHistory I₁ I₂) (source : H → GraphRootState GQ d K)
variable (pastGraph : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (source h))
variable (otherGraph : ∀ h, GraphRootRep P M (History.graphSequence (other h)) (source h))

include closed recognizes bounded pastGraph otherGraph in
theorem summary_phase_never_ends_iff (h : H) (env : Nat → I₁ × I₂ × Graph) :
    PhaseNeverEnds P d past h env ↔ PhaseNeverEnds P d other h env := by
  have transfer : ∀ first second : H → EnvHistory I₁ I₂,
      (∀ h, GraphRootRep P M (History.graphSequence (first h)) (source h)) →
      (∀ h, GraphRootRep P M (History.graphSequence (second h)) (source h)) →
      PhaseNeverEnds P d first h env → PhaseNeverEnds P d second h env := by
    intro first second firstGraph secondGraph never n
    have atRound := never n
    refine ⟨(summary_future_live_iff M P closed recognizes bounded first second source
      firstGraph secondGraph n _).mp atRound.1, ?_⟩
    rw [← summary_future_first_exit_eq M P closed recognizes bounded first second source
      firstGraph secondGraph n _ atRound.1]
    exact atRound.2
  exact ⟨transfer past other pastGraph otherGraph,transfer other past otherGraph pastGraph⟩

variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable (shape : InputShape H)
variable (pastShape : RepresentsInputShape past shape) (otherShape : RepresentsInputShape other shape)
variable (pastCovers : ∀ h k, InputConnected P (past h) k → ∃ j, past j = k)
variable (otherCovers : ∀ h k, InputConnected P (other h) k → ∃ j, other j = k)
variable (pastInjective : Function.Injective past) (otherInjective : Function.Injective other)

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers
  pastInjective otherInjective in
theorem summary_first_handover_transfer {O₁ O₂ Q : Type} {B C : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (outcome : LeaderHandover Q B C)
    (realized : FirstPhaseHandover P d past step initial slot minimum out outcome) :
    FirstPhaseHandover P d other step initial slot minimum out outcome := by
  obtain ⟨n,root,move,live,first,complete,advertised⟩ := realized
  refine ⟨n,root,move,?_,?_,?_,advertised⟩
  · exact (summary_future_live_iff M P closed recognizes bounded past other source
      pastGraph otherGraph n root).mp live
  · rwa [← summary_future_first_exit_eq M P closed recognizes bounded past other source
      pastGraph otherGraph n root live]
  · exact summary_closing_offer_transfer M P closed recognizes bounded past other source
      pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers
      pastInjective otherInjective step initial (fun m s => out m.val s) (Nat.le_refl n) root live move complete

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers
  pastInjective otherInjective in
theorem summary_first_handover_iff {O₁ O₂ Q : Type} {B C : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (outcome : LeaderHandover Q B C) :
    FirstPhaseHandover P d past step initial slot minimum out outcome ↔
      FirstPhaseHandover P d other step initial slot minimum out outcome :=
  ⟨summary_first_handover_transfer M P closed recognizes bounded past other source
      pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers
      pastInjective otherInjective step initial slot minimum out outcome,
    summary_first_handover_transfer M P closed recognizes bounded other past source
      otherGraph pastGraph shape otherShape pastShape otherCovers pastCovers
      otherInjective pastInjective step initial slot minimum out outcome⟩

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers
  pastInjective otherInjective in
/-- Equality of finite boundary data preserves the entire local phase
specification, including arbitrarily late first handovers and infinite plays. The permitted
set may contain additional outcomes, as in the finite phase-offer monitor.
Both orientations and all private-input streams are quantified here. -/
theorem summary_phase_move_iff {O₁ O₂ Q R : Type} {B C : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (accept : R → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop) (incoming : H → R)
    (permitted : Set (LeaderHandover Q B C)) (out : ContinuationPolicy H I₁ I₂ O₁ O₂) :
    PhaseMoveRealized P d past step initial slot minimum accept incoming permitted out ↔
      PhaseMoveRealized P d other step initial slot minimum accept incoming permitted out := by
  unfold PhaseMoveRealized
  have handovers := summary_first_handover_iff M P closed recognizes bounded past other source
    pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers pastInjective otherInjective
    step initial slot minimum out
  have infinite := summary_phase_never_ends_iff M P closed recognizes bounded past other source
    pastGraph otherGraph
  constructor
  · rintro ⟨exactProfile,winning⟩
    exact ⟨fun outcome offered => exactProfile outcome ((handovers outcome).mpr offered),
      fun h env never => winning h env ((infinite h env).mpr never)⟩
  · rintro ⟨exactProfile,winning⟩
    exact ⟨fun outcome offered => exactProfile outcome ((handovers outcome).mp offered),
      fun h env never => winning h env ((infinite h env).mp never)⟩

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers
  pastInjective otherInjective in
/-- One transferred distributed strategy has exactly the same whole
handover profiles and final-phase guarantees as the original strategy.
The existential choice precedes every objective and every profile. -/
theorem boundary_summary_phase_strategy_transfer {O₁ O₂ : Type} [Nonempty O₁] [Nonempty O₂]
    (L : Nat) (otherDepth : ∀ h, List.length (other h) = L)
    (σ : StrategyPair I₁ I₂ O₁ O₂) :
    ∃ τ : StrategyPair I₁ I₂ O₁ O₂,
      strategyContinuationPolicy τ other = strategyContinuationPolicy σ past ∧
      ∀ {Q R : Type} {B C : Nat}
        (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
        (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
        (accept : R → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop) (incoming : H → R)
        (permitted : Set (LeaderHandover Q B C)),
        PhaseMoveRealized P d past step initial slot minimum accept incoming permitted
          (strategyContinuationPolicy σ past) ↔
        PhaseMoveRealized P d other step initial slot minimum accept incoming permitted
          (strategyContinuationPolicy τ other) := by
  obtain ⟨τ,policy⟩ := continuation_strategy_transfer past other shape pastShape otherShape L otherDepth σ
  refine ⟨τ,policy,?_⟩
  intro Q R B C step initial slot minimum accept incoming permitted
  rw [policy]
  exact summary_phase_move_iff M P closed recognizes bounded past other source
    pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers pastInjective otherInjective
    step initial slot minimum accept incoming permitted (strategyContinuationPolicy σ past)

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers
  pastInjective otherInjective in
/-- A phase specification is realizable at one complete boundary family if
and only if it is realizable at any other family with the same finite data.
This is a semantic equivalence, not a decidability assertion. -/
theorem boundary_summary_phase_realizable_iff {O₁ O₂ Q R : Type} {B C : Nat}
    [Nonempty O₁] [Nonempty O₂]
    (L N : Nat) (pastDepth : ∀ h, List.length (past h) = L)
    (otherDepth : ∀ h, List.length (other h) = N)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (accept : R → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop) (incoming : H → R)
    (permitted : Set (LeaderHandover Q B C)) :
    (∃ σ : StrategyPair I₁ I₂ O₁ O₂, PhaseMoveRealized P d past step initial slot minimum
      accept incoming permitted (strategyContinuationPolicy σ past)) ↔
    (∃ τ : StrategyPair I₁ I₂ O₁ O₂, PhaseMoveRealized P d other step initial slot minimum
      accept incoming permitted (strategyContinuationPolicy τ other)) := by
  constructor
  · rintro ⟨σ,realizes⟩
    obtain ⟨τ,_,preserves⟩ := boundary_summary_phase_strategy_transfer M P closed recognizes bounded
      past other source pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers
      pastInjective otherInjective N otherDepth σ
    exact ⟨τ,(preserves step initial slot minimum accept incoming permitted).mp realizes⟩
  · rintro ⟨τ,realizes⟩
    obtain ⟨σ,_,preserves⟩ := boundary_summary_phase_strategy_transfer M P closed recognizes bounded
      other past source otherGraph pastGraph shape otherShape pastShape otherCovers pastCovers
      otherInjective pastInjective L pastDepth τ
    exact ⟨σ,(preserves step initial slot minimum accept incoming permitted).mp realizes⟩

end Transfer
end Characterisation
