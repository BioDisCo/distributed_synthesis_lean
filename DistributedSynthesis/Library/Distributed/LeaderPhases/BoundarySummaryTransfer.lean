/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphPhaseSuccessors

/-! The observation matrix and pointed graph-state bank determine the full
future component structure. Transfer uses the same root numbering, scenario,
and policy at every depth; it does not identify different physical rounds. -/
namespace Characterisation
open DistributedSynthesis

section GraphFuture
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
/-- A common finite graph bank gives the same admissible scenarios at every
future depth, including scenarios that leave the live prefix language. -/
theorem summary_future_live_iff (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    P (History.graphSequence (closingLayerHistory past n s)) ↔
      P (History.graphSequence (closingLayerHistory other n s)) := by
  have first := closingGraphRun_rep M P closed recognizes bounded past source pastGraph n s
  have second := closingGraphRun_rep M P closed recognizes bounded other source otherGraph n s
  exact (graphRootRep_live_iff M P _ _ first).symm.trans (graphRootRep_live_iff M P _ _ second)

include closed recognizes bounded pastGraph otherGraph in
/-- The next-boundary decision is the same on corresponding live histories.
The histories themselves may begin at different absolute depths. -/
theorem summary_future_boundary_eq (n : Nat) (s : ClosingLayer H I₁ I₂ (n+1))
    (live : P (History.graphSequence (closingLayerHistory past (n+1) s))) :
    leaderBoundary P d (closingLayerHistory past (n+1) s) =
      leaderBoundary P d (closingLayerHistory other (n+1) s) := by
  have first := closingGraphRun_rep M P closed recognizes bounded past source pastGraph n s.1
  have second := closingGraphRun_rep M P closed recognizes bounded other source otherGraph n s.1
  have otherLive := (summary_future_live_iff M P closed recognizes bounded past other source
    pastGraph otherGraph (n+1) s).mp live
  exact (graphRootBoundary_exact M P closed recognizes (closingLayerHistory past n s.1)
    (closingGraphRun M source n s.1) first ⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩ live).symm.trans
    (graphRootBoundary_exact M P closed recognizes (closingLayerHistory other n s.1)
      (closingGraphRun M source n s.1) second ⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩ otherLive)

include closed recognizes bounded pastGraph otherGraph in
/-- Every live phase ends at the same relative round after transfer. Flags
on forbidden scenarios and the depth-zero flag are irrelevant. -/
theorem summary_future_first_exit_eq (n : Nat) (s : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n s))) :
    closingFirstExit (fun m t => leaderBoundary P d (closingLayerHistory past m t)) n s =
      closingFirstExit (fun m t => leaderBoundary P d (closingLayerHistory other m t)) n s := by
  apply closingFirstExit_congr_on_live P closed past _ _ n ?_ n (Nat.le_refl n) s live
  intro m positive _ t alive
  cases m with
  | zero => omega
  | succ m =>
    exact summary_future_boundary_eq M P closed recognizes bounded past other source
      pastGraph otherGraph m t alive

variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable (shape : InputShape H)
variable (pastShape : RepresentsInputShape past shape) (otherShape : RepresentsInputShape other shape)
variable (pastCovers : ∀ h k, InputConnected P (past h) k → ∃ j, past j = k)
variable (otherCovers : ∀ h k, InputConnected P (other h) k → ∃ j, other j = k)

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers in
/-- Corresponding scenarios belong to the same full component in one
realization exactly when they do in the other. The shared finite mask is
computed from the common shape and graph bank; coverage is proved by the
existing full-component descendant theorem. -/
theorem summary_future_connected_iff (n : Nat) (root s : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n root))) :
    InputConnected P (closingLayerHistory past n root) (closingLayerHistory past n s) ↔
      InputConnected P (closingLayerHistory other n root) (closingLayerHistory other n s) := by
  let mask := fun t : ClosingLayer H I₁ I₂ n => (closingGraphRun M source n t).isSome
  have firstLive : ∀ t, mask t = true ↔ P (History.graphSequence (closingLayerHistory past n t)) :=
    fun t => graphRootRep_live_iff M P _ _
      (closingGraphRun_rep M P closed recognizes bounded past source pastGraph n t)
  have secondLive : ∀ t, mask t = true ↔ P (History.graphSequence (closingLayerHistory other n t)) :=
    fun t => graphRootRep_live_iff M P _ _
      (closingGraphRun_rep M P closed recognizes bounded other source otherGraph n t)
  have liveOther := (secondLive root).mp ((firstLive root).mpr live)
  exact (closingLayerComponentMask_exact P closed past shape pastShape pastCovers n mask firstLive root live s).symm.trans
    (closingLayerComponentMask_exact P closed other shape otherShape otherCovers n mask secondLive root liveOther s)

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers in
/-- The same retained scenarios enumerate the whole target component after
transfer. There is no independent selection of a new target for each root. -/
theorem summary_complete_enumeration_transfer {S : Type}
    (pastInjective : Function.Injective past) (n : Nat) (root : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n root)))
    (keep : S → ClosingLayer H I₁ I₂ n)
    (complete : ∀ k, InputConnected P (closingLayerHistory past n root) k ↔
      ∃ i, closingLayerHistory past n (keep i) = k) :
    ∀ k, InputConnected P (closingLayerHistory other n root) k ↔
      ∃ i, closingLayerHistory other n (keep i) = k := by
  intro k
  constructor
  · intro conn
    obtain ⟨s,eq⟩ := closingLayer_component_coverage P closed other otherCovers n root k conn
    have corresponding := (summary_future_connected_iff M P closed recognizes bounded past other source
      pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers n root s live).mpr
      (by rwa [eq])
    obtain ⟨i,entry⟩ := (complete _).mp corresponding
    have scenarios := closingLayerHistory_injective past pastInjective n entry
    exact ⟨i,by rw [scenarios,eq]⟩
  · rintro ⟨i,rfl⟩
    apply (summary_future_connected_iff M P closed recognizes bounded past other source
      pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers n root (keep i) live).mp
    exact (complete _).mpr ⟨i,rfl⟩

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers in
/-- A whole checked semantic handover transfers with its exact certificate,
numbering, replayed labels, and parent slots. Only the literal root histories
are replaced. All future output positions are kept. -/
theorem summary_closing_offer_transfer {O₁ O₂ Q : Type} {B D n : Nat}
    (pastInjective : Function.Injective past) (otherInjective : Function.Injective other)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (root : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n root)))
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (realizes : ClosingOfferRealizes P past step initial expected bound root move) :
    ClosingOfferRealizes P other step initial expected bound root move := by
  refine ⟨?_,?_,?_,realizes.2.2.2.1,?_⟩
  · intro i j equal
    have scenarios := closingLayerHistory_injective other otherInjective n equal
    apply realizes.1
    exact congrArg (closingLayerHistory past n) scenarios
  · exact summary_complete_enumeration_transfer M P closed recognizes bounded past other source
      pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers pastInjective n root live
      move.2.2.1 realizes.2.1
  · intro p i j
    exact (realizes.2.2.1 p i j).trans
      (((closingLayerShape_exact past shape pastShape n) p (move.2.2.1 i) (move.2.2.1 j)).symm.trans
        ((closingLayerShape_exact other shape otherShape n) p (move.2.2.1 i) (move.2.2.1 j)))
  · exact closingCertificate_parent_prefix other other (fun _ => ⟨[],by simp⟩) move

include closed recognizes bounded pastGraph otherGraph pastShape otherShape pastCovers otherCovers in
/-- A single local strategy transfers all future behavior at once: output
policies, graph admissibility, boundary tests, and complete components. This
is stronger than transferring each successor or finite window separately. -/
theorem boundary_summary_strategy_transfer {O₁ O₂ Q : Type}
    [Nonempty O₁] [Nonempty O₂]
    (L : Nat) (otherDepth : ∀ h, List.length (other h) = L)
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop) (initial : H → Q)
    (σ : StrategyPair I₁ I₂ O₁ O₂) :
    ∃ τ : StrategyPair I₁ I₂ O₁ O₂,
      strategyContinuationPolicy τ other = strategyContinuationPolicy σ past ∧
      (ContinuationWins accept initial (strategyContinuationPolicy τ other) ↔
        ContinuationWins accept initial (strategyContinuationPolicy σ past)) ∧
      (∀ n s, P (History.graphSequence (closingLayerHistory past n s)) ↔
        P (History.graphSequence (closingLayerHistory other n s))) ∧
      (∀ n s, P (History.graphSequence (closingLayerHistory past (n+1) s)) →
        leaderBoundary P d (closingLayerHistory past (n+1) s) =
          leaderBoundary P d (closingLayerHistory other (n+1) s)) ∧
      ∀ n root s, P (History.graphSequence (closingLayerHistory past n root)) →
        (InputConnected P (closingLayerHistory past n root) (closingLayerHistory past n s) ↔
          InputConnected P (closingLayerHistory other n root) (closingLayerHistory other n s)) := by
  obtain ⟨τ,policy⟩ := continuation_strategy_transfer past other shape pastShape otherShape L otherDepth σ
  refine ⟨τ,policy,by rw [policy],?_,?_,?_⟩
  · exact summary_future_live_iff M P closed recognizes bounded past other source pastGraph otherGraph
  · exact summary_future_boundary_eq M P closed recognizes bounded past other source pastGraph otherGraph
  · exact summary_future_connected_iff M P closed recognizes bounded past other source
      pastGraph otherGraph shape pastShape otherShape pastCovers otherCovers

end GraphFuture
end Characterisation
