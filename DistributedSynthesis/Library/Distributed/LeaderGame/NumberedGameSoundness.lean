/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedGameMachine

/-! Instantiate global physical parity with the concrete numbered decoder
and successor selector. No local edge or minimum-correctness oracle remains. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (P : List Graph → Prop)
variable (tree : LabeledTree
  (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
  (NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
variable (initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

noncomputable def numberedGameInitialCode : HandoverCode B C :=
  carriedHandoverCode (numberedGameSlot objective)
    (initialCarriedLeaderState (fun q => (rank q).val) objective.initial ([],initial)) []

variable (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)

include closed recognizes recent bounded small in
theorem numberedGame_infinite_handover_soundness
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)))
    (accepted : (numberedLeaderGame M objective rank initial.1 (numberedGameInitialCode objective rank initial)).WinningTree tree) :
    ∃ read : LeaderPhaseOrigin I₁ I₂ → NumberedGameState (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read (boundaryOrigin P h) = numberedGameMachine M objective rank P tree initial h) ∧
      ImplementsPhaseFamily P d (fun origin => numberedGameDecode M objective rank tree origin (read origin)) σ ∧
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        (numberedGameMachine M objective rank P tree initial h).label h =
          strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial h) ∧
      ∀ (history : Nat → EnvHistory I₁ I₂)
        (_depth : ∀ n, List.length (history n) = n)
        (_prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
        (_live : ∀ n, P (History.graphSequence (history n)))
        (cuts : Nat → Nat), LeaderPhaseCuts P d history cuts →
        NatSeqMinEvenParity (fun n => (rank (strategyHistoryLabel σ
          (fun s input output => objective.step s (input,output)) objective.initial (history (n+1)))).val) := by
  letI : Inhabited (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := ⟨initial.1⟩
  have accepted' : (supportedLeaderProgressMonitor (numberedLeaderOffers objective)
      (numberedGameInitialCode objective rank initial) initial.1
      (fun header move => numberedLeaderLegal M objective rank header move = true)).WinningTree tree := accepted
  have validTree := ((supportedLeaderProgress_winning_iff (numberedLeaderOffers objective)
    (numberedGameInitialCode objective rank initial) initial.1
    (fun header move => numberedLeaderLegal M objective rank header move = true) tree).mp accepted').1
  exact carriedPublicGame_physical_parity P closed d recent
    (fun s input output => objective.step s (input,output)) rank objective.initial initial
    (numberedGameDecode M objective rank tree) (numberedGameSelect M objective rank P tree)
    (numberedGameSlot objective) (numberedLeaderOffers objective) initial.1
    (fun header move => numberedLeaderLegal M objective rank header move = true) tree accepted'
    (fun h a live interval boundary => numberedGameMachine_actual_edge M objective rank P tree initial
      closed recognizes recent bounded small validTree initialRep h live a interval boundary)

end
end Characterisation
