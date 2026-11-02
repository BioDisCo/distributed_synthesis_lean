/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.EndlessLeaderAcceptance

/-! The final phase of the concrete numbered decoder satisfies its residual
objective. No future boundary implies every subsequent graph is outgoing
from the agreed leader, including the first round of that final phase. -/
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

theorem numberedController_final_accepts
    (labels : EnvHistory I₁ I₂ → objective.State)
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (history : Nat → EnvHistory I₁ I₂) (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (next : ∀ n, history (n+1) = history n ++ [round n])
    (N : Nat) (live : P (History.graphSequence (history N)))
    (absent : ∀ n, N < n → leaderBoundary P d (history n) = false)
    (source : NumberedBoundaryRep M objective P labels header past (boundaryOrigin P (history N)))
    (legal : numberedLeaderLegal M objective rank header move = true) :
    let σ := chooseNumberedController M objective rank header past move.2 move.1
    objective.AcceptsFrom (labels (history N))
      (continuationTrace (strategyContinuationPolicy σ (fun _ : Unit => history N)) ()
        (fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo,(round (N+n)).graph))) := by
  let σ := chooseNumberedController M objective rank header past move.2 move.1
  obtain ⟨i,actual⟩ := (source.2.1 (history N)).mp
    (show InputConnected P (history N) (history N) from Relation.ReflTransGen.refl)
  have incoming := source.2.2.2.2.2 i
  rw [actual] at incoming
  have leader := numberedBoundaryRep_leader M objective P labels header past rank move (history N) live source legal
  have controller : NumberedController M objective rank header past move.2 move.1 σ :=
    chooseNumberedController_spec M objective rank header past move.2 move.1
      (by simpa only [Prod.eta] using legal) source.2.2.2.1 (List.length (history N)) source.2.2.1
  have outgoing : ∀ n, (round (N+n)).graph = leaderOutgoingGraph move.1 := by
    intro n
    have result := leader_phase_oneway_prefix P d history round next N (N+n+1+d+1)
      (fun t lower _ => absent t lower) (N+n) (by omega) (by omega)
    rwa [← leader] at result
  cases direction : move.1 with
  | one =>
    rw [direction] at controller
    obtain ⟨_,_,_,_,endless⟩ := controller
    have accepted := endless i (fun n => ((round (N+n)).inputTwo,(round (N+n)).inputOne))
    rw [incoming,continuationTrace_same_history σ past (fun _ : Unit => history N) i () actual] at accepted
    have env : (fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo,Graph.right)) =
        (fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo,(round (N+n)).graph)) := by
      funext n
      rw [outgoing,direction]
      rfl
    rw [env] at accepted
    simpa only [σ,direction] using accepted
  | two =>
    rw [direction] at controller
    obtain ⟨_,_,_,_,endless⟩ := controller
    have accepted := endless i (fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo))
    rw [incoming,continuationTrace_same_history σ past (fun _ : Unit => history N) i () actual] at accepted
    have env : (fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo,Graph.left)) =
        (fun n => ((round (N+n)).inputOne,(round (N+n)).inputTwo,(round (N+n)).graph)) := by
      funext n
      rw [outgoing,direction]
      rfl
    rw [env] at accepted
    simpa only [σ,direction] using accepted

end
end Characterisation
