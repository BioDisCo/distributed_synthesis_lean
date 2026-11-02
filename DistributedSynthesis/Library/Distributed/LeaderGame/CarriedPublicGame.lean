/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.CarriedNumberedHandover
import DistributedSynthesis.Library.Distributed.LeaderGame.PublicGameRealization

/-! Public histories and parity for a controller that retains its complete
carried state. The physical minimum equation is proved by construction, not
assumed as a local certificate premise. -/
namespace Characterisation
open DistributedSynthesis

section
variable {Payload Q I₁ I₂ O₁ O₂ Outcome : Type}
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (priority : Q → Nat)
variable (decode : LeaderPhaseOrigin I₁ I₂ →
  CarriedLeaderState (List Outcome × Payload) Q I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
variable (select : CarriedLeaderState (List Outcome × Payload) Q I₁ I₂ →
  LeaderPhaseOrigin I₁ I₂ → LeaderPhaseOrigin I₁ I₂ →
  (EnvHistory I₁ I₂ → Q) → (EnvHistory I₁ I₂ → Nat) → Outcome × Payload)

def carriedPublicUpdate (state : CarriedLeaderState (List Outcome × Payload) Q I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂)
    (labels : EnvHistory I₁ I₂ → Q) (minima : EnvHistory I₁ I₂ → Nat) : List Outcome × Payload :=
  let chosen := select state old target labels minima
  (state.data.1 ++ [chosen.1],chosen.2)

def carriedPublicObservation (fallback : Outcome)
    (state : CarriedLeaderState (List Outcome × Payload) Q I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂) : Outcome :=
  ((carriedLeaderAdvance step priority decode (carriedPublicUpdate select) state old target).data.1.getLast?).getD fallback

theorem carriedPublicAdvance_node (fallback : Outcome)
    (state : CarriedLeaderState (List Outcome × Payload) Q I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂) :
    (carriedLeaderAdvance step priority decode (carriedPublicUpdate select) state old target).data.1 =
      state.data.1 ++ [carriedPublicObservation step priority decode select fallback state old target] := by
  simp only [carriedPublicObservation,carriedLeaderAdvance,carriedPublicUpdate,
    List.getLast?_concat,Option.getD_some]

variable (P : List Graph → Prop) (d : Nat) (q₀ : Q) (initial : Payload)

include select in
theorem carriedPublicHistory_exact (closed : PrefixClosed P) (fallback : Outcome)
    (read : LeaderPhaseOrigin I₁ I₂ → CarriedLeaderState (List Outcome × Payload) Q I₁ I₂)
    (reads : ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
      read (boundaryOrigin P h) =
        carriedLeaderMachine P d step priority q₀ ([],initial) decode (carriedPublicUpdate select) h)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) :
    publicHandoverHistory P d
      (fun _ old target => carriedPublicObservation step priority decode select fallback (read old) old target) h =
      (carriedLeaderMachine P d step priority q₀ ([],initial) decode (carriedPublicUpdate select) h).data.1 := by
  have claim : ∀ n (h : EnvHistory I₁ I₂), List.length h = n → P (History.graphSequence h) →
      publicHandoverHistory P d
        (fun _ old target => carriedPublicObservation step priority decode select fallback (read old) old target) h =
        (carriedLeaderMachine P d step priority q₀ ([],initial) decode (carriedPublicUpdate select) h).data.1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h length live
      by_cases empty : h = []
      · subst h
        simp only [publicHandoverHistory,carriedLeaderMachine,boundaryMachine_empty,initialCarriedLeaderState]
      · have positive := List.length_pos_iff.mpr empty
        let a := previousLeaderBoundary P d h
        have phase := previousLeaderBoundary_interval P d h positive
        have less : a < List.length h := phase.start_lt
        have rootLength : List.length (h.take a) = a := by
          simp only [List.length_take,min_eq_left (Nat.le_of_lt less)]
        have liveRoot := live_history_take P closed h live a
        have recursive := ih a (by omega) (h.take a) rootLength liveRoot
        rw [publicHandoverHistory_boundary P d _ h a phase,recursive,reads _ liveRoot]
        change _ = (boundaryMachine P d (initialCarriedLeaderState priority q₀ ([],initial))
          (carriedLeaderAdvance step priority decode (carriedPublicUpdate select)) h).data.1
        rw [boundaryMachine_nonempty P d _ _ h empty,carriedPublicAdvance_node _ _ _ _ fallback]
  exact claim _ h rfl live

end

section Parity
variable {Payload Q HQ Move I₁ I₂ O₁ O₂ : Type} {B C : Nat}
variable [Fintype HQ] [Fintype Move] [Inhabited (LeaderHandover HQ B C)]
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (rank : Q → Fin (C+1)) (q₀ : Q) (initialPayload : Payload)
variable (decode : LeaderPhaseOrigin I₁ I₂ →
  CarriedLeaderState (List (LeaderHandover HQ B C) × Payload) Q I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
variable (select : CarriedLeaderState (List (LeaderHandover HQ B C) × Payload) Q I₁ I₂ →
  LeaderPhaseOrigin I₁ I₂ → LeaderPhaseOrigin I₁ I₂ →
  (EnvHistory I₁ I₂ → Q) → (EnvHistory I₁ I₂ → Nat) → LeaderHandover HQ B C × Payload)
variable (slot : CarriedLeaderState (List (LeaderHandover HQ B C) × Payload) Q I₁ I₂ →
  EnvHistory I₁ I₂ → Fin (B+1))

def carriedHandoverCode
    (state : CarriedLeaderState (List (LeaderHandover HQ B C) × Payload) Q I₁ I₂)
    (h : EnvHistory I₁ I₂) : HandoverCode B C :=
  (slot state h,⟨state.minimum h % (C+1),Nat.mod_lt _ (by omega)⟩)

variable (offers : Move → LeaderHandover HQ B C → Bool)
variable (initialFamily : LeaderHandover HQ B C)
variable (Legal : SwitchInterface HQ B → Move → Prop) [DecidableRel Legal]
variable (tree : LabeledTree (LeaderHandover HQ B C) Move)

include closed recent in
/-- Global parity for the same composed strategy. The only local game
premise is that each actual handover is an offered predecessor edge; the
whole-phase minimum and the infinite compatible thread are constructed. -/
theorem carriedPublicGame_physical_parity
    (accepted : (supportedLeaderProgressMonitor offers
      (carriedHandoverCode slot (initialCarriedLeaderState (fun q => (rank q).val) q₀ ([],initialPayload)) [])
      initialFamily Legal).WinningTree tree)
    (edge : ∀ (h : EnvHistory I₁ I₂) (a : Nat),
      P (History.graphSequence h) → LeaderPhaseInterval P d h a → leaderBoundary P d h = true →
      let machine := carriedLeaderMachine P d step (fun q => (rank q).val) q₀ ([],initialPayload)
        decode (carriedPublicUpdate select)
      OfferedHandoverEdge offers (carriedHandoverCode slot (machine (h.take a)) (h.take a))
        (tree (machine (h.take a)).data.1)
        (carriedPublicObservation step (fun q => (rank q).val) decode select initialFamily
          (machine (h.take a)) (boundaryOrigin P (h.take a)) (boundaryOrigin P h))
        (carriedHandoverCode slot (machine h) h)) :
    ∃ read : LeaderPhaseOrigin I₁ I₂ → CarriedLeaderState (List (LeaderHandover HQ B C) × Payload) Q I₁ I₂,
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read (boundaryOrigin P h) = carriedLeaderMachine P d step (fun q => (rank q).val)
          q₀ ([],initialPayload) decode (carriedPublicUpdate select) h) ∧
      ImplementsPhaseFamily P d (fun origin => decode origin (read origin)) σ ∧
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        (carriedLeaderMachine P d step (fun q => (rank q).val) q₀ ([],initialPayload)
          decode (carriedPublicUpdate select) h).label h = strategyHistoryLabel σ step q₀ h) ∧
      ∀ (history : Nat → EnvHistory I₁ I₂)
        (_depth : ∀ n, List.length (history n) = n)
        (_prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
        (_live : ∀ n, P (History.graphSequence (history n)))
        (cuts : Nat → Nat), LeaderPhaseCuts P d history cuts →
        NatSeqMinEvenParity (fun n => (rank (strategyHistoryLabel σ step q₀ (history (n+1)))).val) := by
  obtain ⟨read,σ,reads,impl,labels,minima⟩ := carriedLeaderMachine_realization P d step (fun q => (rank q).val)
    q₀ ([],initialPayload) decode (carriedPublicUpdate select) closed recent
  let machine := carriedLeaderMachine P d step (fun q => (rank q).val) q₀ ([],initialPayload)
    decode (carriedPublicUpdate select)
  let observe := fun (_ : List (LeaderHandover HQ B C)) old target =>
    carriedPublicObservation step (fun q => (rank q).val) decode select initialFamily (read old) old target
  let code := fun h => carriedHandoverCode slot (machine h) h
  let score := fun h => (rank (strategyHistoryLabel σ step q₀ h)).val
  have nodes := carriedPublicHistory_exact step (fun q => (rank q).val) decode select P d q₀ initialPayload
    closed initialFamily read reads
  have initialCode : code [] = carriedHandoverCode slot
      (initialCarriedLeaderState (fun q => (rank q).val) q₀ ([],initialPayload)) [] := by
    dsimp only [code,machine,carriedLeaderMachine]
    rw [boundaryMachine_empty]
  have edges : ∀ (h : EnvHistory I₁ I₂) (a : Nat), P (History.graphSequence h) →
      LeaderPhaseInterval P d h a → leaderBoundary P d h = true →
      OfferedHandoverEdge offers (code (h.take a)) (tree (publicHandoverHistory P d observe (h.take a)))
        (observe (publicHandoverHistory P d observe (h.take a))
          (boundaryOrigin P (h.take a)) (boundaryOrigin P h)) (code h) := by
    intro h a live phase boundary
    have liveRoot := live_history_take P closed h live a
    rw [nodes _ liveRoot]
    dsimp only [observe]
    rw [reads _ liveRoot]
    exact edge h a live phase boundary
  have minimum : ∀ (h : EnvHistory I₁ I₂) (a : Nat), P (History.graphSequence h) →
      LeaderPhaseInterval P d h a → leaderBoundary P d h = true →
      (code h).2.val = historyPhaseMinimum score a (List.length h) h := by
    intro h a live phase _
    have exactMin := minima h live (by have := phase.start_lt; omega)
    rw [previousLeaderBoundary_eq P d h a phase] at exactMin
    change (machine h).minimum h % (C+1) = _
    rw [exactMin]
    apply Nat.mod_eq_of_lt
    have small := rangeMin_le (fun i => score (h.take (a+i+1))) 0 (List.length h-a-1) 0 (by omega)
    exact lt_of_le_of_lt small (rank _).isLt
  refine ⟨read,σ,reads,impl,labels,?_⟩
  intro history depth prefixes live cuts phases
  exact publicGame_physical_parity P d observe offers _ initialFamily Legal tree accepted code initialCode
    score edges minimum history depth prefixes live cuts phases

end Parity
end Characterisation
