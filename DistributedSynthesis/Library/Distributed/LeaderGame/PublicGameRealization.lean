/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.PublicHandoverRecursion
import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseParityComposition
import DistributedSynthesis.Library.Distributed.LeaderPhases.SupportedLeaderProgress

/-! Construct the public branch and hidden predecessor thread of an actual
execution. Only individual handovers require an offer, predecessor, and
minimum equation; no infinite branch or accepting thread is a premise. -/
namespace Characterisation
open DistributedSynthesis

section PublicHistory
variable {I₁ I₂ Outcome : Type}
variable (P : List Graph → Prop) (d : Nat)
variable (observe : List Outcome → LeaderPhaseOrigin I₁ I₂ → LeaderPhaseOrigin I₁ I₂ → Outcome)

noncomputable abbrev publicHandoverHistory (h : EnvHistory I₁ I₂) : List Outcome :=
  boundaryMachine P d [] (fun node old target => node ++ [observe node old target]) h

theorem publicHandoverHistory_boundary (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : LeaderPhaseInterval P d h a) :
    publicHandoverHistory P d observe h =
      publicHandoverHistory P d observe (h.take a) ++
        [observe (publicHandoverHistory P d observe (h.take a))
          (boundaryOrigin P (h.take a)) (boundaryOrigin P h)] := by
  have nonempty : h ≠ [] := by intro eq; have bound := phase.start_lt; simp [eq] at bound
  rw [publicHandoverHistory, boundaryMachine_nonempty _ _ _ _ h nonempty,
    previousLeaderBoundary_eq P d h a phase]

variable (history : Nat → EnvHistory I₁ I₂)
variable (depth : ∀ n, List.length (history n) = n)
variable (prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
variable (cuts : Nat → Nat) (phases : LeaderPhaseCuts P d history cuts)

noncomputable def actualHandoverBranch (n : Nat) : Outcome :=
  observe (publicHandoverHistory P d observe (history (cuts n)))
    (boundaryOrigin P (history (cuts n))) (boundaryOrigin P (history (cuts (n+1))))

include depth prefixes phases in
/-- The recursive public history agrees with every finite prefix of the
actual handover branch. The number of public steps is the number of completed
phases; the cut values retain the physical round numbers. -/
theorem publicHandoverHistory_cuts (n : Nat) :
    publicHandoverHistory P d observe (history (cuts n)) =
      branchNode (actualHandoverBranch P d observe history cuts) n := by
  induction n with
  | zero =>
    have empty : history (cuts 0) = [] := List.eq_nil_of_length_eq_zero (by rw [depth,phases.1])
    rw [empty]
    exact boundaryMachine_empty P d _ _
  | succ n ih =>
    have phase := leaderPhaseCuts_intervals history depth prefixes cuts P d phases n
    rw [depth] at phase
    have step := publicHandoverHistory_boundary P d observe (history (cuts (n+1))) (cuts n) phase
    rw [prefixes _ _ (phases.2.1.monotone (by omega))] at step
    change _ = branchNode (actualHandoverBranch P d observe history cuts) n ++ [_]
    rw [step]
    exact congrArg (fun node => node ++ [actualHandoverBranch P d observe history cuts n]) ih

end PublicHistory

section Strategy
variable {I₁ I₂ O₁ O₂ Outcome Move : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (observe : List Outcome → LeaderPhaseOrigin I₁ I₂ → LeaderPhaseOrigin I₁ I₂ → Outcome)
variable (tree : LabeledTree Outcome Move)
variable (decode : Move → LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)

include closed recent in
/-- Follow the game tree through the recursively reconstructed public
history. The two processes use one common game node despite private inputs;
every output uses its actual full view and the table of its active phase. -/
theorem publicGame_strategy :
    ∃ read : LeaderPhaseOrigin I₁ I₂ → List Outcome,
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
        read (boundaryOrigin P h) = publicHandoverHistory P d observe h) ∧
      ImplementsPhaseFamily P d (fun origin => decode (tree (read origin)) origin) σ ∧
      ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → 0 < List.length h →
        let a := previousLeaderBoundary P d h
        let controller := decode (tree (publicHandoverHistory P d observe (h.take a)))
          (boundaryOrigin P (h.take a))
        (σ.one (currentView .one h),σ.two (currentView .two h)) =
          (controller.one (currentView .one h),controller.two (currentView .two h)) :=
  boundaryMachine_strategy P d [] (fun node old target => node ++ [observe node old target])
    closed recent (fun origin node => decode (tree node) origin)

end Strategy

section Parity
variable {I₁ I₂ Q Move : Type} {B C : Nat}
variable [Fintype Q] [Fintype Move] [Inhabited (LeaderHandover Q B C)]
variable (P : List Graph → Prop) (d : Nat)
variable (observe : List (LeaderHandover Q B C) → LeaderPhaseOrigin I₁ I₂ →
  LeaderPhaseOrigin I₁ I₂ → LeaderHandover Q B C)
variable (offers : Move → LeaderHandover Q B C → Bool)
variable (initial : HandoverCode B C) (initialFamily : LeaderHandover Q B C)
variable (Legal : SwitchInterface Q B → Move → Prop) [DecidableRel Legal]
variable (tree : LabeledTree (LeaderHandover Q B C) Move)
variable (accepted : (supportedLeaderProgressMonitor offers initial initialFamily Legal).WinningTree tree)
variable (code : EnvHistory I₁ I₂ → HandoverCode B C) (initialCode : code [] = initial)
variable (score : EnvHistory I₁ I₂ → Nat)

variable (edge : ∀ (h : EnvHistory I₁ I₂) (a : Nat),
  P (History.graphSequence h) → LeaderPhaseInterval P d h a → leaderBoundary P d h = true →
  OfferedHandoverEdge offers (code (h.take a)) (tree (publicHandoverHistory P d observe (h.take a)))
    (observe (publicHandoverHistory P d observe (h.take a))
      (boundaryOrigin P (h.take a)) (boundaryOrigin P h)) (code h))
variable (minimum : ∀ (h : EnvHistory I₁ I₂) (a : Nat),
  P (History.graphSequence h) → LeaderPhaseInterval P d h a → leaderBoundary P d h = true →
    (code h).2.val = historyPhaseMinimum score a (List.length h) h)

include accepted initialCode edge minimum in
/-- Global physical parity follows from local handover equations and the
winning public game tree. The actual infinite public branch and compatible
hidden thread are constructed in the proof, not supplied as hypotheses. -/
theorem publicGame_physical_parity
    (history : Nat → EnvHistory I₁ I₂)
    (depth : ∀ n, List.length (history n) = n)
    (prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
    (live : ∀ n, P (History.graphSequence (history n)))
    (cuts : Nat → Nat) (phases : LeaderPhaseCuts P d history cuts) :
    NatSeqMinEvenParity (fun n => score (history (n+1))) := by
  let branch := actualHandoverBranch P d observe history cuts
  have publicPrefixes := publicHandoverHistory_cuts P d observe history depth prefixes cuts phases
  have empty : history (cuts 0) = [] := List.eq_nil_of_length_eq_zero (by rw [depth,phases.1])
  have intervals : ∀ n, LeaderPhaseInterval P d (history (cuts (n+1))) (cuts n) := by
    intro n
    simpa only [depth] using leaderPhaseCuts_intervals history depth prefixes cuts P d phases n
  let thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
      (observableThreadWord tree branch) := {
    code := fun n => code (history (cuts n))
    initial := by rw [empty]; exact initialCode
    edge := by
      intro n
      have result := edge (history (cuts (n+1))) (cuts n) (live _) (intervals n) (phases.2.2 n).1
      rw [prefixes _ _ (phases.2.1.monotone (by omega))] at result
      change OfferedHandoverEdge offers _ (tree (branchNode branch n)) (branch n) _
      rw [← publicPrefixes n]
      exact result }
  have parity := ((supportedLeaderProgress_winning_iff offers initial initialFamily Legal tree).mp accepted).2 branch thread
  have minima : ∀ n, (thread.code (n+1)).2.val =
      cutBlockMin (fun n => score (history (n+1))) cuts n := by
    intro n
    have exactMin := minimum (history (cuts (n+1))) (cuts n) (live _)
      (intervals n) (phases.2.2 n).1
    change (code (history (cuts (n+1)))).2.val = _
    rw [exactMin, depth]
    unfold historyPhaseMinimum cutBlockMin
    apply rangeMin_congr
    intro i bound
    have strict := phases.2.1 (show n < n+1 by omega)
    rw [prefixes _ _ (by omega)]
    simp only [Nat.zero_add]
  rw [funext minima] at parity
  exact (natSeqMinEvenParity_cutBlockMin _ phases.2.1 phases.1).mp parity

end Parity
end Characterisation
