/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBoundarysteparena
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeGlobalClock
import DistributedSynthesis.Formalizations.Theorem.ThmSummaryEpochCertificate
import DistributedSynthesis.Formalizations.Theorem.ThmGlobalJournalChecker
import DistributedSynthesis.Formalizations.Theorem.ThmGlobalChainChecker

/-!
# The reversal-forgiving objective and the fragment readback upgrade

The no-direct-reversal fragment as an objective transformation: the
reversal-forgiving companion of a deterministic parity objective
accepts every word whose graph sequence contains a direct reversal and
behaves as the original objective otherwise.  Synthesis against the
companion over all environments is therefore exactly synthesis against
the original objective over the no-direct fragment.

The payoff is that the fragment readback upgrade of
`ThmTauTreeGlobalClock.lean` becomes the *full* readback upgrade of
the companion: the journal readback wins the companion on the fragment
by the fragment upgrade, and off the fragment the companion accepts
everything.  This discharges `LocalSummaryAutomaton.ReadbackUpgrade`
for the companion unconditionally, so the summary epoch certificate
and with it the finite-game decidability chain close end to end for
the fragment synthesis problem.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- A direct reversal inside a word: two consecutive one-sided rounds
of opposite orientations. -/
def HasDirectReversalWord
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Prop :=
  ∃ n : Nat,
    ((word n).graph = Graph.left ∧ (word (n + 1)).graph = Graph.right) ∨
      ((word n).graph = Graph.right ∧ (word (n + 1)).graph = Graph.left)

/-- The graph of an executed round is the environment's graph. -/
theorem execution_graph
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (execution σ env n).graph = (env n).graph := by
  rw [execution_apply]
  rfl

/-- Leaving the no-direct fragment is having a direct reversal in the
executed word. -/
theorem hasDirectReversalWord_execution_iff
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    HasDirectReversalWord (execution σ env) ↔
      ¬ NoDirectReversalSequence env := by
  constructor
  · rintro ⟨n, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ hno
    · rw [execution_graph] at h1 h2
      exact (hno n).1 h1 h2
    · rw [execution_graph] at h1 h2
      exact (hno n).2 h1 h2
  · intro hno
    by_contra hrev
    apply hno
    intro n
    constructor
    · intro h1 h2
      exact hrev ⟨n, Or.inl ⟨by rw [execution_graph]; exact h1,
        by rw [execution_graph]; exact h2⟩⟩
    · intro h1 h2
      exact hrev ⟨n, Or.inr ⟨by rw [execution_graph]; exact h1,
        by rw [execution_graph]; exact h2⟩⟩

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Whether a round's graph directly reverses the previous one. -/
def reversalKill : Option Graph -> Graph -> Bool
  | some Graph.left, Graph.right => true
  | some Graph.right, Graph.left => true
  | _, _ => false

/--
The reversal-forgiving companion: run the objective while tracking the
previous round's graph; on a direct reversal, fall into an accepting
sink of priority zero.  Words with a direct reversal are accepted
outright; on the no-direct fragment the companion is the objective.
-/
def reversalForgiving :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) where
  State := (A.State × ULift.{s} (Option Graph)) ⊕ PUnit.{s + 1}
  stateFinite := by infer_instance
  initial := Sum.inl (A.initial, ⟨none⟩)
  step := fun state r =>
    match state with
    | Sum.inl (q, last) =>
        if reversalKill last.down r.graph then Sum.inr PUnit.unit
        else Sum.inl (A.step q r, ⟨some r.graph⟩)
    | Sum.inr _ => Sum.inr PUnit.unit
  priority := fun state =>
    match state with
    | Sum.inl (q, _) => A.priority q
    | Sum.inr _ => 0

/-- The graph recorded before round `n`. -/
def lastGraph (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    Nat -> Option Graph
  | 0 => none
  | n + 1 => some (word n).graph

/-- On the no-direct fragment the companion's run mirrors the
objective's run with the recorded previous graph. -/
theorem reversalForgiving_run_of_noReversal
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hno : ¬ HasDirectReversalWord word) :
    ∀ n : Nat,
      (A.reversalForgiving).run word n =
        Sum.inl (A.run word n, ⟨lastGraph word n⟩) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (A.reversalForgiving).step ((A.reversalForgiving).run word n)
            (word n) =
          _
      rw [ih]
      show
        (if reversalKill (lastGraph word n) (word n).graph then
            (Sum.inr PUnit.unit : (A.reversalForgiving).State)
          else Sum.inl (A.step (A.run word n) (word n),
            (⟨some (word n).graph⟩ : ULift.{s} (Option Graph)))) =
          Sum.inl (A.step (A.run word n) (word n),
            (⟨some (word n).graph⟩ : ULift.{s} (Option Graph)))
      rw [if_neg]
      intro hkill
      rcases n with - | m
      · exact absurd hkill (by
          show reversalKill none (word 0).graph = true -> False
          rcases (word 0).graph <;> decide)
      · apply hno
        refine ⟨m, ?_⟩
        revert hkill
        show reversalKill (some (word m).graph) (word (m + 1)).graph =
          true -> _
        rcases h1 : (word m).graph <;>
          rcases h2 : (word (m + 1)).graph <;>
          intro hkill <;>
          first
            | exact absurd hkill (by decide)
            | exact Or.inl ⟨rfl, rfl⟩
            | exact Or.inr ⟨rfl, rfl⟩

/-- On the no-direct fragment the companion accepts exactly when the
objective does. -/
theorem reversalForgiving_accepts_iff_of_noReversal
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hno : ¬ HasDirectReversalWord word) :
    (A.reversalForgiving).Accepts word ↔ A.Accepts word := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity,
    DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  have hfun :
      (fun n =>
          (A.reversalForgiving).priority
            ((A.reversalForgiving).run word n)) =
        fun n => A.priority (A.run word n) := by
    funext n
    rw [reversalForgiving_run_of_noReversal A word hno n]
    rfl
  rw [hfun]

/-- The sink is absorbing. -/
theorem reversalForgiving_sink_absorbing
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    {n : Nat}
    (hsink : (A.reversalForgiving).run word n = Sum.inr PUnit.unit) :
    ∀ m : Nat, n ≤ m ->
      (A.reversalForgiving).run word m = Sum.inr PUnit.unit := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  clear hm
  induction k with
  | zero => exact hsink
  | succ k ih =>
      show
        (A.reversalForgiving).step
            ((A.reversalForgiving).run word (n + k)) (word (n + k)) =
          _
      rw [ih]
      rfl

/-- A direct reversal makes the companion accept outright. -/
theorem reversalForgiving_accepts_of_reversal
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hrev : HasDirectReversalWord word) :
    (A.reversalForgiving).Accepts word := by
  obtain ⟨n, hcase⟩ := hrev
  -- the run is in the sink from round `n + 2` on
  have hsink : (A.reversalForgiving).run word (n + 2) = Sum.inr PUnit.unit := by
    rcases hshape :
        (A.reversalForgiving).run word (n + 1) with ⟨q, last⟩ | u
    · -- the previous graph is recorded, so the kill fires
      have hlast : last = ⟨some (word n).graph⟩ := by
        have hstep :
            (A.reversalForgiving).run word (n + 1) =
              (A.reversalForgiving).step
                ((A.reversalForgiving).run word n) (word n) := rfl
        rcases hprev :
            (A.reversalForgiving).run word n with ⟨q', last'⟩ | u'
        · rw [hstep, hprev] at hshape
          by_cases hkill : reversalKill last'.down (word n).graph = true
          · exact absurd hshape (by
              show
                (if reversalKill last'.down (word n).graph then
                    (Sum.inr PUnit.unit :
                      (A.reversalForgiving).State)
                  else Sum.inl (A.step q' (word n), ⟨some (word n).graph⟩)) ≠
                  Sum.inl (q, last)
              rw [if_pos hkill]
              simp)
          · have := hshape
            rw [show
                (A.reversalForgiving).step (Sum.inl (q', last')) (word n) =
                  (if reversalKill last'.down (word n).graph then
                      Sum.inr PUnit.unit
                    else Sum.inl (A.step q' (word n),
                      ⟨some (word n).graph⟩)) from rfl,
              if_neg hkill] at this
            exact (congrArg Prod.snd (Sum.inl.inj this)).symm
        · rw [hstep, hprev] at hshape
          exact absurd hshape (by simp [reversalForgiving])
      show
        (A.reversalForgiving).step
            ((A.reversalForgiving).run word (n + 1)) (word (n + 1)) =
          _
      rw [hshape, hlast]
      show
        (if reversalKill (some (word n).graph) (word (n + 1)).graph then
            (Sum.inr PUnit.unit : (A.reversalForgiving).State)
          else Sum.inl (A.step q (word (n + 1)),
            ⟨some (word (n + 1)).graph⟩)) =
          Sum.inr PUnit.unit
      rw [if_pos]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl
    · -- already in the sink
      show
        (A.reversalForgiving).step
            ((A.reversalForgiving).run word (n + 1)) (word (n + 1)) =
          _
      rw [hshape]
      rfl
  -- priority zero recurs, and zero is a lower bound for everything
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  refine ⟨0, ⟨0, rfl⟩, ?_, fun q _ => Nat.zero_le q⟩
  intro m
  refine ⟨max m (n + 2), le_max_left _ _, ?_⟩
  show
    (A.reversalForgiving).priority
        ((A.reversalForgiving).run word (max m (n + 2))) = 0
  rw [reversalForgiving_sink_absorbing A word hsink (max m (n + 2))
    (le_max_right _ _)]
  rfl

/--
Synthesis against the companion over all environments is synthesis
against the objective over the no-direct fragment.
-/
theorem reversalForgiving_realizable_iff :
    (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          (A.reversalForgiving).Accepts (execution σ env)) ↔
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          NoDirectReversalSequence env ->
            A.Accepts (execution σ env) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, fun env hnd => ?_⟩
    have hno : ¬ HasDirectReversalWord (execution σ env) := by
      rw [hasDirectReversalWord_execution_iff]
      exact fun h => h hnd
    exact
      (reversalForgiving_accepts_iff_of_noReversal A _ hno).mp (hσ env)
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, fun env => ?_⟩
    by_cases hrev : HasDirectReversalWord (execution σ env)
    · exact reversalForgiving_accepts_of_reversal A _ hrev
    · refine
        (reversalForgiving_accepts_iff_of_noReversal A _ hrev).mpr
          (hσ env ?_)
      by_contra hnd
      exact hrev ((hasDirectReversalWord_execution_iff σ env).mpr hnd)

/-- The same equivalence for a fixed strategy. -/
theorem reversalForgiving_wins_iff
    (σ : StrategyPair In₁ In₂ Out₁ Out₂) :
    (∀ env : EnvironmentSequence In₁ In₂,
        (A.reversalForgiving).Accepts (execution σ env)) ↔
      ∀ env : EnvironmentSequence In₁ In₂,
        NoDirectReversalSequence env -> A.Accepts (execution σ env) := by
  constructor
  · intro hσ env hnd
    have hno : ¬ HasDirectReversalWord (execution σ env) := by
      rw [hasDirectReversalWord_execution_iff]
      exact fun h => h hnd
    exact
      (reversalForgiving_accepts_iff_of_noReversal A _ hno).mp (hσ env)
  · intro hσ env
    by_cases hrev : HasDirectReversalWord (execution σ env)
    · exact reversalForgiving_accepts_of_reversal A _ hrev
    · refine
        (reversalForgiving_accepts_iff_of_noReversal A _ hrev).mpr
          (hσ env ?_)
      by_contra hnd
      exact hrev ((hasDirectReversalWord_execution_iff σ env).mpr hnd)


/-! ### The readback upgrade of the companion -/

section Upgrade

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

instance : DecidableEq (A.reversalForgiving).State := by
  show DecidableEq ((A.State × ULift.{s} (Option Graph)) ⊕ PUnit.{s + 1})
  infer_instance

/-- Whether the companion is realizable over all environments. -/
def ReversalForgivingRealizable : Prop :=
  ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    ∀ env : EnvironmentSequence In₁ In₂,
      (A.reversalForgiving).Accepts (execution σ env)

open Classical in
/--
The summary automaton of the companion's journal readback: the journal
summaries of a chosen fragment witness when the companion is
realizable, and of the default plan family otherwise.
-/
noncomputable def reversalForgivingSummaries :
    LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂ :=
  if h : ReversalForgivingRealizable (In₁ := In₁) A then
    let w :=
      (journal_fragment_readback_upgrade
        (leftThreadCheckerInstance (A.reversalForgiving))
        (rightThreadCheckerInstance (A.reversalForgiving))
        (chainThreadCheckerInstance (A := A.reversalForgiving)) h).some
    letI := w.controlFintype
    letI := w.controlDecEq
    letI := w.controlInhabited
    journalSummaries (In₁ := In₁) w.plans
  else
    journalSummaries (In₁ := In₁)
      (fun _ =>
        (default :
          BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) (A.reversalForgiving)
            (ULift.{max u v x y, s} PUnit.{s + 1})
            (ULift.{max u v x y, s} PUnit.{s + 1})
            (ULift.{max u v x y, s} PUnit.{s + 1})))

open Classical in
/--
The readback upgrade of the reversal-forgiving companion,
unconditionally: realizability of the companion is realizability of
the objective on the no-direct fragment, the fragment readback upgrade
supplies a witness winning on the fragment, and the companion accepts
everything off the fragment.
-/
theorem reversalForgiving_readbackUpgrade :
    LocalSummaryAutomaton.ReadbackUpgrade
      (reversalForgivingSummaries (In₁ := In₁) A)
      (A.reversalForgiving) := by
  intro σ hσ
  have h : ReversalForgivingRealizable (In₁ := In₁) A := ⟨σ, hσ⟩
  unfold reversalForgivingSummaries
  rw [dif_pos h]
  refine ⟨Prod.fst, Prod.fst, ?_⟩
  intro env
  set w :=
    (journal_fragment_readback_upgrade
      (leftThreadCheckerInstance (A.reversalForgiving))
      (rightThreadCheckerInstance (A.reversalForgiving))
      (chainThreadCheckerInstance (A := A.reversalForgiving)) h).some
    with hwdef
  letI := w.controlFintype
  letI := w.controlDecEq
  letI := w.controlInhabited
  show
    (A.reversalForgiving).Accepts
      (execution (journalStrategy w.plans) env)
  by_cases hrev :
      HasDirectReversalWord (execution (journalStrategy w.plans) env)
  · exact
      reversalForgiving_accepts_of_reversal A _ hrev
  · refine w.accepts env ?_
    by_contra hnd
    exact
      hrev
        ((hasDirectReversalWord_execution_iff _ env).mpr hnd)

/-! ### The full-model readback upgrade (entry-indexed route)

The objective automaton `A` itself, no reversal-forgiving companion: given the
entry-indexed measurability certificate for the boundary-game plan families, the
full journal readback realizes on *every* environment.  This is the clean
`{←,→,↔}` route, bypassing the fragment's sink-acceptance trick. -/

/-- Whether the objective is realizable over all environments (direct reversals
included). -/
def FullRealizable : Prop :=
  ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)

/-- The certificate hypothesis of the full-model route (paper `prop:starcomplete`,
honest existential form): whenever the boundary game is won, it has a
**θ̄-measurable** positional winner -- one whose committed blind tables are
`b_old`-invariant (`ReversalMeasurable`).  This is the folding of a realizing
strategy onto its θ̄-representative followed by re-positionalization.  It replaces
the blanket `∀ τ, ReversalMeasurable (plansOf τ)`, which the paper's
state-tailoring `τ` refutes; the existential is true at paper rigor and
non-vacuous (we consume a measurable winner, not an arbitrary strategy). -/
abbrev EntryIndexedCertificate : Prop :=
  ∀ (C : Type s) [Fintype C] [DecidableEq C] [Inhabited C]
    (τ :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} C)
          (ULift.{max u v x y, s} C)
          (ULift.{max u v x y, s} C)).PositionalStrategy
        ParityPlayer.even),
    CountableParityGame.PositionalStrategy.WinningFrom
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} C)
            (ULift.{max u v x y, s} C)
            (ULift.{max u v x y, s} C))
        τ (Sum.inl (A.initial, A.initial)) ->
      ∃ τ' :
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} C)
              (ULift.{max u v x y, s} C)
              (ULift.{max u v x y, s} C)).PositionalStrategy
            ParityPlayer.even,
        CountableParityGame.PositionalStrategy.WinningFrom
            (G :=
              DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} C)
                (ULift.{max u v x y, s} C)
                (ULift.{max u v x y, s} C))
            τ' (Sum.inl (A.initial, A.initial)) ∧
          ReversalMeasurable (plansOf τ')

/-- The entry-indexed certificate's existential body, reduced to a **measurable,
winning-preserving fold** on plan families.  Given a fold that is
`ReversalMeasurable` by construction (`hmeas` -- met by the θ̄-folds, e.g.
`globalFold_reversalMeasurable`) and keeps the boundary game won (`hwin` -- the
sole research residual, paper `prop:starcomplete`), a winning `τ` yields a
θ̄-measurable winner: fold `plansOf τ`, then realize it as a strategy via
`committingStrategy`.  The measurability half is discharged here through
`plansOf_committingStrategy`; only winning-preservation of the fold remains open.
This is the machine-checked reduction of `EntryIndexedCertificate` to the single
research obligation.

The fold is **control-changing**: every realizing fold on plan families
(`foldChain`, `globalFold`, `foldθ`) re-synthesizes the chain and so changes the
chain-control type from `C_V` to `C_L ⊕ C_R` -- an endo-typed fold would force the
chain's blind slot to equal `τ`'s original chain, which is exactly the
cross-boundary agreement one is trying to *install*.  Hence the folded winner `τ'`
lives over the fold's target control `(C_L', C_R', C_V')`, not the source
`(C_L, C_R, C_V)`; both are finite. -/
theorem reversalMeasurable_winner_of_fold
    {C_L C_R C_V C_L' C_R' C_V' : Type max u v x y s}
    [Fintype C_L] [DecidableEq C_L] [Inhabited C_L]
    [Fintype C_R] [DecidableEq C_R] [Inhabited C_R]
    [Fintype C_V] [DecidableEq C_V] [Inhabited C_V]
    [Fintype C_L'] [DecidableEq C_L'] [Inhabited C_L']
    [Fintype C_R'] [DecidableEq C_R'] [Inhabited C_R']
    [Fintype C_V'] [DecidableEq C_V'] [Inhabited C_V']
    (fold :
      PlanFamily (In₁ := In₁) A C_L C_R C_V ->
        PlanFamily (In₁ := In₁) A C_L' C_R' C_V')
    (hmeas :
      ∀ Q : PlanFamily (In₁ := In₁) A C_L C_R C_V,
        ReversalMeasurable (fold Q))
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
          (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
          τ (Sum.inl (A.initial, A.initial)) ->
        CountableParityGame.PositionalStrategy.WinningFrom
          (G := DetParityAutomaton.boundaryGame A C_L' C_R' C_V')
          (committingStrategy (fold (plansOf τ)))
          (Sum.inl (A.initial, A.initial)))
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
        τ (Sum.inl (A.initial, A.initial))) :
    ∃ τ' :
        (DetParityAutomaton.boundaryGame A C_L' C_R' C_V').PositionalStrategy
          ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
          (G := DetParityAutomaton.boundaryGame A C_L' C_R' C_V')
          τ' (Sum.inl (A.initial, A.initial)) ∧
        ReversalMeasurable (plansOf τ') :=
  ⟨committingStrategy (fold (plansOf τ)), hwin hτ,
    by rw [plansOf_committingStrategy]; exact hmeas _⟩

/-- **The fold-winning-preservation obligation `hwin` is exactly `prop:starsound`.**  With the
converse of `accepts_arenaWord_of_winning` (`winningFrom_committingStrategy_of_accepts`) proved,
`reversalMeasurable_winner_of_fold`'s residual `hwin` reduces to a pure **arena-acceptance**
statement: if the winner `τ`'s arena word is accepted on every environment, then so is the
*folded* family's arena word.  This is `prop:starsound` -- the cross-reading / delay-1 content --
with all game-theory scaffolding discharged.  A winning `τ` yields a θ̄-measurable winner given
`hmeas` (met by `globalFold_reversalMeasurable`/the θ̄-fold) and this arena soundness. -/
theorem reversalMeasurable_winner_of_fold_of_arenaSound
    {C_L C_R C_V C_L' C_R' C_V' : Type max u v x y s}
    [Fintype C_L] [DecidableEq C_L] [Inhabited C_L]
    [Fintype C_R] [DecidableEq C_R] [Inhabited C_R]
    [Fintype C_V] [DecidableEq C_V] [Inhabited C_V]
    [Fintype C_L'] [DecidableEq C_L'] [Inhabited C_L']
    [Fintype C_R'] [DecidableEq C_R'] [Inhabited C_R']
    [Fintype C_V'] [DecidableEq C_V'] [Inhabited C_V']
    (fold :
      PlanFamily (In₁ := In₁) A C_L C_R C_V ->
        PlanFamily (In₁ := In₁) A C_L' C_R' C_V')
    (hmeas :
      ∀ Q : PlanFamily (In₁ := In₁) A C_L C_R C_V,
        ReversalMeasurable (fold Q))
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
        τ (Sum.inl (A.initial, A.initial)))
    (hsound :
      (∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (arenaWord (plansOf τ) env)) ->
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (arenaWord (fold (plansOf τ)) env)) :
    ∃ τ' :
        (DetParityAutomaton.boundaryGame A C_L' C_R' C_V').PositionalStrategy
          ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
          (G := DetParityAutomaton.boundaryGame A C_L' C_R' C_V')
          τ' (Sum.inl (A.initial, A.initial)) ∧
        ReversalMeasurable (plansOf τ') :=
  reversalMeasurable_winner_of_fold A fold hmeas τ
    (fun hwin =>
      winningFrom_committingStrategy_of_accepts (fold (plansOf τ))
        (hsound (fun env => accepts_arenaWord_of_winning τ hwin env)))
    hτ

/-- **The entry-indexed certificate discharges the Route-B summary-soundness
certificate.**  The two full-model routes -- the arena-correspondence route
(`journal_readback_accepts_of_accepts_full`, gated on `EntryIndexedCertificate`)
and the fringe-elimination route (`journal_readback_accepts_of_accepts_route_b`,
gated on `SummarySoundnessCertificate`) -- share a single research residual: a
θ̄-measurable winner.  From an `EntryIndexedCertificate` winner `τ'` (winning, with
`ReversalMeasurable (plansOf τ')`), the proved bridge
`accepts_execution_journalStrategy_of_winning_full` derives all-environment
acceptance of its journal readback, which is exactly the Route-B conclusion.  Hence
proving `EntryIndexedCertificate` -- equivalently, via
`reversalMeasurable_winner_of_fold`, the single fold-winning-preservation
obligation `hwin` (paper `prop:starcomplete`) -- makes *both* full-model synthesis endpoints
unconditional at once. -/
theorem summarySoundnessCertificate_of_entryIndexed
    (hcert : EntryIndexedCertificate (In₁ := In₁) A) :
    SummarySoundnessCertificate (In₁ := In₁) (A := A) := by
  intro C _ _ _ τ hτ
  obtain ⟨τ', hwin', hmeas⟩ := hcert C τ hτ
  exact
    ⟨τ', hwin', fun env =>
      accepts_execution_journalStrategy_of_winning_full τ' hwin' env hmeas⟩

open Classical in
/--
The summary automaton of the full-model journal readback: the journal summaries
of a full-model witness when the objective is realizable, the default plan
family otherwise.
-/
noncomputable def fullSummaries (hcert : EntryIndexedCertificate (In₁ := In₁) A) :
    LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂ :=
  if h : FullRealizable (In₁ := In₁) A then
    let w :=
      (journal_fragment_readback_upgrade_full
        (leftThreadCheckerInstance A)
        (rightThreadCheckerInstance A)
        (chainThreadCheckerInstance (A := A)) h hcert).some
    letI := w.controlFintype
    letI := w.controlDecEq
    letI := w.controlInhabited
    journalSummaries (In₁ := In₁) w.plans
  else
    journalSummaries (In₁ := In₁)
      (fun _ =>
        (default :
          BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A
            (ULift.{max u v x y, s} PUnit.{s + 1})
            (ULift.{max u v x y, s} PUnit.{s + 1})
            (ULift.{max u v x y, s} PUnit.{s + 1})))

open Classical in
/--
The full-model readback upgrade: from full realizability of the objective, the
entry-indexed certificate supplies a committed plan family whose readback is
accepted on every environment.  No `NoDirectReversalSequence`, no
reversal-forgiving companion.
-/
theorem full_readbackUpgrade (hcert : EntryIndexedCertificate (In₁ := In₁) A) :
    LocalSummaryAutomaton.ReadbackUpgrade
      (fullSummaries (In₁ := In₁) A hcert) A := by
  intro σ hσ
  have h : FullRealizable (In₁ := In₁) A := ⟨σ, hσ⟩
  unfold fullSummaries
  rw [dif_pos h]
  refine ⟨Prod.fst, Prod.fst, ?_⟩
  intro env
  set w :=
    (journal_fragment_readback_upgrade_full
      (leftThreadCheckerInstance A)
      (rightThreadCheckerInstance A)
      (chainThreadCheckerInstance (A := A)) h hcert).some
    with hwdef
  letI := w.controlFintype
  letI := w.controlDecEq
  letI := w.controlInhabited
  show A.Accepts (execution (journalStrategy w.plans) env)
  exact w.accepts env

open Classical in
/-- **Route B** summary automaton: the journal summaries of a Route-B full-model
witness (via `journal_fragment_readback_upgrade_route_b`, the fringe-elimination
route) when realizable, the default family otherwise. -/
noncomputable def fullSummaries_route_b
    (hcert : SummarySoundnessCertificate (In₁ := In₁) (A := A)) :
    LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂ :=
  if h : FullRealizable (In₁ := In₁) A then
    let w :=
      (journal_fragment_readback_upgrade_route_b
        (leftThreadCheckerInstance A)
        (rightThreadCheckerInstance A)
        (chainThreadCheckerInstance (A := A)) h hcert).some
    letI := w.controlFintype
    letI := w.controlDecEq
    letI := w.controlInhabited
    journalSummaries (In₁ := In₁) w.plans
  else
    journalSummaries (In₁ := In₁)
      (fun _ =>
        (default :
          BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A
            (ULift.{max u v x y, s} PUnit.{s + 1})
            (ULift.{max u v x y, s} PUnit.{s + 1})
            (ULift.{max u v x y, s} PUnit.{s + 1})))

open Classical in
/-- **Route B** full-model readback upgrade: from full realizability, the
summary-soundness certificate supplies a committed plan family whose readback is
accepted on every environment.  Identical to `full_readbackUpgrade` but through
the fringe-elimination route, with `SummarySoundnessCertificate` (true) in place
of the entry-indexed certificate. -/
theorem full_readbackUpgrade_route_b
    (hcert : SummarySoundnessCertificate (In₁ := In₁) (A := A)) :
    LocalSummaryAutomaton.ReadbackUpgrade
      (fullSummaries_route_b (In₁ := In₁) A hcert) A := by
  intro σ hσ
  have h : FullRealizable (In₁ := In₁) A := ⟨σ, hσ⟩
  unfold fullSummaries_route_b
  rw [dif_pos h]
  refine ⟨Prod.fst, Prod.fst, ?_⟩
  intro env
  set w :=
    (journal_fragment_readback_upgrade_route_b
      (leftThreadCheckerInstance A)
      (rightThreadCheckerInstance A)
      (chainThreadCheckerInstance (A := A)) h hcert).some
    with hwdef
  letI := w.controlFintype
  letI := w.controlDecEq
  letI := w.controlInhabited
  show A.Accepts (execution (journalStrategy w.plans) env)
  exact w.accepts env

end Upgrade

/-! ### The fragment decidability endpoint -/

section Endpoint

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

/--
Decidability of distributed synthesis over the no-direct-reversal
fragment, for deterministic parity objectives.

The chain is: the reversal-forgiving companion turns the fragment
synthesis problem into full synthesis against a parity objective; the
fragment readback upgrade discharges the companion's
`ReadbackUpgrade` unconditionally; the summary epoch certificate and
the rotating-rational-run backend compile the companion to a finite
dynamic-hierarchy parity game; `thm:dynhiersynth` decides it.  The
input-free tree-automaton target family is the same backend datum as
in the unrestricted endpoints.
-/
noncomputable def dpa_noDirect_fragment_synthesis_decidable
    (A :
      DetParityAutomaton.{max u v x y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State]
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          NoDirectReversalSequence env -> A.Accepts (execution σ env)) :=
  let compilation :=
    (RoundAwareLambdaRotatingRationalRunEpochBackendCertificate.ofEpochCertificate
        (A.reversalForgiving) Branch Label target targetNonempty
        (summaryEpochCertificate (A.reversalForgiving)
          (reversalForgivingSummaries (In₁ := In₁) A)
          (reversalForgiving_readbackUpgrade
            (In₁ := In₁) A))).toDPAToFiniteGameCompilation
  letI : Decidable compilation.finiteGame.realizable :=
    Classical.choice
      (dynamic_hierarchy_synthesis_bridge compilation.finiteGame).2.2
  decidable_of_iff compilation.finiteGame.realizable
    (compilation.realizabilityEquivalent.trans
      (reversalForgiving_realizable_iff (In₁ := In₁) A))

/--
Decidability of distributed synthesis over the **full** `{←,→,↔}` model, for
deterministic parity objectives, given the entry-indexed measurability
certificate `hcert`.

Unlike the fragment endpoint there is no reversal-forgiving companion: the
objective automaton `A` is compiled directly, its full readback upgrade
(`full_readbackUpgrade`, conditional on `hcert`) discharges the summary epoch
certificate, and the rotating-rational-run backend compiles `A` to a finite
dynamic-hierarchy parity game decided by `thm:dynhiersynth`.  The conclusion
quantifies over *all* environments — direct reversals included.
-/
noncomputable def dpa_full_synthesis_decidable
    (A :
      DetParityAutomaton.{max u v x y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State]
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    (hcert : EntryIndexedCertificate (In₁ := In₁) A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  let compilation :=
    (RoundAwareLambdaRotatingRationalRunEpochBackendCertificate.ofEpochCertificate
        A Branch Label target targetNonempty
        (summaryEpochCertificate A
          (fullSummaries (In₁ := In₁) A hcert)
          (full_readbackUpgrade (In₁ := In₁) A hcert))).toDPAToFiniteGameCompilation
  letI : Decidable compilation.finiteGame.realizable :=
    Classical.choice
      (dynamic_hierarchy_synthesis_bridge compilation.finiteGame).2.2
  decidable_of_iff compilation.finiteGame.realizable
    compilation.realizabilityEquivalent

/--
**Route B** decidability of full `{←,→,↔}` distributed synthesis: identical to
`dpa_full_synthesis_decidable`, but conditional on the summary-soundness
certificate `SummarySoundnessCertificate` (true by fringe elimination,
`lem:fringe`) in place of the entry-indexed certificate.  The readback upgrade is
`full_readbackUpgrade_route_b`; the rest of the epoch → finite game →
`thm:dynhiersynth` pipeline is shared verbatim.
-/
noncomputable def dpa_full_synthesis_decidable_route_b
    (A :
      DetParityAutomaton.{max u v x y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State]
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    (hcert : SummarySoundnessCertificate (In₁ := In₁) (A := A)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  let compilation :=
    (RoundAwareLambdaRotatingRationalRunEpochBackendCertificate.ofEpochCertificate
        A Branch Label target targetNonempty
        (summaryEpochCertificate A
          (fullSummaries_route_b (In₁ := In₁) A hcert)
          (full_readbackUpgrade_route_b (In₁ := In₁) A hcert))).toDPAToFiniteGameCompilation
  letI : Decidable compilation.finiteGame.realizable :=
    Classical.choice
      (dynamic_hierarchy_synthesis_bridge compilation.finiteGame).2.2
  decidable_of_iff compilation.finiteGame.realizable
    compilation.realizabilityEquivalent

end Endpoint

end DetParityAutomaton

end DistributedSynthesis
