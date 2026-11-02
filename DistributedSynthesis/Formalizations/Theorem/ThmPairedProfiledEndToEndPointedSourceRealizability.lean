/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndSemanticFamilyMove
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalAdjacency
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilySourceSelection
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedRealization

/-!
# Pointed semantic discharge of end-to-end family-source realizability

The open-view-class construction already retains exactly the proof-side fact
needed to share a blind sender: an actual pointed history and every alternative
member of its class have the same local view.  This file connects that fact to
the fixed-policy end-to-end family interface.

The only additional premise is deliberately exposed as a named compatibility
predicate: the two *exact restarted monitors* must be won by the semantic
continuations at those two histories.  The existing open realization proves
the analogous fact for its pre-policy open-root monitors, but there is
currently no theorem identifying those monitors with the later fixed-policy
restart roots.  Thus the predicate below is the precise remaining semantic
transport law, rather than a hidden second rationalization.

All class members and orientations occur only in proofs.  Neither construction
passes a member, orientation, current graph, or strict-leader bit to the shared
sender.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## The two semantic histories represented by one pointed class -/

/-- The actual process-one history is member `false`; an alternative member
of the same finite view class is member `true`. -/
def profiledOpenRightPointedPairHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (pointed : ProfiledOpenRightPointedRealization A strategy hwin basis source)
    (alternative : {root // root ∈ source.1}) :
    Bool → History In₁ In₂ Graph Out₁ Out₂
  | false => pointed.actualEntry.leftHistory
  | true => (pointed.realization.entry alternative).leftHistory

/-- Process-two mirror. -/
def profiledOpenLeftPointedPairHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (pointed : ProfiledOpenLeftPointedRealization A strategy hwin basis source)
    (alternative : {root // root ∈ source.1}) :
    Bool → History In₁ In₂ Graph Out₁ Out₂
  | false => pointed.actualEntry.rightHistory
  | true => (pointed.realization.entry alternative).rightHistory

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The two process-one histories selected from one pointed realization have
equal local views. -/
theorem profiledOpenRightPointedPairHistory_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (pointed : ProfiledOpenRightPointedRealization A strategy hwin basis source)
    (alternative : {root // root ∈ source.1}) :
    currentView Proc.one
        (profiledOpenRightPointedPairHistory A pointed alternative false) =
      currentView Proc.one
        (profiledOpenRightPointedPairHistory A pointed alternative true) := by
  change currentView Proc.one pointed.actualEntry.leftHistory =
    currentView Proc.one (pointed.realization.entry alternative).leftHistory
  rw [← pointed.entry_selected]
  exact (pointed.realization.view_eq pointed.selected).trans
    (pointed.realization.view_eq alternative).symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left pointed-view equality. -/
theorem profiledOpenLeftPointedPairHistory_view_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (pointed : ProfiledOpenLeftPointedRealization A strategy hwin basis source)
    (alternative : {root // root ∈ source.1}) :
    currentView Proc.two
        (profiledOpenLeftPointedPairHistory A pointed alternative false) =
      currentView Proc.two
        (profiledOpenLeftPointedPairHistory A pointed alternative true) := by
  change currentView Proc.two pointed.actualEntry.rightHistory =
    currentView Proc.two (pointed.realization.entry alternative).rightHistory
  rw [← pointed.entry_selected]
  exact (pointed.realization.view_eq pointed.selected).trans
    (pointed.realization.view_eq alternative).symm

/-! ## Exact fixed-policy continuation compatibility -/

/-- A right fixed-policy restart family is pointed-semantically compatible if
its two restarted monitors are realized at an actual history and one member of
the same open process-one view class.  The view equality itself is not a
premise: it follows from the pointed realization. -/
def EndToEndRightFamilyPointedSemanticCompatible
    (source : Bool → EndToEndRightRestartRoot A package) : Prop :=
  ∃ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
      (hwin : ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution strategy env))
      (basis : ∀ state : PairedProfiledTreeState A,
        (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
      (openSource : ProfiledOpenRightViewClass A)
      (pointed : ProfiledOpenRightPointedRealization A strategy hwin basis
        openSource)
      (alternative : {root // root ∈ openSource.1})
      (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
        (ProfiledRightReceiverOutput A)),
    ∀ anchor env,
      (endToEndRightFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy
            (profiledOpenRightPointedPairHistory A pointed alternative anchor))
          env)

/-- Left fixed-policy continuation compatibility. -/
def EndToEndLeftFamilyPointedSemanticCompatible
    (source : Bool → EndToEndLeftRestartRoot A package) : Prop :=
  ∃ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
      (hwin : ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution strategy env))
      (basis : ∀ state : PairedProfiledTreeState A,
        (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
      (openSource : ProfiledOpenLeftViewClass A)
      (pointed : ProfiledOpenLeftPointedRealization A strategy hwin basis
        openSource)
      (alternative : {root // root ∈ openSource.1})
      (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
        (ProfiledLeftReceiverOutput A)),
    ∀ anchor env,
      (endToEndLeftFamilyRootMonitors A package source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy
            (profiledOpenLeftPointedPairHistory A pointed alternative anchor))
          env)

/-! ## Discharge to the executable family-source interface -/

/-- Pointed semantic compatibility supplies one shared winning right-family
table. -/
theorem endToEndRightFamilySourceRealizable_of_pointedSemanticCompatible
    (source : Bool → EndToEndRightRestartRoot A package)
    (hcompatible : EndToEndRightFamilyPointedSemanticCompatible A package
      source) :
    EndToEndRightFamilySourceRealizable A package source := by
  rcases hcompatible with
    ⟨strategy, hwin, basis, openSource, pointed, alternative, receiver,
      hmonitor⟩
  let history := profiledOpenRightPointedPairHistory A pointed alternative
  have hview : currentView Proc.one (history false) =
      currentView Proc.one (history true) :=
    profiledOpenRightPointedPairHistory_view_eq A pointed alternative
  let move := endToEndRightFamilyPairMoveOfViewEq A package strategy history
    hview source receiver hmonitor
  refine ⟨move.2, ?_⟩
  exact endToEndRightFamilyPairMoveOfViewEq_wins A package strategy history
    hview source receiver hmonitor

/-- Left mirror. -/
theorem endToEndLeftFamilySourceRealizable_of_pointedSemanticCompatible
    (source : Bool → EndToEndLeftRestartRoot A package)
    (hcompatible : EndToEndLeftFamilyPointedSemanticCompatible A package
      source) :
    EndToEndLeftFamilySourceRealizable A package source := by
  rcases hcompatible with
    ⟨strategy, hwin, basis, openSource, pointed, alternative, receiver,
      hmonitor⟩
  let history := profiledOpenLeftPointedPairHistory A pointed alternative
  have hview : currentView Proc.two (history false) =
      currentView Proc.two (history true) :=
    profiledOpenLeftPointedPairHistory_view_eq A pointed alternative
  let move := endToEndLeftFamilyPairMoveOfViewEq A package strategy history
    hview source receiver hmonitor
  refine ⟨move.2, ?_⟩
  exact endToEndLeftFamilyPairMoveOfViewEq_wins A package strategy history
    hview source receiver hmonitor

/-! ## The reachable alternating pair -/

/-- The exact semantic obligation on a reachable adjacent pair.  Its source
maps are the mixed current/pending maps proved in the adjacency invariant. -/
def EndToEndBothPendingAdjacency.PointedSemanticCompatible
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) : Prop :=
  EndToEndRightFamilyPointedSemanticCompatible A package
      (adj.rightFamilySource A package) ∧
    EndToEndLeftFamilyPointedSemanticCompatible A package
      (adj.leftFamilySource A package)

/-- Once the pointed semantic transport holds, both executable family
selectors are on their winning branches. -/
theorem EndToEndBothPendingAdjacency.familySourcesRealizable_of_pointedSemanticCompatible
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (hcompatible : adj.PointedSemanticCompatible A package) :
    EndToEndRightFamilySourceRealizable A package
        (adj.rightFamilySource A package) ∧
      EndToEndLeftFamilySourceRealizable A package
        (adj.leftFamilySource A package) :=
  ⟨endToEndRightFamilySourceRealizable_of_pointedSemanticCompatible A
      package (adj.rightFamilySource A package) hcompatible.1,
    endToEndLeftFamilySourceRealizable_of_pointedSemanticCompatible A package
      (adj.leftFamilySource A package) hcompatible.2⟩

/-- The same bridge reaches the total executable selectors: under pointed
semantic compatibility, neither selector takes its arbitrary fallback. -/
theorem EndToEndBothPendingAdjacency.familyMoveSelectors_win_of_pointedSemanticCompatible
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates)
    (hcompatible : adj.PointedSemanticCompatible A package) :
    EndToEndRightFamilyRootTableWins A package
        (adj.rightFamilySource A package)
        (endToEndRightFamilyMoveSelector A package
          (adj.rightFamilySource A package)).2 ∧
      EndToEndLeftFamilyRootTableWins A package
        (adj.leftFamilySource A package)
        (endToEndLeftFamilyMoveSelector A package
          (adj.leftFamilySource A package)).2 := by
  have hrealizable :=
    adj.familySourcesRealizable_of_pointedSemanticCompatible A package
      hcompatible
  exact
    ⟨endToEndRightFamilyMoveSelector_wins A package
        (adj.rightFamilySource A package) hrealizable.1,
      endToEndLeftFamilyMoveSelector_wins A package
        (adj.leftFamilySource A package) hrealizable.2⟩

end

end DetParityAutomaton

end DistributedSynthesis
