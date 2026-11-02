/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEntryRestartRightCongruence
import DistributedSynthesis.Formalizations.Theorem.ThmStarSynthesis

/-!
# Fold extraction hypotheses

D. Berwanger, A. B. Mathew, M. van den Bogaard,
*Hierarchical information and the synthesis of distributed strategies*,
Acta Informatica 54(7), 2017.

`Extraction` packages the epoch-entry quotient and strategy-fold hypotheses
used by the constructions below. They are explicit assumptions, not
consequences asserted here from the citation.

The cited Theorem 17 requires an objective observable by all players.
Applying Theorem 10 requires a game with dynamically hierarchical
information. In particular, neither citation alone supplies an epoch-entry
right congruence for continuation-code sets. The lemmas below derive the
entry-restart closure certificate from that quotient hypothesis.
-/

namespace DistributedSynthesis

namespace Literature

namespace BMvdB

universe u v w x y

/--
**The finite epoch entry quotient** (Definition `def:epochcongruence`(iv)):
for every automaton instantiation and lawful raw summary, some finite
entry monitor coordinate is a right congruence for continuation-code
sets on the regular hull.  Genuinely open; NOT implied by the cited
strategy theorems (see the module docstring).
-/
def EpochFoldQuotient : Prop :=
  ∀ {Alphabet In₁ In₂ Out₁ Out₂ : Type u}
    [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂]
    [Fintype Out₁] [Fintype Out₂]
    [Fintype (BoundaryLabel Out₁ Out₂)]
    [DecidableEq (BoundaryLabel Out₁ Out₂)]
    (A : DetParityAutomaton.{u, u} Alphabet) [DecidableEq A.State]
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (S₀ : PathSummarySemigroup.{u, u} (AutomatonEdgeType A.State)),
    PathSummaryLawful S₀ ->
    ∀ (radius : Nat) (P : Proc -> AutomatonEdgeType A.State -> Prop),
      ∃ (entryMonitors : Proc ->
          DeterministicMonitorFamily.{u, u, u} (AutomatonEdgeType A.State))
        (entryIndex : (d : Proc) -> (entryMonitors d).index),
        AutomatonEntryRightCongruence A letter S₀ entryMonitors
          entryIndex radius P

end BMvdB

end Literature

/-! ### Compatibility lifts through monitor enrichment -/

/-- Base-summary window compatibility lifts through any monitor
enrichment: the enriched window determines the raw window. -/
theorem summaryWindowCompatible_enrichedBase
    {EdgeType : Type u} {Atom : Type v}
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (family : DeterministicMonitorFamily.{u, x, y} EdgeType)
    (c : Nat) {atomOf : TypedPath EdgeType -> Atom}
    (h : SummaryWindowCompatible S c atomOf) :
    SummaryWindowCompatible (enrichedBaseSemigroup S family) c atomOf := by
  intro p q hpq
  apply h
  have hsum := congrArg SummaryWindowValue.summary hpq
  have hpre := congrArg SummaryWindowValue.pref hpq
  have hsuf := congrArg SummaryWindowValue.suff hpq
  simp only [summaryWindowAbstraction] at hsum hpre hsuf
  rw [show enrichedBaseSemigroup S family =
      S.prod (monitorTransitionSemigroup family) from rfl,
    PathSummarySemigroup.pathSummaryValue_prod,
    PathSummarySemigroup.pathSummaryValue_prod] at hsum
  have hfst := congrArg Prod.fst hsum
  dsimp only at hfst
  simp only [summaryWindowAbstraction, SummaryWindowValue.mk.injEq]
  exact ⟨hfst, hpre, hsuf⟩

/-! ### The set-route consumption bridge -/

section Bridge

universe u

variable {Alphabet In₁ In₂ Out₁ Out₂ : Type u}
variable [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Fintype (BoundaryLabel Out₁ Out₂)]
variable [DecidableEq (BoundaryLabel Out₁ Out₂)]
variable (A : DetParityAutomaton.{u, u} Alphabet) [DecidableEq A.State]
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)

/--
**The set-route bridge**: the cited quotient law alone closes the
reversal-closure certificate.  Beyond the anchor, the inputs are only
the journal-atom interface data, with window compatibility required at
the raw summary `S₀` -- the lift through the chosen enrichment is
automatic.
-/
noncomputable def entryRestartClosureCertificate_of_epochFoldQuotient
    (hquot : Literature.BMvdB.EpochFoldQuotient.{u})
    (S₀ : PathSummarySemigroup.{u, u} (AutomatonEdgeType A.State))
    (hlaw : PathSummaryLawful S₀)
    (radius : Nat) (P : Proc -> AutomatonEdgeType A.State -> Prop)
    {BaseAtom Continuation : Proc -> Type u}
    (baseAtomOf : (d : Proc) ->
      TypedPath (AutomatonEdgeType A.State) -> BaseAtom d)
    (continuationOf : (d : Proc) ->
      TypedPath (AutomatonEdgeType A.State) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible S₀ radius (baseAtomOf d))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate
      (fun _ => AutomatonEdgeType A.State) BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation :=
  let hx := hquot A letter S₀ hlaw radius P
  entryRestartClosureCertificate_of_entryRightCongruence A letter S₀
    hx.choose hx.choose_spec.choose radius P hlaw
    hx.choose_spec.choose_spec
    baseAtomOf continuationOf baseSound
    (fun d =>
      summaryWindowCompatible_enrichedBase S₀
        (concreteMonitorFamily A letter hx.choose d) radius (compatible d))
    hradius

end Bridge

/-! ### The single citation anchor -/

namespace Literature

namespace BMvdB

universe u

/--
**The two open fold obligations at one discharge point.**  NOT a claim
that the cited paper supplies either (see the module docstring):
`starFold` (paper `prop:starcomplete`, alias
`Literature.Berwanger.ExtractionAtFold`) has the split-fringe +
Theorem 10 + readback pipeline as its candidate discharge, pending a
concrete `FringeDecomposition` for the full local-view model;
`epochFoldQuotient` is genuinely open and not implied by the strategy
theorems.
-/
structure Extraction : Prop where
  epochFoldQuotient : EpochFoldQuotient.{u}
  starFold :
    ∀ {In₁ In₂ Out₁ Out₂ : Type u}
      [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
      [DecidableEq In₁] [DecidableEq In₂]
      [Inhabited Out₁] [Inhabited Out₂]
      (A : DetParityAutomaton.{u, u} (RoundRecord In₁ In₂ Graph Out₁ Out₂)),
      Nonempty (DetParityAutomaton.StarFoldPackage A)

/-- Star-route projection of the anchor. -/
theorem Extraction.starFoldPackage (h : Extraction.{u})
    {In₁ In₂ Out₁ Out₂ : Type u}
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (A : DetParityAutomaton.{u, u} (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    Nonempty (DetParityAutomaton.StarFoldPackage A) :=
  h.starFold A

end BMvdB

end Literature

end DistributedSynthesis
