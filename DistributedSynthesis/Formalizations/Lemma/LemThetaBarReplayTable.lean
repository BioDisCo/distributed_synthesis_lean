/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSameThetaInterchange

/-!
# The θ̄-indexed replay table

Assembly of the interchange bricks into the finite commitment of
`def:entrythread`/`prop:starcomplete` (`real_model/paper.tex`), at the
execution level.

**The finite coordinate.**  A receive boundary is presented as a generated
prefix `h₀` extended by one receive round with inputs `(i₁, i₂)` and graph
`left` or `both` -- the `b_old` alternative.  Its *labeled entry pair*
`thetaBarPair A σ h₀ i₁ i₂ = (θ_←, θ_↔) ∈ A.State × A.State` records the
automaton state of both variants.  This is the Lean form of the reduced
entry thread `θ̄`: finite, and -- the key soundness fact -- **a function of
the blind side's view alone** (`thetaBarPair_view_invariant`, from the
brick-1 class machinery), so indexing a blind table by it is legal.

**The replay transport.**  `thetaBar_replay_accepted`: for a realizing `σ`
and any play entry whose labeled pair agrees with a chosen representative
boundary, the word that *eternally replays* `σ` from the representative's
matching variant is accepted -- for **every** continuation environment,
unconditionally.  Chains need no separate treatment: re-reversals, closures
and whole subsequent blocks are part of the replayed continuation, and the
transport is a single application of the entry congruence.  The blind half
of the replay is `b_old`-independent before the blind side's first receive
(`thetaBarPair_blind_table_invariant`), so the blind process can start the
replay knowing only `θ̄`; the informed side selects the matching variant,
having recovered `b_old` at the reversal (`recv_view_determines_prefix_two`).

**The honest residual.**  One fringe survives at the execution level: at the
boundary round itself the informed side cannot yet distinguish a genuine
reversal (`right`, replay begins) from a bidirectional closure (`both`, no
fold), so a single-valued strategy cannot behave differently in the two
branches at that round.  This is `b_new` (`thm:onebitfringe`, informed
side), and it is exactly what the boundary game's staged closing carries as
a contingent commitment (the `closeR`/`closeL` tables and the close-resolve
stage).  Discharging it is the remaining glue between this execution-level
table and the arena-level `hsound`; it is a boundary-round matter, not an
interchange or chain matter.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- The `left` (`b_old = ←`) variant of a receive boundary. -/
def bOldVariantLeft (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h₀ : History In₁ In₂ Graph Out₁ Out₂) (i₁ : In₁) (i₂ : In₂) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, Graph.left⟩)

/-- The `both` (`b_old = ↔`) variant of a receive boundary. -/
def bOldVariantBoth (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h₀ : History In₁ In₂ Graph Out₁ Out₂) (i₁ : In₁) (i₂ : In₂) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, Graph.both⟩)

theorem strategyGenerated_bOldVariantLeft
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix σ h₀) (i₁ : In₁) (i₂ : In₂) :
    StrategyGeneratedPrefix σ (bOldVariantLeft σ h₀ i₁ i₂) :=
  hgen₀.append ⟨i₁, i₂, Graph.left⟩

theorem strategyGenerated_bOldVariantBoth
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix σ h₀) (i₁ : In₁) (i₂ : In₂) :
    StrategyGeneratedPrefix σ (bOldVariantBoth σ h₀ i₁ i₂) :=
  hgen₀.append ⟨i₁, i₂, Graph.both⟩

/-- The two `b_old` variants carry the same blind view: process `1` receives
in both, with the same payload. -/
theorem bOldPair_viewOne_eq (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h₀ : History In₁ In₂ Graph Out₁ Out₂) (i₁ : In₁) (i₂ : In₂) :
    currentView Proc.one (bOldVariantLeft σ h₀ i₁ i₂) =
      currentView Proc.one (bOldVariantBoth σ h₀ i₁ i₂) := by
  rw [bOldVariantLeft, bOldVariantBoth,
    currentView_one_append_recv _ _ (Or.inl rfl),
    currentView_one_append_recv _ _ (Or.inr rfl)]
  rfl

namespace DetParityAutomaton

variable {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

/-- The labeled entry pair `θ̄ = (θ_←, θ_↔)` of a receive boundary: the
automaton states of the two `b_old` variants.  A finite coordinate. -/
def thetaBarPair (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h₀ : History In₁ In₂ Graph Out₁ Out₂) (i₁ : In₁) (i₂ : In₂) :
    A.State × A.State :=
  (entryState (A := A) (bOldVariantLeft σ h₀ i₁ i₂),
    entryState (A := A) (bOldVariantBoth σ h₀ i₁ i₂))

/-- **`θ̄` is a function of the blind view** (`def:entrythread`): two
generated receive boundaries indistinguishable to process `1` have the same
labeled entry pair.  This is what licenses a blind table indexed by `θ̄`. -/
theorem thetaBarPair_view_invariant
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ h₀' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix σ h₀)
    (hgen₀' : StrategyGeneratedPrefix σ h₀')
    (i₁ j₁ : In₁) (i₂ j₂ : In₂) (g g' : Graph)
    (hg : g = Graph.left ∨ g = Graph.both)
    (hg' : g' = Graph.left ∨ g' = Graph.both)
    (hview :
      currentView Proc.one (History.append h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩)) =
        currentView Proc.one (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩))) :
    thetaBarPair (A := A) σ h₀' j₁ j₂ = thetaBarPair (A := A) σ h₀ i₁ i₂ := by
  obtain ⟨h₀eq, hj₁, hj₂⟩ :=
    recv_view_determines_prefix_one σ hgen₀ hgen₀' i₁ j₁ i₂ j₂ g g' hg hg' hview
  rw [h₀eq, hj₁, hj₂]

/-- The `A`-state of a receive boundary is the matching component of its own
labeled pair. -/
theorem entryState_eq_thetaBarPair_component
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h₀ : History In₁ In₂ Graph Out₁ Out₂) (i₁ : In₁) (i₂ : In₂)
    (g : Graph) (hg : g = Graph.left ∨ g = Graph.both) :
    entryState (A := A) (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩)) =
      (match g with
        | Graph.left => (thetaBarPair (A := A) σ h₀ i₁ i₂).1
        | _ => (thetaBarPair (A := A) σ h₀ i₁ i₂).2) := by
  rcases hg with rfl | rfl <;> rfl

/-- **The θ̄-indexed replay is accepted, for every environment** (the
assembly of `prop:starcomplete`'s fold at the execution level).  Fix a
representative receive boundary `(h₀*, i₁*, i₂*)` and a play boundary
`(h₀, i₁, i₂)` with the *same labeled pair* -- the only data the table is
indexed by -- and the same `b_old` value `g`.  Then the word that replays
`σ` from the representative's `g`-variant, prepended by the play's own
`g`-variant, is accepted.  The continuation environment is arbitrary:
re-reversals, closures and all subsequent blocks are part of the replayed
continuation, so chains need no separate gluing. -/
theorem thetaBar_replay_accepted
    [Inhabited In₁] [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h₀star h₀ : History In₁ In₂ Graph Out₁ Out₂}
    (hgenStar : StrategyGeneratedPrefix σ h₀star)
    (i₁star i₁ : In₁) (i₂star i₂ : In₂)
    (g : Graph) (hg : g = Graph.left ∨ g = Graph.both)
    (hpair :
      thetaBarPair (A := A) σ h₀star i₁star i₂star =
        thetaBarPair (A := A) σ h₀ i₁ i₂)
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts
      (OmegaWord.prependList
        (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩))
        (contWord σ (History.append h₀star (nextRound σ h₀star ⟨i₁star, i₂star, g⟩))
          env)) := by
  rcases hg with rfl | rfl
  · exact accepts_prependList_contWord_congr σ hwin
      (hgenStar.append ⟨i₁star, i₂star, Graph.left⟩)
      (congrArg Prod.fst hpair) env
  · exact accepts_prependList_contWord_congr σ hwin
      (hgenStar.append ⟨i₁star, i₂star, Graph.both⟩)
      (congrArg Prod.snd hpair) env

/-- **The blind half of the replay table is `b_old`-independent** before the
blind side's first receive: along an all-`right` continuation the two
variants of the representative drive identical blind outputs, so the blind
process can start the replay from `θ̄` alone, without knowing `b_old`. -/
theorem thetaBarPair_blind_table_invariant
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h₀star : History In₁ In₂ Graph Out₁ Out₂) (i₁star : In₁) (i₂star : In₂)
    (env : EnvironmentSequence In₁ In₂)
    (hright : ∀ j : Nat, (env j).graph = Graph.right) (n : Nat) :
    (contWord σ (bOldVariantLeft σ h₀star i₁star i₂star) env n).outputOne =
      (contWord σ (bOldVariantBoth σ h₀star i₁star i₂star) env n).outputOne :=
  contWord_outputOne_eq_of_viewOne_eq σ
    (bOldPair_viewOne_eq σ h₀star i₁star i₂star) env hright n

end DetParityAutomaton

end DistributedSynthesis
