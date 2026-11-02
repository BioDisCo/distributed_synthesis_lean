/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ComponentSteps
import DistributedSynthesis.Formalizations.ComponentTrees.Compression

/-!
# Compressing a component

Manuscript source label: `lem:tree-compression`.

## Paper statement

Choose one representative of each class.
There is a reduction $r:K'\to K'$ at $(K',q')$ such that
\begin{equation}r(eu)=e'u\qquad(eu\in E(K'))\enspace,
\end{equation}
where $e'$ is the chosen representative of~$e$.
Its image has at most $B$ edges.
If $|E(K)|\leq B$, then $|E(\liveext{K})|\leq b$.

## Reading the proof

See the [proof locations](PROOFS.md#compressing-a-component) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Compression

/-- Reuses `Characterisation.ComponentTrees.compression_reduction`. -/
theorem compression_reduction :
    ∀ {I₁ I₂ O₁ O₂ Q G : Type} {D : ℕ} [inst : Fintype I₁] [inst_1 : Fintype I₂]
      [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] (M : Recognizer Graph G)
      [inst_4 : DecidablePred fun (x : G) => x ∈ M.accept] (m : ComponentGames.HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
      (C : Finset m.source.End) {S V : Type} [Fintype S] [Nontrivial V] (label : m.source.End → S)
      (rep : ↥(ComponentGames.HistoryGame.participatingRoots m C) → ↥(ComponentGames.HistoryGame.participatingRoots m C)),
      (∀ (h : ↥(ComponentGames.HistoryGame.participatingRoots m C)),
          ComponentTrees.endpointTable m C label (rep h) = ComponentTrees.endpointTable m C label h) →
        (∀ (h k : ↥(ComponentGames.HistoryGame.participatingRoots m C)),
            ComponentTrees.endpointTable m C label h = ComponentTrees.endpointTable m C label k → rep h = rep k) →
          ∀ (A : Set (ℕ → Graph)),
            (∀ (h : List Graph), LivePrefix A h ↔ M.eval h ∈ M.accept) →
              0 < D →
                (∀ (u : List Graph),
                    LivePrefix A u →
                      ∃ (σ : StrategyPair V V (Option V) (Option V)),
                        ComponentGames.Consensus.SolvesBy σ (Residual A u) D) →
                  ComponentGames.HistoryGame.IsComponent M m C →
                    ∃ (r : ComponentTrees.Reduction (fun (e : ↥C) => m.source.history ↑e) fun (e : ↥C) => label ↑e),
                      (∀ (e : ↥C),
                          m.source.history ↑(r.map.edge e) =
                            (rep (ComponentGames.HistoryGame.rootOf m C e)).val.val ++ (PeriodicBlocks.scenarioWord D e.val).val) ∧
                        (Finset.image r.map.edge Finset.univ).card ≤
                          (1 + Nat.card S) ^ Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D *
                            Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D :=
  @_root_.Characterisation.ComponentTrees.compression_reduction

/-- Reuses `Characterisation.ComponentTrees.endpointTable_card`. -/
theorem endpointTable_card :
    ∀ {I₁ I₂ B : Type} {D : ℕ} [Fintype I₁] [Fintype I₂] [DecidableEq I₁]
      [DecidableEq I₂] [Fintype B],
      Nat.card (PeriodicBlocks.BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D → Option B) =
        (1 + Nat.card B) ^ Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D :=
  @_root_.Characterisation.ComponentTrees.endpointTable_card

/-- Reuses `Characterisation.ComponentTrees.endpointFold_image_bound`. -/
theorem endpointFold_image_bound :
    ∀ {I₁ I₂ O₁ O₂ Q B : Type} {D : ℕ} [inst : Fintype I₁] [inst_1 : Fintype I₂]
      [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] (m : ComponentGames.HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
      (K : Finset m.source.End) (label : m.source.End → B)
      (rep : ↥(ComponentGames.HistoryGame.participatingRoots m K) → ↥(ComponentGames.HistoryGame.participatingRoots m K))
      (preserves :
        ∀ (h : ↥(ComponentGames.HistoryGame.participatingRoots m K)),
          ComponentTrees.endpointTable m K label (rep h) = ComponentTrees.endpointTable m K label h),
      (∀ (h k : ↥(ComponentGames.HistoryGame.participatingRoots m K)),
          ComponentTrees.endpointTable m K label h = ComponentTrees.endpointTable m K label k → rep h = rep k) →
        ∀ [Fintype B],
          (Finset.image (ComponentTrees.endpointFold m K label rep preserves) Finset.univ).card ≤
            (1 + Nat.card B) ^ Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D *
              Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D :=
  @_root_.Characterisation.ComponentTrees.endpointFold_image_bound

/-- Reuses `Characterisation.ComponentTrees.live_endpoints_bound`. -/
theorem live_endpoints_bound :
    ∀ {I₁ I₂ O₁ O₂ Q G : Type} {D : ℕ} [inst : Fintype I₁] [inst_1 : Fintype I₂]
      [inst_2 : DecidableEq I₁] [inst_3 : DecidableEq I₂] (m : ComponentGames.HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
      (M : Recognizer Graph G) [inst_4 : DecidablePred fun (x : G) => x ∈ M.accept] (L : ℕ),
      m.source.histories.card ≤ L →
        (ComponentGames.HistoryGame.extensions M m).card ≤ L * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D :=
  @_root_.Characterisation.ComponentTrees.live_endpoints_bound

end DistributedSynthesis.Paper.Compression
