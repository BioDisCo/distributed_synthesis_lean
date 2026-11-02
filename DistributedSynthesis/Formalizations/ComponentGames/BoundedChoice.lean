/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.BoundedReplay

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable {Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
variable (rank : EnvHistory I₁ I₂ → Rank)

def ReplacementProgress (m m' : Move I₁ I₂ O₁ O₂ Q D) : Prop :=
  ∀ (h : m'.source.Root) (a : m.source.Root) (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D),
    h.val = a.val ++ w.val → ∃ b : m.source.Root,
      (m'.replacement h).val = b.val ++ w.val ∧ rank b.val ≤ rank a.val ∧
      ∀ u : EnvHistory I₁ I₂, List.length u ≤ D →
        strategyHistoryLabel σ step q₀ (a.val ++ u) = strategyHistoryLabel σ step q₀ (b.val ++ u)

/-- Choose rank-minimal representatives of exactly the paper's previous
block key, and obtain a legal bounded move with its full next invariant. -/
theorem bounded_successor_choice
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (m : Move I₁ I₂ O₁ O₂ Q D) (faithful : Faithful M step q₀ σ m)
    (P : Position I₁ I₂ Q D) (next : Next M step m P) :
    ∃ m' : Move I₁ I₂ O₁ O₂ Q D,
      Legal M step (.bounded (compressionBound I₁ I₂ O₁ O₂ G Q D)) P m' ∧
      Faithful M step q₀ σ m' ∧ ReplacementProgress step q₀ σ rank m m' := by
  obtain ⟨phase,K,component,histories,labels⟩ := next
  let key := componentKey M m K
  let ranking (i : participatingRoots m K) := rank i.val.val
  let rep := representative key ranking
  have preserves : ∀ i, componentKey M m K (rep i) = componentKey M m K i := representative_key key ranking
  have constant : ∀ i j, componentKey M m K i = componentKey M m K j → rep i = rep j :=
    fun _ _ same => representative_eq key ranking same
  let equiv := componentEquiv m K P histories
  let r := fun h => equiv (fold M m K rep preserves (equiv.symm h))
  let m' : Move I₁ I₂ O₁ O₂ Q D := ⟨P,restrictClosingPolicy r (algorithmRule σ P),r⟩
  have localMove := bounded_representative_move M m K rep preserves step holes P component histories labels
    (algorithmRule σ P) (algorithmMove_legal M step σ P).2.1 constant
  have idem (h : P.Root) : r (r h) = r h := by
    dsimp only [r]
    rw [equiv.symm_apply_apply,fold_idempotent M m K rep preserves constant]
  have states : ∀ h : P.Root, P.state h = strategyHistoryLabel σ step q₀ h.val :=
    faithful_next_states M step q₀ σ m faithful P ⟨phase,K,component,histories,labels⟩
  refine ⟨m',⟨rfl,localMove.1,localMove.2.1,?_⟩,⟨states,rfl,idem,localMove.2.1⟩,?_⟩
  · simpa only [retained,m',compressionBound,StrategyBlockType,blockType_card_exact,blockWord_card]
      using localMove.2.2
  · intro h a w eq
    let e := equiv.symm h
    have history : m.source.history e.val = h.val := congrArg Subtype.val (equiv.apply_symm_apply h)
    have endpoint : e.val = wordScenario a w := m.source.history_injective
      (history.trans (eq.trans (wordScenario_history m.source.past a w).symm))
    have root : (rootOf m K e).val = a := by
      change closingLayerRoot D e.val = a
      rw [endpoint,wordScenario_root]
    have suffix : scenarioWord D e.val = w := by rw [endpoint,scenarioWord_wordScenario]
    refine ⟨(rep (rootOf m K e)).val,?_,?_,?_⟩
    · change m.source.history (fold M m K rep preserves e).val = _
      rw [fold_history,suffix]
    · have le := representative_rank key ranking (rootOf m K e)
      change rank (rep (rootOf m K e)).val.val ≤ rank (rootOf m K e).val.val at le
      rw [root] at le
      exact le
    · intro u within
      have replay := faithful_key_replay M step q₀ σ m faithful K component (rootOf m K e)
        (rep (rootOf m K e)) (preserves _).symm u within
      rw [root] at replay
      exact replay
end
end Characterisation.ComponentGames.HistoryGame
