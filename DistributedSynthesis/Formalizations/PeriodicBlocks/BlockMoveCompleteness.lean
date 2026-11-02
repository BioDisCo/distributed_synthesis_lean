/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockCompression

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxSynthPendingDepth 16

def strategyBoundary {I₁ I₂ O₁ O₂ G Q : Type} {B : Nat}
    (M : Recognizer Graph G) (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : BlockSlots B → EnvHistory I₁ I₂) : BlockBoundary G Q B :=
  ⟨extractInputShape past, fun i => M.eval (History.graphSequence (past i)),
    fun i => strategyHistoryLabel σ step q₀ (past i)⟩

def ResponseProgress {I₁ I₂ O₁ O₂ Q : Type} {Rank : Type*} [LE Rank] {B D : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (rank : EnvHistory I₁ I₂ → Rank)
    (past : BlockSlots B → EnvHistory I₁ I₂) (mask : ComponentMask I₁ I₂ B D)
    (response : BlockResponse I₁ I₂ B D) : Prop :=
  ∀ e, mask e = true → ∃ i,
    response.keep (response.fold e) = wordScenario i (scenarioWord D e) ∧
    rank (past i) ≤ rank (past (closingLayerRoot D e)) ∧
    ∀ u : EnvHistory I₁ I₂, List.length u ≤ D →
      strategyHistoryLabel σ step q₀ (past i++u) =
        strategyHistoryLabel σ step q₀ (past (closingLayerRoot D e)++u)

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {Rank : Type*} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Inhabited I₁] [Inhabited I₂]
variable [Finite O₁] [Finite O₂] [Finite G] [Finite Q]
variable [LinearOrder Rank] [WellFoundedLT Rank]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (P : List Graph → Prop) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (commonRoots : CommonBlockRoots (I₁:=I₁) (I₂:=I₂) P D)
variable (bound : compressionBound I₁ I₂ O₁ O₂ G Q D ≤ B+1)
variable (σ : StrategyPair I₁ I₂ O₁ O₂) (rank : EnvHistory I₁ I₂ → Rank)

include recognizes commonRoots bound in
theorem strategy_move_exists (past : BlockSlots B → EnvHistory I₁ I₂) :
    ∃ move : BlockMove I₁ I₂ O₁ O₂ G Q B D,
      move.source = strategyBoundary M step q₀ σ past ∧
      (∀ t s, move.policy t s =
        (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
         σ.two (currentView .two (closingLayerHistory past (t.val+1) s)))) ∧
      BlockMoveValid M step move.source move ∧
      ∀ mask, (∃ e, blockEndLive M move e = true ∧ mask = blockComponent M move e) →
        ResponseProgress step q₀ σ rank past mask (move.response mask) := by
  classical
  letI : Nonempty O₁ := ⟨σ.one (.empty .one)⟩
  letI : Nonempty O₂ := ⟨σ.two (.empty .two)⟩
  let dummyWord : BlockInput I₁ I₂ D :=
    ⟨List.replicate D (envRecordEquiv I₁ I₂ (default,default,.right)), List.length_replicate⟩
  let dummy : BlockResponse I₁ I₂ B D := ⟨fun _ => wordScenario 0 dummyWord, fun _ => 0⟩
  let base : BlockMove I₁ I₂ O₁ O₂ G Q B D := {
    source := strategyBoundary M step q₀ σ past
    policy := fun t s => (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
      σ.two (currentView .two (closingLayerHistory past (t.val+1) s)))
    response := fun _ => dummy }
  have responses : ∀ mask, ∃ response : BlockResponse I₁ I₂ B D,
      (∃ e, blockEndLive M base e = true ∧ mask = blockComponent M base e) →
        ResponseChecks M step base mask response ∧ ResponseProgress step q₀ σ rank past mask response := by
    intro mask
    by_cases possible : ∃ e, blockEndLive M base e = true ∧ mask = blockComponent M base e
    · obtain ⟨anchor,live,rfl⟩ := possible
      obtain ⟨leader,common⟩ := component_common_roots M P recognizes commonRoots base past
        (extractInputShape_exact past) (fun _ => rfl) anchor live
      obtain ⟨response,valid,folded⟩ := block_response_exists M step q₀ σ base past
        (extractInputShape_exact past) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
        bound anchor live (rank ∘ past) leader common
      refine ⟨response,fun _ => ⟨valid,?_⟩⟩
      intro e inside
      let key := strategyBlockType σ D past base.source.graph
        (fun i => strategyHistoryLabel σ step q₀ (past i)) (componentSuffixes M base anchor)
      let i := representative key (rank ∘ past) (closingLayerRoot D e)
      refine ⟨i,folded e inside,representative_rank key (rank ∘ past) _,?_⟩
      intro u within
      have same := representative_key key (rank ∘ past) (closingLayerRoot D e)
      exact strategy_block_replay σ step q₀ D _ _
        (congrArg BlockType.objectiveState same) (congrArg BlockType.rule same) u within
    · exact ⟨dummy,fun h => False.elim (possible h)⟩
  choose response checks using responses
  let move : BlockMove I₁ I₂ O₁ O₂ G Q B D := ⟨base.source,base.policy,response⟩
  refine ⟨move,rfl,fun _ _ => rfl,?_,?_⟩
  · refine ⟨rfl,?_,fun e live => (checks _ ⟨e,live,rfl⟩).1⟩
    intro t
    apply (shapeCoherent_iff_local _ _
      (closingLayerShape_exact past base.source.shape (extractInputShape_exact past) (t.val+1)) _).mpr
    exact ⟨σ,fun _ => ⟨rfl,rfl⟩⟩
  · intro mask possible
    exact (checks mask possible).2

end
end
end Characterisation.PeriodicBlocks
