/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.BlockHistories
import DistributedSynthesis.Formalizations.ComponentTrees.Positions
import DistributedSynthesis.Formalizations.PeriodicBlocks.ObjectiveBridge

/-! Actual blocks produced by a distributed algorithm. Uses the existing
continuation policy, complete-block words, histories, and physical execution.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.HistoryGame
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {H K I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

def strategyPolicy (past : H → EnvHistory I₁ I₂) : ClosingPolicy H I₁ I₂ O₁ O₂ D :=
  fun t => strategyContinuationPolicy σ past t.val

theorem strategyPolicy_coherent [DecidableEq I₁] [DecidableEq I₂] (past : H → EnvHistory I₁ I₂) :
    ClosingPolicyCoherent (extractInputShape past) (strategyPolicy σ past (D:=D)) :=
  fun t => strategyContinuationPolicy_coherent σ past _ (extractInputShape_exact past) t.val

theorem strategyPolicy_restrict (past : K → EnvHistory I₁ I₂) (f : H → K) :
    restrictClosingPolicy f (strategyPolicy σ past (D:=D)) = strategyPolicy σ (past ∘ f) := by
  funext t s
  simp only [restrictClosingPolicy, strategyPolicy, strategyContinuationPolicy,
    closingLayerHistory_map]

def strategyBlock (h : EnvHistory I₁ I₂) (u : BlockInput I₁ I₂ D) :
    BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D :=
  ruleBlock (strategyPolicy σ (fun _ : Unit => h)) (wordScenario () u)

theorem strategyBlock_at (past : H → EnvHistory I₁ I₂) (h : H) (u : BlockInput I₁ I₂ D) :
    ruleBlock (strategyPolicy σ past) (wordScenario h u) = strategyBlock σ (past h) u := by
  let f : Unit → H := fun _ => h
  have mapped : mapClosingLayer f D (wordScenario () u) = wordScenario h u := by
    rw [← wordScenario_scenarioWord D (mapClosingLayer f D (wordScenario () u)), closingLayerRoot_map,
      wordScenario_root]
    congr 1
    simp only [scenarioWord, EncodedClosingRestriction.word_map]
    exact scenarioWord_wordScenario () u
  apply Subtype.ext
  change closingLayerTrace _ D _ _ = closingLayerTrace (strategyPolicy σ (past ∘ f)) D _ _
  rw [← strategyPolicy_restrict σ past f, closingLayerTrace_restrict, mapped]

def strategyBlocks (words : List (BlockInput I₁ I₂ D)) : List (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D) :=
  words.reverseRecOn [] (fun words u blocks => blocks ++ [strategyBlock σ (blockHistory words) u])

@[simp] theorem strategyBlocks_nil : strategyBlocks σ ([] : List (BlockInput I₁ I₂ D)) = [] := by simp only [strategyBlocks, List.reverseRecOn_nil]
@[simp] theorem strategyBlocks_append (words : List (BlockInput I₁ I₂ D)) (u : BlockInput I₁ I₂ D) :
    strategyBlocks σ (words ++ [u]) = strategyBlocks σ words ++ [strategyBlock σ (blockHistory words) u] := by
  simp only [strategyBlocks, List.reverseRecOn_concat]

theorem strategyBlocks_environment (words : List (BlockInput I₁ I₂ D)) :
    ((strategyBlocks σ words).map (fun w => w.val.map (fun a => envRecordEquiv I₁ I₂ a.1))).flatten =
      blockHistory words := by
  induction words using List.reverseRecOn with
  | nil => simp only [strategyBlocks_nil, List.map_nil, List.flatten_nil, blockHistory_nil]
  | append_singleton words u ih =>
    simp only [strategyBlocks_append, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      strategyBlock, ruleBlock_environment, scenarioWord_wordScenario, ih, blockHistory_append]

variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
def strategyState (words : List (BlockInput I₁ I₂ D)) : B.State :=
  (strategyBlocks σ words).foldl B.step B.initial

theorem strategyState_reachable (words : List (BlockInput I₁ I₂ D)) :
    StateReachable B (blockHistory words) (strategyState σ B words) :=
  ⟨strategyBlocks σ words, strategyBlocks_environment σ words, rfl⟩

@[simp] theorem strategyState_nil : strategyState σ B ([] : List (BlockInput I₁ I₂ D)) = B.initial := by simp only [strategyState, strategyBlocks_nil, List.foldl_nil]
@[simp] theorem strategyState_append (words : List (BlockInput I₁ I₂ D)) (u : BlockInput I₁ I₂ D) :
    strategyState σ B (words ++ [u]) = B.step (strategyState σ B words) (strategyBlock σ (blockHistory words) u) := by
  simp only [strategyState, strategyBlocks_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

end
end Characterisation.ComponentTrees
