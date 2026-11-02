/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingStrategyExtraction

/-! Executable local-observation checks for a bank of closing plans. This
bridges the rolling-plan representation to the existing bounded closing
compiler instead of introducing another observation model. -/
namespace Characterisation
open DistributedSynthesis

def closingLayerWord {H I₁ I₂ : Type} :
    (n : Nat) → ClosingLayer H I₁ I₂ n → Fin n → I₁ × I₂ × Graph
  | 0, _ => Fin.elim0
  | n+1, s => Fin.lastCases s.2 (closingLayerWord n s.1)

def closingLayerFromWord {H I₁ I₂ : Type} (h : H) :
    (n : Nat) → (Fin n → I₁ × I₂ × Graph) → ClosingLayer H I₁ I₂ n
  | 0, _ => h
  | n+1, word => (closingLayerFromWord h n (fun i => word i.castSucc),word (Fin.last n))

theorem closingLayerWord_fromWord {H I₁ I₂ : Type} (h : H) (n : Nat)
    (word : Fin n → I₁ × I₂ × Graph) :
    closingLayerWord n (closingLayerFromWord h n word) = word := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [closingLayerWord,closingLayerFromWord,Fin.lastCases_last]
    · simpa only [closingLayerWord,closingLayerFromWord,Fin.lastCases_castSucc] using congrFun (ih _) j

theorem closingLayerRoot_fromWord {H I₁ I₂ : Type} (h : H) (n : Nat)
    (word : Fin n → I₁ × I₂ × Graph) :
    closingLayerRoot n (closingLayerFromWord h n word) = h := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _

theorem closingLayerHistory_word {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerHistory past n s = past (closingLayerRoot n s) ++
      List.ofFn (fun i => let r := closingLayerWord n s i
        (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) := by
  induction n with
  | zero => simp [closingLayerHistory,closingLayerRoot]
  | succ n ih =>
    rw [List.ofFn_succ']
    simpa [closingLayerHistory,closingLayerRoot,closingLayerWord,scenarioHistory,
      List.concat_eq_append,List.append_assoc] using congrArg (fun h => h ++ [⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩]) (ih s.1)

def closingPolicyOfBank {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) : ClosingPolicy H I₁ I₂ O₁ O₂ (D+1) :=
  fun t s => bank (closingLayerRoot (t.val+1) s) ((),⟨t,closingLayerWord (t.val+1) s⟩)

def ClosingBankCoherent {H I₁ I₂ O₁ O₂ : Type} [DecidableEq I₁] [DecidableEq I₂] {D : Nat}
    (shape : InputShape H) (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) : Prop :=
  ClosingPolicyCoherent shape (closingPolicyOfBank bank)

instance closingBankCoherent_decidable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
    (shape : InputShape H) (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) :
    Decidable (ClosingBankCoherent shape bank) := by
  unfold ClosingBankCoherent
  infer_instance

/-- Passing the bank check gives one local strategy for all roots and all
hypothetical graph-and-input prefixes, including every intermediate output. -/
theorem closingBankCoherent_local {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (coherent : ClosingBankCoherent shape bank) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ h (s : ClosingScenario I₁ I₂ (D+1)),
      σ.one (currentView .one (windowHistory (fun _ : Unit => past h) (D+1) s)) = (bank h s).1 ∧
      σ.two (currentView .two (windowHistory (fun _ : Unit => past h) (D+1) s)) = (bank h s).2 := by
  obtain ⟨σ,correct⟩ := (closingPolicyCoherent_iff_local past shape rep L depth (closingPolicyOfBank bank)).mp coherent
  refine ⟨σ,fun h s => ?_⟩
  rcases s with ⟨⟨⟩,t,word⟩
  have result := correct t (closingLayerFromWord h (t.val+1) word)
  simpa only [closingPolicyOfBank,closingLayerHistory_word,closingLayerWord_fromWord,
    closingLayerRoot_fromWord,windowHistory] using result

theorem closingBankOfStrategy_coherent {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [DecidableEq I₁] [DecidableEq I₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H) (rep : RepresentsInputShape past shape) :
    ClosingBankCoherent shape (fun h => closingPlanOfStrategy σ (past h) (D+1)) := by
  have output : ∀ t s, closingPolicyOfBank (fun h => closingPlanOfStrategy σ (past h) (D+1)) t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))) := by
    intro t s
    simp only [closingPolicyOfBank,closingPlanOfStrategy,windowHistory,closingLayerHistory_word]
  intro t
  constructor
  · intro s r eq
    rw [output,output,(closingLayerShape_exact past shape rep _ .one s r).mp eq]
  · intro s r eq
    rw [output,output,(closingLayerShape_exact past shape rep _ .two s r).mp eq]

/-- When all roots share the leader view, extending every root by the same
one-way input word preserves the entire source observation matrix. Thus the
closing-bank check is one fixed finite predicate throughout the phase. -/
theorem rollingSourceHistory_shape {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (same : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (node : List (I₂ × I₁)) : RepresentsInputShape (rollingSourceHistory past node) shape := by
  have leaders : ∀ h k, shape .one h k = true := fun h k => (rep .one h k).mpr (same h k)
  induction node using List.reverseRecOn with
  | nil =>
    intro p h k
    simpa [rollingSourceHistory,rightInputHistory] using rep p h k
  | append_singleton node r ih =>
    intro p h k
    rw [rollingSourceHistory_snoc,rollingSourceHistory_snoc]
    change shape p h k = true ↔ currentView p (History.append _ _) = currentView p (History.append _ _)
    cases p
    · rw [currentView_one_append,currentView_one_append]
      simpa using ih .one h k
    · rw [currentView_two_append,currentView_two_append]
      simp [Proc.other,← ih .one h k,← ih .two h k,leaders]

theorem rollingOriginalBank_coherent {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [DecidableEq I₁] [DecidableEq I₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (same : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (node : List (I₂ × I₁)) : ClosingBankCoherent shape (rollingOriginalBank σ past D node) :=
  closingBankOfStrategy_coherent σ _ shape (rollingSourceHistory_shape past shape rep same node)

end Characterisation
