/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockArena

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

theorem closingLayerFromWord_word {H I₁ I₂ : Type} (n : Nat)
    (s : ClosingLayer H I₁ I₂ n) :
    closingLayerFromWord (closingLayerRoot n s) n (closingLayerWord n s) = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (closingLayerFromWord (closingLayerRoot n s.1) n
      (fun i => closingLayerWord (n+1) s i.castSucc), closingLayerWord (n+1) s (Fin.last n)) = s
    simp only [closingLayerWord, Fin.lastCases_castSucc, Fin.lastCases_last, ih]
    rfl

def scenarioWord {H I₁ I₂ : Type} (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n :=
  ⟨List.ofFn (fun i => envRecordEquiv I₁ I₂ (closingLayerWord n s i)), List.length_ofFn⟩

def wordScenario {H I₁ I₂ : Type} (h : H) {n : Nat}
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) : ClosingLayer H I₁ I₂ n :=
  closingLayerFromWord h n (fun i => (envRecordEquiv I₁ I₂).symm (u.val.get (i.cast u.property.symm)))

@[simp] theorem wordScenario_root {H I₁ I₂ : Type} (h : H) {n : Nat}
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) :
    closingLayerRoot n (wordScenario h u) = h := closingLayerRoot_fromWord h n _

@[simp] theorem scenarioWord_wordScenario {H I₁ I₂ : Type} (h : H) {n : Nat}
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) :
    scenarioWord n (wordScenario h u) = u := by
  apply Subtype.ext
  simp only [scenarioWord, wordScenario, closingLayerWord_fromWord, Equiv.apply_symm_apply]
  apply List.ext_getElem
  · simp [u.property]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.get_eq_getElem]
    rfl

@[simp] theorem wordScenario_scenarioWord {H I₁ I₂ : Type} (n : Nat)
    (s : ClosingLayer H I₁ I₂ n) :
    wordScenario (closingLayerRoot n s) (scenarioWord n s) = s := by
  unfold wordScenario scenarioWord
  simp only [List.get_eq_getElem, List.getElem_ofFn, Equiv.symm_apply_apply]
  exact closingLayerFromWord_word n s

def blockScenarioEquiv (H I₁ I₂ : Type) (n : Nat) :
    (H × BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) ≃ ClosingLayer H I₁ I₂ n where
  toFun := fun x => wordScenario x.1 x.2
  invFun := fun s => (closingLayerRoot n s, scenarioWord n s)
  left_inv := by intro x; simp
  right_inv := wordScenario_scenarioWord n

theorem scenarioWord_history {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerHistory past n s = past (closingLayerRoot n s) ++ (scenarioWord n s).val :=
  closingLayerHistory_word past n s

@[simp] theorem wordScenario_history {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (i : H) {n : Nat} (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) :
    closingLayerHistory past n (wordScenario i u) = past i ++ u.val := by
  rw [scenarioWord_history, wordScenario_root, scenarioWord_wordScenario]

end Characterisation.PeriodicBlocks
