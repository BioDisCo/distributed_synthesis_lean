/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Execution

/-! Renaming private-input alphabets preserves full views and every physical
execution round. Strategies are transported through the inverse view map. -/
namespace Characterisation.InputAlphabetRelabeling
open DistributedSynthesis
variable {I₁ I₂ J₁ J₂ O₁ O₂ : Type}

def payload (f₁ : I₁ → J₁) (f₂ : I₂ → J₂) : PSum I₁ I₂ → PSum J₁ J₂
  | .inl i => .inl (f₁ i)
  | .inr i => .inr (f₂ i)

def view (f₁ : I₁ → J₁) (f₂ : I₂ → J₂) : {p : Proc} → View I₁ I₂ p → View J₁ J₂ p
  | _, .empty p => .empty p
  | _, .noRecv v i => .noRecv (view f₁ f₂ v) (payload f₁ f₂ i)
  | _, .recv v i w j => .recv (view f₁ f₂ v) (payload f₁ f₂ i) (view f₁ f₂ w) (payload f₁ f₂ j)

variable (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂)

theorem payload_inverse (i : PSum I₁ I₂) : payload e₁.symm e₂.symm (payload e₁ e₂ i) = i := by
  cases i <;> simp [payload]

theorem view_inverse {p : Proc} (v : View I₁ I₂ p) : view e₁.symm e₂.symm (view e₁ e₂ v) = v := by
  induction v with
  | empty => rfl
  | noRecv v i ih => simp only [view,ih,payload_inverse]
  | recv v i w j ih₁ ih₂ => simp only [view,ih₁,ih₂,payload_inverse]

def environment (r : EnvironmentRound I₁ I₂) : EnvironmentRound J₁ J₂ :=
  ⟨e₁ r.inputOne,e₂ r.inputTwo,r.graph⟩
def record (r : RoundRecord I₁ I₂ Graph O₁ O₂) : RoundRecord J₁ J₂ Graph O₁ O₂ :=
  ⟨e₁ r.inputOne,e₂ r.inputTwo,r.graph,r.outputOne,r.outputTwo⟩
def strategy (σ : StrategyPair I₁ I₂ O₁ O₂) : StrategyPair J₁ J₂ O₁ O₂ :=
  ⟨fun v => σ.one (view e₁.symm e₂.symm v),fun v => σ.two (view e₁.symm e₂.symm v)⟩

theorem environment_inverse (r : EnvironmentRound I₁ I₂) :
    environment e₁.symm e₂.symm (environment e₁ e₂ r) = r := by
  cases r; simp [environment]

theorem record_inverse (r : RoundRecord I₁ I₂ Graph O₁ O₂) :
    record e₁.symm e₂.symm (record e₁ e₂ r) = r := by
  cases r; simp [record]

theorem strategy_inverse (σ : StrategyPair I₁ I₂ O₁ O₂) :
    strategy e₁.symm e₂.symm (strategy e₁ e₂ σ) = σ := by
  cases σ
  simp only [strategy,Equiv.symm_symm,view_inverse]

theorem viewPair_map (h : History I₁ I₂ Graph O₁ O₂) :
    viewPair (h.map (record e₁ e₂)) = (view e₁ e₂ (viewPair h).1,view e₁ e₂ (viewPair h).2) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h r ih =>
    simp only [List.map_append,List.map_singleton]
    change viewPair (History.append _ _) = _
    rw [viewPair_append]
    change _ = (view e₁ e₂ (viewPair (History.append h r)).1,view e₁ e₂ (viewPair (History.append h r)).2)
    rw [viewPair_append,ih]
    cases hg : r.graph <;> simp [advanceViews,record,hg,view,payload]
    all_goals first | rfl | exact ⟨rfl,rfl⟩

theorem nextRound_map (σ : StrategyPair I₁ I₂ O₁ O₂)
    (h : History I₁ I₂ Graph O₁ O₂) (r : EnvironmentRound I₁ I₂) :
    nextRound (strategy e₁ e₂ σ) (h.map (record e₁ e₂)) (environment e₁ e₂ r) =
      record e₁ e₂ (nextRound σ h r) := by
  have natural : advanceViewsWithEnvironment
      (view e₁ e₂ (viewPair h).1,view e₁ e₂ (viewPair h).2) (environment e₁ e₂ r) =
      (view e₁ e₂ (advanceViewsWithEnvironment (viewPair h) r).1,
       view e₁ e₂ (advanceViewsWithEnvironment (viewPair h) r).2) := by
    cases r with
    | mk one two g => cases g <;> rfl
  unfold nextRound nextView
  rw [viewPair_map,natural]
  simp only [strategy,view_inverse]
  rfl

theorem executionPrefix_map (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    executionPrefix (strategy e₁ e₂ σ) (fun t => environment e₁ e₂ (env t)) n =
      (executionPrefix σ env n).map (record e₁ e₂) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [executionPrefix_succ,History.append,List.map_append,List.map_singleton,ih,nextRound_map]

theorem execution_map (σ : StrategyPair I₁ I₂ O₁ O₂) (env : EnvironmentSequence I₁ I₂) (n : Nat) :
    execution (strategy e₁ e₂ σ) (fun t => environment e₁ e₂ (env t)) n =
      record e₁ e₂ (execution σ env n) := by
  simp only [execution_apply,executionPrefix_map,nextRound_map]

end Characterisation.InputAlphabetRelabeling
