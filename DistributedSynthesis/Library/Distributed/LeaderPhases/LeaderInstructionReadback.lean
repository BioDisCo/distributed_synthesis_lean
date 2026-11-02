/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PieceTransitions

/-! A receiver can evaluate the agreed leader's previously prescribed table
from the previous environment history and the current input pair. It need
not distinguish one-way delivery from bidirectional delivery. -/
namespace Characterisation
open DistributedSynthesis

theorem receiving_one_identifies_past {I₁ I₂ : Type*}
    (h k : EnvHistory I₁ I₂) (r s : RoundRecord I₁ I₂ Graph Unit Unit)
    (receivesR : r.graph = .left ∨ r.graph = .both)
    (receivesS : s.graph = .left ∨ s.graph = .both)
    (same : currentView .one (h++[r]) = currentView .one (k++[s])) :
    h = k ∧ r.inputOne = s.inputOne ∧ r.inputTwo = s.inputTwo := by
  change currentView .one (History.append h r) = currentView .one (History.append k s) at same
  rw [currentView_one_append,currentView_one_append] at same
  rcases receivesR with rg | rg <;> rcases receivesS with sg | sg <;>
    simp only [rg,sg,View.recv.injEq,PSum.inl.injEq,PSum.inr.injEq] at same
  all_goals exact ⟨joint_env_history h k same.1 same.2.2.1,same.2.1,same.2.2.2⟩

theorem receiving_two_identifies_past {I₁ I₂ : Type*}
    (h k : EnvHistory I₁ I₂) (r s : RoundRecord I₁ I₂ Graph Unit Unit)
    (receivesR : r.graph = .right ∨ r.graph = .both)
    (receivesS : s.graph = .right ∨ s.graph = .both)
    (same : currentView .two (h++[r]) = currentView .two (k++[s])) :
    h = k ∧ r.inputOne = s.inputOne ∧ r.inputTwo = s.inputTwo := by
  change currentView .two (History.append h r) = currentView .two (History.append k s) at same
  rw [currentView_two_append,currentView_two_append] at same
  rcases receivesR with rg | rg <;> rcases receivesS with sg | sg <;>
    simp only [rg,sg,View.recv.injEq,PSum.inl.injEq,PSum.inr.injEq] at same
  all_goals exact ⟨joint_env_history h k same.2.2.1 same.1,same.2.2.2,same.2.1⟩

/-- A prescribed instruction can depend on the full previous history and
both current inputs at a receiving process. It cannot depend on which of
the two currently indistinguishable delivering graphs was selected. -/
theorem receiving_one_table_is_local {I₁ I₂ C : Type*} [Nonempty C]
    (table : EnvHistory I₁ I₂ → I₁ → I₂ → C) :
    ∃ response : View I₁ I₂ .one → C, ∀ (h : EnvHistory I₁ I₂) x y g,
      g = .left ∨ g = .both →
      response (currentView .one (h++[⟨x,y,g,(),()⟩])) = table h x y := by
  let S := {s : NextScenario (EnvHistory I₁ I₂) I₁ I₂ //
    s.2.2.2 = .left ∨ s.2.2.2 = .both}
  let hist (s : S) := scenarioHistory id s.val
  let value (s : S) := table s.val.1 s.val.2.1 s.val.2.2.1
  have coherent : ∀ s t : S, currentView .one (hist s) = currentView .one (hist t) →
      value s = value t := by
    intro s t eq
    have facts := receiving_one_identifies_past s.val.1 t.val.1
      ⟨s.val.2.1,s.val.2.2.1,s.val.2.2.2,(),()⟩
      ⟨t.val.2.1,t.val.2.2.1,t.val.2.2.2,(),()⟩ s.property t.property eq
    dsimp only at facts
    dsimp [value]
    rw [facts.1,facts.2.1,facts.2.2]
  obtain ⟨response,correct⟩ := factor_local_response (fun s => currentView .one (hist s)) value coherent
  exact ⟨response,fun h x y g delivered => correct ⟨(h,x,y,g),delivered⟩⟩

theorem receiving_two_table_is_local {I₁ I₂ C : Type*} [Nonempty C]
    (table : EnvHistory I₁ I₂ → I₁ → I₂ → C) :
    ∃ response : View I₁ I₂ .two → C, ∀ (h : EnvHistory I₁ I₂) x y g,
      g = .right ∨ g = .both →
      response (currentView .two (h++[⟨x,y,g,(),()⟩])) = table h x y := by
  let S := {s : NextScenario (EnvHistory I₁ I₂) I₁ I₂ //
    s.2.2.2 = .right ∨ s.2.2.2 = .both}
  let hist (s : S) := scenarioHistory id s.val
  let value (s : S) := table s.val.1 s.val.2.1 s.val.2.2.1
  have coherent : ∀ s t : S, currentView .two (hist s) = currentView .two (hist t) →
      value s = value t := by
    intro s t eq
    have facts := receiving_two_identifies_past s.val.1 t.val.1
      ⟨s.val.2.1,s.val.2.2.1,s.val.2.2.2,(),()⟩
      ⟨t.val.2.1,t.val.2.2.1,t.val.2.2.2,(),()⟩ s.property t.property eq
    dsimp only at facts
    dsimp [value]
    rw [facts.1,facts.2.1,facts.2.2]
  obtain ⟨response,correct⟩ := factor_local_response (fun s => currentView .two (hist s)) value coherent
  exact ⟨response,fun h x y g delivered => correct ⟨(h,x,y,g),delivered⟩⟩

end Characterisation
