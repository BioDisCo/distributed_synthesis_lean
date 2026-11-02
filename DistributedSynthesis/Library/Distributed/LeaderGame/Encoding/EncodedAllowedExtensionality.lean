/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolver

/-! Local tests depend on membership in the advertised outcome set, not on
the order or multiplicity of its numeric list presentation. -/
namespace Characterisation
open DistributedSynthesis

namespace EncodedGraphMemory
 theorem checks_membership_congr (d : Data) (a b : List EncodedLeaderAlphabet.Outcome)
    (same : ∀ o, o ∈ a ↔ o ∈ b) : checks d a = checks d b := by
  simp only [checks,valid,Restricted,same]
  rfl
end EncodedGraphMemory
namespace EncodedLeftGraphMemory
 theorem checks_membership_congr (d : Data) (a b : List EncodedLeaderAlphabet.Outcome)
    (same : ∀ o, o ∈ a ↔ o ∈ b) : checks d a = checks d b := by
  simp only [checks,valid,Restricted,same]
  rfl
end EncodedLeftGraphMemory

namespace EncodedLeaderPhysical
 theorem solve_membership_congr (p : EncodedLeaderPhase.Data) (m : EncodedGraphMemory.Data)
    (a b : List EncodedLeaderAlphabet.Outcome) (same : ∀ o, o ∈ a ↔ o ∈ b) :
    solve (p,m,a) = solve (p,m,b) := by
  have rows : checks (p,m,a) = checks (p,m,b) := by
    simp only [checks,memory,allowed,EncodedGraphMemory.checks_membership_congr m a b same]
    rfl
  change EncodedLeaderSafety.solve (_,_,_,_,checks (p,m,a)) =
    EncodedLeaderSafety.solve (_,_,_,_,checks (p,m,b))
  rw [rows]
  rfl
end EncodedLeaderPhysical
namespace EncodedLeftLeaderPhysical
 theorem solve_membership_congr (p : EncodedLeaderPhase.Data) (m : EncodedGraphMemory.Data)
    (a b : List EncodedLeaderAlphabet.Outcome) (same : ∀ o, o ∈ a ↔ o ∈ b) :
    solve (p,m,a) = solve (p,m,b) := by
  have rows : checks (p,m,a) = checks (p,m,b) := by
    simp only [checks,EncodedLeaderPhysical.memory,EncodedLeaderPhysical.allowed,
      EncodedLeftGraphMemory.checks_membership_congr m a b same]
    rfl
  change EncodedLeaderSafety.solve (_,_,_,_,checks (p,m,a)) =
    EncodedLeaderSafety.solve (_,_,_,_,checks (p,m,b))
  rw [rows]
  rfl
end EncodedLeftLeaderPhysical
namespace EncodedHeaderCompiler
 theorem test_membership_congr (g : GraphData) (o : EncodedRoundObjectives.Data)
    (h : EncodedLeaderAlphabet.Header) (a b : List EncodedLeaderAlphabet.Outcome)
    (same : ∀ code, code ∈ a ↔ code ∈ b) (one : Bool) :
    test (g,o,h,a) one = test (g,o,h,b) one := by
  unfold test solve
  cases one with
  | false =>
    simp only [cond_false]
    apply Bool.eq_iff_iff.mpr
    rw [EncodedInitialLeftLeaderBanks.solve_iff,EncodedInitialLeftLeaderBanks.solve_iff]
    apply exists_congr
    intro bank
    change (_ ∧ EncodedLeftLeaderPhysical.solve (_,_,a) = true) ↔
      (_ ∧ EncodedLeftLeaderPhysical.solve (_,_,b) = true)
    rw [EncodedLeftLeaderPhysical.solve_membership_congr _ _ a b same]
    rfl
  | true =>
    simp only [cond_true]
    apply Bool.eq_iff_iff.mpr
    rw [EncodedInitialLeaderBanks.solve_iff,EncodedInitialLeaderBanks.solve_iff]
    apply exists_congr
    intro bank
    change (_ ∧ EncodedLeaderPhysical.solve (_,_,a) = true) ↔
      (_ ∧ EncodedLeaderPhysical.solve (_,_,b) = true)
    rw [EncodedLeaderPhysical.solve_membership_congr _ _ a b same]
    rfl
end EncodedHeaderCompiler
end Characterisation
