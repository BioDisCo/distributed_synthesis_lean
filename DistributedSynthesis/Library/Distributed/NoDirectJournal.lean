/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.JournalCompilation
import DistributedSynthesis.Formalizations.Theorem.ThmReversalForgiving

/-! # No-direct-reversal synthesis as journal tree nonemptiness

The journal automaton is constructed independently of a winning strategy. This
semantic reduction bypasses `reversalForgivingSummaries`, which branches on
realizability itself. It does not yet assert encoded computability of the
canonical checker constructors or of tree nonemptiness.
-/

namespace DistributedSynthesis.NoDirectJournal
open DetParityAutomaton

variable {In₁ In₂ Out₁ Out₂ : Type}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable (A : DetParityAutomaton.{0, 0} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [DecidableEq A.State]

/-- Arbitrary perfect-recall realizability on the no-direct-reversal fragment. -/
def Realizable : Prop :=
  ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    ∀ env : EnvironmentSequence In₁ In₂,
      NoDirectReversalSequence env → A.Accepts (execution σ env)

/-- The equivalence is parametric in any semantically correct thread checkers. -/
theorem realizable_iff_nonempty_of_checkers
    (CL : LeftThreadChecker A.reversalForgiving)
    (CR : RightThreadChecker A.reversalForgiving)
    (CC : ChainThreadChecker (A := A.reversalForgiving)) :
    Realizable A ↔
      ∃ tree, (globalJournalAutomaton A.reversalForgiving CL CR CC).acceptsTree tree := by
  classical
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := (reversalForgiving_realizable_iff A).mpr h
    obtain ⟨τ, hτ⟩ := exists_positional_uniformization_winner σ hσ
    exact ⟨tauTree σ τ, tauTree_acceptsTree σ τ CL CR CC hτ⟩
  · intro h
    letI := globalJournalLabelFintype (A := A.reversalForgiving)
    obtain ⟨t, ht⟩ :=
      (globalJournalAutomaton A.reversalForgiving CL CR CC).exists_transitionRational_accepted h
    letI : DecidableEq t.Control := Classical.decEq _
    letI : Inhabited t.Control := ⟨t.initial⟩
    obtain ⟨plans, hplans⟩ := journal_readback_accepts_of_accepts t CL CR CC ht
    refine ⟨journalStrategy plans, ?_⟩
    intro env hnd
    have hno : ¬ HasDirectReversalWord (execution (journalStrategy plans) env) := by
      rw [hasDirectReversalWord_execution_iff]
      exact fun h => h hnd
    exact (reversalForgiving_accepts_iff_of_noReversal A _ hno).mp (hplans env hnd)

/-- The canonical semantic target; its checker compilation remains noncomputable. -/
noncomputable def journal :=
  globalJournalAutomaton A.reversalForgiving
    (leftThreadCheckerInstance A.reversalForgiving)
    (rightThreadCheckerInstance A.reversalForgiving)
    (chainThreadCheckerInstance (A := A.reversalForgiving))

theorem realizable_iff_nonempty :
    Realizable A ↔ ∃ tree, (journal A).acceptsTree tree :=
  realizable_iff_nonempty_of_checkers A _ _ _

/-- The same equivalence through executable outer assembly, with explicit data. -/
theorem realizable_iff_compiled_nonempty
    (CL : LeftThreadChecker A.reversalForgiving)
    (CR : RightThreadChecker A.reversalForgiving)
    (CC : ChainThreadChecker (A := A.reversalForgiving))
    [Fintype (GlobalJournalLabel A.reversalForgiving)] :
    Realizable A ↔ ∃ tree,
      (JournalCompilation.compile A.reversalForgiving CL CR CC).toRunAutomaton.acceptsTree tree :=
  realizable_iff_nonempty_of_checkers A CL CR CC

end DistributedSynthesis.NoDirectJournal
