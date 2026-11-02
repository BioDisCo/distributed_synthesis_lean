/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalJournalAutomaton

/-! # Executable assembly of the journal tree automaton

This constructor takes an objective and three concrete thread checkers as data.
It does not choose a winning strategy or test realizability. The semantic
checker constructors are noncomputable; this module makes only the outer
assembly executable, not the complete objective-to-journal compiler.
-/

namespace DistributedSynthesis.JournalCompilation
open DetParityAutomaton

variable {In₁ In₂ Out₁ Out₂ : Type}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (A : DetParityAutomaton.{0, 0} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [DecidableEq A.State]
variable (CL : LeftThreadChecker A) (CR : RightThreadChecker A)
variable (CC : ChainThreadChecker (A := A))

/-- The priority shift is a maximum over the supplied finite state enumeration. -/
def shift : Nat :=
  2 * ((Finset.univ.sup fun state : A.State => A.priority state) + 1)

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] in
@[simp] theorem shift_eq : shift A = globalShift A := rfl

/-- Executable priorities with the same min-even convention as the journal. -/
def priority (state : GlobalJournalState A CL CR CC) : Nat :=
  match state with
  | Sum.inl atom => A.priority atom.2
  | Sum.inr (Sum.inl (checker, _)) => CL.monitor.priority checker + shift A
  | Sum.inr (Sum.inr (Sum.inl (checker, _))) => CR.monitor.priority checker + shift A
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, _)))) =>
      CC.monitor.priority checker + shift A
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, _))))) =>
      CC.monitor.priority checker + shift A
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => shift A

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem priority_eq (state : GlobalJournalState A CL CR CC) :
    priority A CL CR CC state = globalJournalPriority A CL CR CC state := rfl

/-- Assemble the finite journal monitor from concrete checker tables.
The label enumeration is supplied explicitly; no classical enumeration is used. -/
def compile [Fintype (GlobalJournalLabel A)] :
    DeterministicBlockMonitor.{0, 0, 0} (GlobalJournalBranch A) (GlobalJournalLabel A) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := GlobalJournalState A CL CR CC
  stateFinite := by
    letI := CL.monitor.stateFinite
    letI := CR.monitor.stateFinite
    letI := CC.monitor.stateFinite
    infer_instance
  initial := Sum.inl (A.initial, A.initial)
  step := globalJournalStep A CL CR CC
  priority := priority A CL CR CC

omit [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The executable assembly is exactly the semantic automaton. -/
theorem compile_toRunAutomaton [Fintype (GlobalJournalLabel A)] :
    (compile A CL CR CC).toRunAutomaton = globalJournalAutomaton A CL CR CC := rfl

omit [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem compile_acceptsTree_iff [Fintype (GlobalJournalLabel A)]
    (tree : LabeledTree (GlobalJournalBranch A) (GlobalJournalLabel A)) :
    (compile A CL CR CC).toRunAutomaton.acceptsTree tree ↔
      (globalJournalAutomaton A CL CR CC).acceptsTree tree := Iff.rfl

end DistributedSynthesis.JournalCompilation
