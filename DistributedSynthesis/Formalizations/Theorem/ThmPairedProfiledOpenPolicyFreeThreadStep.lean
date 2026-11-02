/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPolicyFreeFamilyStep
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenObservableThreads

/-!
# A policy-free family move advances the retained semantic thread

The common family table must be selected before rationalization.  This file
connects that table to the corrected observable-thread automaton: resolving a
member of the family advances the retained hidden root to the root actually
emitted by the table, and that hidden transition is simultaneously a literal
step of the original winning strategy memory.

This is the positive counterpart of the quantifier separation in
`LemInputFreeBasisNotFamilyUniform`.  The public transition sees a whole view
class and one common table.  The selected member is a universally resolved
proof-side thread; it is not revealed to either process.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A right-to-left resolution of the common policy-free table is both an
exact live-thread transition and a genuine raw-strategy memory step. -/
theorem exists_profiledOpenRightPolicyFreeLiveThreadStep
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1}) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let env := omegaOfList (past ++ [input])
    let output := profiledOpenRightRepresentableOutputAt A source
      (realization.coherentTable A).table member env past.length
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∃ child : ProfiledOpenLeftPointedRealization A strategy hwin basis
          (output.2 row).2,
        profiledOpenThreadStep A (.right source)
            (.live (.right member.1))
            (realization.representableMove A, .left (output.2 row).2)
            (.fromOne member.1 row past input) =
          .live (.left child.selected.1) ∧
        PairedStrategyMemory.step (A := A)
            (.processOne (realization.entry member)
              (realization.minimum member))
            (.fromOne row
              (semanticPast.map fun old => (old.1.2, old.2)) input) =
          .processTwo child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  let output := profiledOpenRightRepresentableOutputAt A source
    (realization.coherentTable A).table member
    (omegaOfList (past ++ [input])) past.length
  obtain ⟨semanticPast, child, hsuccessor, _houtput, hmemory⟩ :=
    exists_profiledOpenRightPolicyFreeFamilyStep A realization member row past
      input
  refine ⟨semanticPast, child, ?_, hmemory⟩
  have hclass :
      ((realization.representableMove A).successor A
        (.fromOne member.1 row past input)).2 =
          (ProfiledOpenObservation.left (A := A) (output.2 row).2).roots A := by
    rw [hsuccessor]
    rfl
  have hstep := profiledOpenThreadStep_live_of A (.right source)
    (.right member.1)
    (realization.representableMove A, .left (output.2 row).2)
    (.fromOne member.1 row past input) rfl hclass
  rw [hsuccessor] at hstep
  exact hstep

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right mirror. -/
theorem exists_profiledOpenLeftPolicyFreeLiveThreadStep
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1}) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let env := omegaOfList (past ++ [input])
    let output := profiledOpenLeftRepresentableOutputAt A source
      (realization.coherentTable A).table member env past.length
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      ∃ child : ProfiledOpenRightPointedRealization A strategy hwin basis
          (output.2 row).2,
        profiledOpenThreadStep A (.left source)
            (.live (.left member.1))
            (realization.representableMove A, .right (output.2 row).2)
            (.fromTwo member.1 row past input) =
          .live (.right child.selected.1) ∧
        PairedStrategyMemory.step (A := A)
            (.processTwo (realization.entry member)
              (realization.minimum member))
            (.fromTwo row
              (semanticPast.map fun old => (old.1.2, old.2)) input) =
          .processOne child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  let output := profiledOpenLeftRepresentableOutputAt A source
    (realization.coherentTable A).table member
    (omegaOfList (past ++ [input])) past.length
  obtain ⟨semanticPast, child, hsuccessor, _houtput, hmemory⟩ :=
    exists_profiledOpenLeftPolicyFreeFamilyStep A realization member row past
      input
  refine ⟨semanticPast, child, ?_, hmemory⟩
  have hclass :
      ((realization.representableMove A).successor A
        (.fromTwo member.1 row past input)).2 =
          (ProfiledOpenObservation.right (A := A) (output.2 row).2).roots A := by
    rw [hsuccessor]
    rfl
  have hstep := profiledOpenThreadStep_live_of A (.left source)
    (.left member.1)
    (realization.representableMove A, .right (output.2 row).2)
    (.fromTwo member.1 row past input) rfl hclass
  rw [hsuccessor] at hstep
  exact hstep

end

end

end DetParityAutomaton

end DistributedSynthesis
