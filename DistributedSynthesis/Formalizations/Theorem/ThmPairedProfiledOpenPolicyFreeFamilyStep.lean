/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedRealization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenRepresentableAutomaton

/-!
# Policy-free semantic steps in the profiled outer family automaton

The rational block table is chosen for a whole exact-view family before the
outer run is rationalized.  This file connects that finite move to the
proof-side semantic representative retained by a pointed realization.  In
particular, an alternating successor is the literal next
`PairedStrategyMemory` state of the raw winning strategy; no strict-leader
signal and no post-extraction common-sender choice is used.
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

/-- The finite productive move chosen by a fixed right semantic realization. -/
noncomputable def ProfiledOpenRightRealization.representableMove
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    ProfiledOpenRepresentableMove A :=
  .right source (realization.coherentTable A).table

/-- Left-to-right mirror. -/
noncomputable def ProfiledOpenLeftRealization.representableMove
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    ProfiledOpenRepresentableMove A :=
  .left source (realization.coherentTable A).table

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem ProfiledOpenRightRealization.representableMove_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    (realization.representableMove A).Valid A :=
  ⟨(realization.coherentTable A).wins,
    (realization.coherentTable A).representable⟩

theorem ProfiledOpenLeftRealization.representableMove_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    (realization.representableMove A).Valid A :=
  ⟨(realization.coherentTable A).wins,
    (realization.coherentTable A).representable⟩

@[simp] theorem ProfiledOpenRightRealization.representableMove_roots
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    (realization.representableMove A).roots A =
      profiledOpenRightClassifiedRoots A source := rfl

@[simp] theorem ProfiledOpenLeftRealization.representableMove_roots
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    (realization.representableMove A).roots A =
      profiledOpenLeftClassifiedRoots A source := rfl

/-- The finite right move reads exactly the coherent output at the requested
family member and finite input history. -/
theorem ProfiledOpenRightRealization.representableMove_successor
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1}) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let output := profiledOpenRightRepresentableOutputAt A source
      (realization.coherentTable A).table member
      (omegaOfList (past ++ [input])) past.length
    (realization.representableMove A).successor A
        (.fromOne member.1 row past input) =
      (.left (output.2 row).1,
        profiledOpenLeftClassifiedRoots A (output.2 row).2) := by
  classical
  dsimp only
  let table := (realization.coherentTable A).table
  have hvalid : ProfiledOpenRepresentableMove.Valid A
      (.right source table) := realization.representableMove_valid A
  change (ProfiledOpenRepresentableMove.right source table).successor A
      (.fromOne member.1 row past input) = _
  simp only [ProfiledOpenRepresentableMove.successor]
  rw [dif_pos hvalid]
  dsimp only
  rw [dif_pos member.2]

/-- Left finite move readback. -/
theorem ProfiledOpenLeftRealization.representableMove_successor
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1}) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let output := profiledOpenLeftRepresentableOutputAt A source
      (realization.coherentTable A).table member
      (omegaOfList (past ++ [input])) past.length
    (realization.representableMove A).successor A
        (.fromTwo member.1 row past input) =
      (.right (output.2 row).1,
        profiledOpenRightClassifiedRoots A (output.2 row).2) := by
  classical
  dsimp only
  let table := (realization.coherentTable A).table
  have hvalid : ProfiledOpenRepresentableMove.Valid A
      (.left source table) := realization.representableMove_valid A
  change (ProfiledOpenRepresentableMove.left source table).successor A
      (.fromTwo member.1 row past input) = _
  simp only [ProfiledOpenRepresentableMove.successor]
  rw [dif_pos hvalid]
  dsimp only
  rw [dif_pos member.2]

end

/-! ## Exact alternating semantic steps -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A right finite-family transition carries a proof-side semantic history,
and its selected child is the literal operational successor of the selected
raw-strategy memory.  The public finite direction need not reveal which side
is informed. -/
theorem exists_profiledOpenRightPolicyFreeFamilyStep
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
        (realization.representableMove A).successor A
            (.fromOne member.1 row past input) =
          (.left child.selected.1,
            profiledOpenLeftClassifiedRoots A (output.2 row).2) ∧
        output =
          profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2) ∧
        PairedStrategyMemory.step (A := A)
            (.processOne (realization.entry member)
              (realization.minimum member))
            (.fromOne row
              (semanticPast.map fun old => (old.1.2, old.2)) input) =
          .processTwo child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  let env := omegaOfList (past ++ [input])
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change omegaOfList (past ++ [input]) past.length = input
    rw [omegaOfList_eq_getElem (past ++ [input]) past.length hnPrefix]
    simp
  obtain ⟨semanticPast, child, houtput, hselected, hstep⟩ :=
    exists_profiledOpenRightCoherentChildStep A source strategy hwin basis
      realization member env past.length row
  refine ⟨semanticPast, child, ?_, ?_, ?_⟩
  · simpa [hselected] using
      realization.representableMove_successor A member row past input
  · simpa [hinput] using houtput
  · simpa [hinput] using hstep

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact left-to-right mirror of
`exists_profiledOpenRightPolicyFreeFamilyStep`. -/
theorem exists_profiledOpenLeftPolicyFreeFamilyStep
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
        (realization.representableMove A).successor A
            (.fromTwo member.1 row past input) =
          (.right child.selected.1,
            profiledOpenRightClassifiedRoots A (output.2 row).2) ∧
        output =
          profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2) ∧
        PairedStrategyMemory.step (A := A)
            (.processTwo (realization.entry member)
              (realization.minimum member))
            (.fromTwo row
              (semanticPast.map fun old => (old.1.2, old.2)) input) =
          .processOne child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  let env := omegaOfList (past ++ [input])
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change omegaOfList (past ++ [input]) past.length = input
    rw [omegaOfList_eq_getElem (past ++ [input]) past.length hnPrefix]
    simp
  obtain ⟨semanticPast, child, houtput, hselected, hstep⟩ :=
    exists_profiledOpenLeftCoherentChildStep A source strategy hwin basis
      realization member env past.length row
  refine ⟨semanticPast, child, ?_, ?_, ?_⟩
  · simpa [hselected] using
      realization.representableMove_successor A member row past input
  · simpa [hinput] using houtput
  · simpa [hinput] using hstep

end

end

end DetParityAutomaton

end DistributedSynthesis
