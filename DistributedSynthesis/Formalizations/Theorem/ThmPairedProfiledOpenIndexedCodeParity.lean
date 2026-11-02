/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeParity
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefThreadSystem

/-!
# Code-observable parity for indexed profiled belief nodes

This is the concrete locality-safe objective presentation.  The hidden
objective monitor still universally selects an initial side and persistent
lineage, but its deterministic parity automaton reads only the finite child
`ProfiledOpenIndexedBiBeliefCode`.  It never reads an exact semantic past,
the strict graph orientation, or a leader bit.

The source-free input-free automaton below therefore has a complete finite
successor table once the child belief code is known.  Semantic acceptance is
left to the recursive correlated unfolding: each forever-live lineage is
flattened to one literal execution of the original realizing strategy.
-/

namespace DistributedSynthesis

universe i u v x y s a

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The deterministic objective monitor over finite child belief codes. -/
noncomputable def profiledOpenIndexedBiBeliefCodeParityDPA
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    DetParityAutomaton (ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  codedAlternatingIndexedLineageCodeDPA initialCode
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedRootPriority A)

/-- Canonical code-only hidden run for one initial side and lineage. -/
noncomputable def profiledOpenIndexedBiBeliefCodeParityRun
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (word : OmegaWord (ProfiledOpenIndexedBiBeliefCode A (I := I)))
    (initialSide : IndexedLineageSide) (lineage : I) :=
  codedAlternatingIndexedLineageCodeRun initialCode
    (profiledOpenIndexedBiBeliefCurrentSlots A) word initialSide lineage

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact objective semantics of the finite code monitor. -/
theorem profiledOpenIndexedBiBeliefCodeParityDPA_accepts_iff
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (word : OmegaWord (ProfiledOpenIndexedBiBeliefCode A (I := I))) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts word ↔
      ∀ initialSide lineage,
        NatSeqMinEvenParity (fun n =>
          (codedAlternatingIndexedLineageCodeThreadSystem initialCode
              (profiledOpenIndexedBiBeliefCurrentSlots A)
              (profiledOpenIndexedRootPriority A)).priority
            (profiledOpenIndexedBiBeliefCodeParityRun A initialCode word
              initialSide lineage n)) := by
  exact codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedRootPriority A) word

/-- The locality-safe source-free run automaton for the complete indexed
belief-node construction. -/
noncomputable def profiledOpenIndexedBiBeliefCodeRunAutomaton
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  sourceFreeBeliefCodeParityRunAutomaton
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)

/-- The exact semantic certificate type now required from the correlated
unfolding. -/
abbrev ProfiledOpenIndexedBiBeliefCodeSemanticCertificate
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (raw : SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedBiBeliefDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I))) : Prop :=
  SourceFreeBeliefCodeParityCertificate
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)
    raw

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Once the correlated semantic certificate is supplied, the existing
input-free rational basis is the only remaining tree-automata input. -/
theorem ProfiledOpenIndexedBiBeliefCodeSemanticCertificate.hasRationalRun
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (raw : SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedBiBeliefDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I)))
    (certificate :
      ProfiledOpenIndexedBiBeliefCodeSemanticCertificate A initialCode raw)
    (basis : (profiledOpenIndexedBiBeliefCodeRunAutomaton A initialCode)
      |>.RationalRunBasis) :
    (profiledOpenIndexedBiBeliefCodeRunAutomaton A initialCode)
      |>.HasRationalRun := by
  exact SourceFreeBeliefCodeParityCertificate.hasRationalRun
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)
    raw certificate basis

/-- The complete policy-state successor factors through the finite child
belief code definitionally. -/
def profiledOpenIndexedBiBeliefCodeControllerNext
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  sourceFreeBeliefCodeParityControllerNext
    (Move := ProfiledOpenIndexedBiBeliefMove A)
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedBiBeliefCodeControllerNext_spec
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (state : SourceFreeBeliefCodeParityFiniteState
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedBiBeliefCodeControllerNext A initialCode state move
        (profiledOpenIndexedBiBeliefNext A state.1 move direction) =
      (profiledOpenIndexedBiBeliefNext A state.1 move direction,
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step state.2
          (profiledOpenIndexedBiBeliefNext A state.1 move direction)) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
