/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Original-DPA acceptance from a finite global machine's epoch coupling

A rational candidate table proves parity for a finite sequence of stored
epoch minima, while the global round machine emits an ordinary physical word.
The structure below is the exact, automaton-independent seam between those
objects: the recurrent physical suffix is cut into nonempty finite blocks and
each block minimum is the corresponding stored epoch priority.

No root, active side, graph orientation, strict leader, candidate, or hidden
bit is executable data here.  A concrete construction may retain such objects
only in proof fields used to establish `blockMin_eq_epochPriority`.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Exact parity-pasting data for one environment trace of one finite global
machine.  `start` discards an arbitrary finite exceptional prefix.  The cuts
are relative to the remaining suffix. -/
structure FiniteGlobalMachineEpochCoupling
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  epochPriority : Nat → Nat
  epochParity : NatSeqMinEvenParity epochPriority
  blockMin_eq_epochPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k = epochPriority k

/-- The exact epoch coupling implies acceptance of the physical word emitted
by the finite global machine. -/
theorem finiteGlobalMachineTraceWord_accepts_of_epochCoupling
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (coupling : A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let priorities : Nat → Nat := fun n ↦ A.priority (A.run word n)
  let tailPriorities : Nat → Nat :=
    fun n ↦ priorities (coupling.start + n)
  have hblocks :
      NatSeqMinEvenParity (cutBlockMin tailPriorities coupling.cuts) := by
    convert coupling.epochParity using 1
    funext k
    exact coupling.blockMin_eq_epochPriority k
  have htail : NatSeqMinEvenParity tailPriorities :=
    (natSeqMinEvenParity_cutBlockMin tailPriorities coupling.cuts_strictMono
      coupling.cuts_zero).mp hblocks
  have hall : NatSeqMinEvenParity priorities :=
    (natSeqMinEvenParity_shift priorities coupling.start).mp htail
  exact (A.accepts_iff_natSeqMinEvenParity word).mpr hall

end DetParityAutomaton

end DistributedSynthesis
