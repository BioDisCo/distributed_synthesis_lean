/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback

/-!
# Re-rooting a finite global round machine at a physical suffix

Acceptance arguments for the raw-joint carrier begin after a finite initial
or exceptional prefix.  This file records the generic timing fact needed by
all such arguments: re-rooting the same transition machine at its control
after `start` rounds and feeding it the dropped environment reproduces the
original state and output traces exactly.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- The same finite transition machine with a new proof-side initial state. -/
def reroot (state : G.State) : FiniteGlobalRoundMachine In₁ In₂ where
  State := G.State
  stateFinite := G.stateFinite
  initial := state
  step := G.step

@[simp] theorem reroot_initial (state : G.State) :
    (G.reroot state).initial = state :=
  rfl

@[simp] theorem reroot_step (state source : G.State)
    (round : EnvironmentRound In₁ In₂) :
    (G.reroot state).step source round = G.step source round :=
  rfl

/-- Exact state trace after dropping a finite environment prefix. -/
theorem reroot_globalStateTrace_drop
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : ∀ n : Nat,
    (G.reroot (G.globalStateTrace env start)).globalStateTrace
        (OmegaWord.drop env start) n =
      G.globalStateTrace env (start + n) := by
  intro n
  induction n with
  | zero => simp [reroot]
  | succ n ih =>
      rw [globalStateTrace_succ, ih]
      rw [show start + (n + 1) = (start + n) + 1 by omega]
      rw [globalStateTrace_succ]
      rfl

/-- The Moore-timed physical word of the re-rooted suffix is literally the
dropped physical word of the original machine. -/
theorem reroot_globalMachineTraceWord_drop
    {Out₁ : Type x} {Out₂ : Type y}
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat) :
    (G.reroot (G.globalStateTrace env start)).globalMachineTraceWord
        outputOne outputTwo (OmegaWord.drop env start) =
      OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
        start := by
  funext n
  simp only [globalMachineTraceWord, OmegaWord.drop]
  rw [G.reroot_globalStateTrace_drop env start (n + 1)]
  simp only [Nat.add_assoc]

end FiniteGlobalRoundMachine

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- An accepting suffix of the machine re-rooted at the actual control after
`start` rounds implies acceptance of the original physical word.  The DPA
state is likewise the actual state after the discarded prefix, so no checker
restart is hidden here. -/
theorem accepts_of_rerootedGlobalMachine_acceptsFrom
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (haccepts :
      A.AcceptsFrom
        (A.run (G.globalMachineTraceWord outputOne outputTwo env) start)
        ((G.reroot (G.globalStateTrace env start)).globalMachineTraceWord
          outputOne outputTwo (OmegaWord.drop env start))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  rw [G.reroot_globalMachineTraceWord_drop outputOne outputTwo env start]
    at haccepts
  exact (A.acceptsFrom_runFrom_drop_iff A.initial
    (G.globalMachineTraceWord outputOne outputTwo env) start).mp haccepts

end DetParityAutomaton

end DistributedSynthesis
