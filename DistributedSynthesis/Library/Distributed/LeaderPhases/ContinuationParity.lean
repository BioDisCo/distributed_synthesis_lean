/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ContinuationResidual

/-! Instantiate residual acceptance using the original automaton tail
theorem. The adversary's infinite acceptance is retained in the implication. -/
namespace Characterisation
open DistributedSynthesis

/-- Adapter between the existing physical-prefix fold and automaton run. -/
theorem branchNode_fold_runFrom {Alphabet : Type}
    (A : DetParityAutomaton.{0,0} Alphabet) (q : A.State)
    (trace : Nat → Alphabet) (n : Nat) :
    (branchNode trace n).foldl A.step q = A.runFrom q trace n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [branchNode,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,
      DetParityAutomaton.runFrom]

theorem parity_residualAcceptance {I₁ I₂ O₁ O₂ : Type}
    (A : DetParityAutomaton.{0,0} (ContinuationLetter I₁ I₂ O₁ O₂)) :
    ResidualAcceptance (fun q input output => A.step q (input,output)) A.AcceptsFrom := by
  intro q trace n accepted
  change A.AcceptsFrom ((branchNode trace n).foldl A.step q) (OmegaWord.drop trace n)
  rw [branchNode_fold_runFrom]
  exact (A.acceptsFrom_runFrom_drop_iff q trace n).mpr accepted

/-- Both residual states are updated at each physical input/output letter.
G may be obtained by projecting letters to their communication graph. -/
def guardedContinuationStep {I₁ I₂ O₁ O₂ : Type}
    (G A : DetParityAutomaton.{0,0} (ContinuationLetter I₁ I₂ O₁ O₂))
    (q : G.State × A.State) (input : I₁ × I₂ × Graph) (output : O₁ × O₂) :
    G.State × A.State :=
  (G.step q.1 (input,output),A.step q.2 (input,output))

def guardedContinuationAccept {I₁ I₂ O₁ O₂ : Type}
    (G A : DetParityAutomaton.{0,0} (ContinuationLetter I₁ I₂ O₁ O₂))
    (q : G.State × A.State) (trace : Nat → ContinuationLetter I₁ I₂ O₁ O₂) : Prop :=
  G.AcceptsFrom q.1 trace → A.AcceptsFrom q.2 trace

theorem guardedContinuation_fold {I₁ I₂ O₁ O₂ : Type}
    (G A : DetParityAutomaton.{0,0} (ContinuationLetter I₁ I₂ O₁ O₂))
    (q : G.State × A.State) (trace : Nat → ContinuationLetter I₁ I₂ O₁ O₂) (n : Nat) :
    (branchNode trace n).foldl (fun q r => guardedContinuationStep G A q r.1 r.2) q =
      (G.runFrom q.1 trace n,A.runFrom q.2 trace n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [branchNode,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih]
    rfl

/-- Prefix removal preserves the implication, including for nonclosed
adversaries. The converse direction of the adversary tail theorem is needed. -/
theorem guardedParity_residualAcceptance {I₁ I₂ O₁ O₂ : Type}
    (G A : DetParityAutomaton.{0,0} (ContinuationLetter I₁ I₂ O₁ O₂)) :
    ResidualAcceptance (guardedContinuationStep G A) (guardedContinuationAccept G A) := by
  intro q trace n accepted
  rw [guardedContinuation_fold]
  intro admitted
  apply (A.acceptsFrom_runFrom_drop_iff q.2 trace n).mpr
  apply accepted
  exact (G.acceptsFrom_runFrom_drop_iff q.1 trace n).mp admitted

end Characterisation
