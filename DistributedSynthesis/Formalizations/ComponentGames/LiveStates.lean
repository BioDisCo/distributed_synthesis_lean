/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeNonemptiness
import DistributedSynthesis.Library.Automata.FiniteOrbitParity
import DistributedSynthesis.Formalizations.ComponentGames.ExplicitBound

/- Executable liveness, using the existing positional-path theorem and
finite-orbit parity algorithm. No classical decision instance occurs in
these definitions. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation

variable {α : Type} [Fintype α]

theorem accepting_continuation_iff_policy (M : DetParityAutomaton α) (q : M.State) :
    (∃ w, M.AcceptsFrom q w) ↔
      ∃ policy : M.State → α, NatSeqMinEvenParity
        (fun n => M.priority (((fun r => M.step r (policy r))^[n]) q)) := by
  constructor
  · rintro ⟨w,accepts⟩
    exact TreeNonemptiness.exists_positional_path q M.step M.priority (M.runFrom q w)
      w rfl (fun _ => rfl) accepts
  · rintro ⟨policy,parity⟩
    let next := fun r => M.step r (policy r)
    let w : Nat → α := fun n => policy ((next^[n]) q)
    have run : ∀ n, M.runFrom q w n = (next^[n]) q := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [DetParityAutomaton.runFrom, ih, Function.iterate_succ_apply']
    refine ⟨w,?_⟩
    change NatSeqMinEvenParity (fun n => M.priority (M.runFrom q w n))
    simpa only [run] using parity

def acceptingContinuationDecidable (M : DetParityAutomaton α) [DecidableEq M.State]
    (q : M.State) : Decidable (∃ w, M.AcceptsFrom q w) := by
  letI := fun policy : M.State → α =>
    FiniteOrbitParity.parityDecidable (fun r => M.step r (policy r)) q M.priority
  exact decidable_of_iff
    (∃ policy : M.State → α, NatSeqMinEvenParity
      (fun n => M.priority (((fun r => M.step r (policy r))^[n]) q)))
    (accepting_continuation_iff_policy M q).symm

def liveState (M : DetParityAutomaton α) [DecidableEq M.State] (q : M.State) : Bool :=
  @decide (∃ w, M.AcceptsFrom q w) (acceptingContinuationDecidable M q)

theorem liveState_correct (M : DetParityAutomaton α) [DecidableEq M.State] (q : M.State) :
    liveState M q = true ↔ ∃ w, M.AcceptsFrom q w := by
  unfold liveState
  exact @decide_eq_true_iff _ (acceptingContinuationDecidable M q)

end Characterisation.ComponentGames
