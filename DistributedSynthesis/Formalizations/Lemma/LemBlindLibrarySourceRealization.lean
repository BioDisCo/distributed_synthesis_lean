/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlindLibraryParitySynthesis

/-!
# Only blind summaries are needed for parity replacement of receive behavior

A winning perfect-recall strategy gives an accepting prescription tree over
any library realizing its blind updates and outputs. No receive congruence
is required: receive outputs and new summaries are chosen with the full
history in this semantic tree. For a finite library, joint positionalization
then replaces those history-dependent choices and yields a finite winner.

This theorem does not assert that the named strategy has finite blind
summaries. Finding a winning replacement that does remains open.
-/

namespace DistributedSynthesis
namespace BlindControllerLibrary
open DetParityAutomaton

universe u v x y c₁ c₂ s
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (L : BlindControllerLibrary.{u,v,x,y,c₁,c₂} In₁ In₂ Out₁ Out₂)
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-- The two blind laws are required only at generated histories. There is
deliberately no finite-summary law for either receive transition. -/
structure RealizesBlind where
  one : View In₁ In₂ .one → L.OneControl
  two : View In₁ In₂ .two → L.TwoControl
  initialOne : one (.empty .one) = L.initialOne
  initialTwo : two (.empty .two) = L.initialTwo
  noRecvOne : ∀ h, StrategyGeneratedPrefix strategy h → ∀ i,
    L.noRecvOne (one (currentView .one h)) i =
      (one (.noRecv (currentView .one h) (.inl i)),
        strategy.one (.noRecv (currentView .one h) (.inl i)))
  noRecvTwo : ∀ h, StrategyGeneratedPrefix strategy h → ∀ j,
    L.noRecvTwo (two (currentView .two h)) j =
      (two (.noRecv (currentView .two h) (.inr j)),
        strategy.two (.noRecv (currentView .two h) (.inr j)))

namespace RealizesBlind
variable {L strategy}
variable (R : L.RealizesBlind strategy)
variable (A : DetParityAutomaton.{max u v x y,s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))

def state (h : History In₁ In₂ Graph Out₁ Out₂) : L.State A :=
  ((R.one (currentView .one h),R.two (currentView .two h)),h.foldl A.step A.initial)

def move (h : History In₁ In₂ Graph Out₁ Out₂) : L.Move := fun i j ↦
  let one := View.recv (currentView .one h) (.inl i) (currentView .two h) (.inr j)
  let two := View.recv (currentView .two h) (.inr j) (currentView .one h) (.inl i)
  ((R.one one,strategy.one one),(R.two two,strategy.two two))

theorem responses_eq (h : History In₁ In₂ Graph Out₁ Out₂)
    (hg : StrategyGeneratedPrefix strategy h) (e : EnvironmentRound In₁ In₂) :
    L.responses A (R.state A h) (R.move h) e =
      ((R.one (nextView .one h e),strategy.one (nextView .one h e)),
        (R.two (nextView .two h e),strategy.two (nextView .two h e))) := by
  have h₁ := R.noRecvOne h hg e.inputOne
  have h₂ := R.noRecvTwo h hg e.inputTwo
  cases he : e.graph <;>
    simp [responses, state, move, nextView, advanceViewsWithEnvironment,
      currentView, he, currentView] at h₁ h₂ ⊢ <;>
    simp_all only

theorem record_eq (h : History In₁ In₂ Graph Out₁ Out₂)
    (hg : StrategyGeneratedPrefix strategy h) (e : EnvironmentRound In₁ In₂) :
    L.record A (R.state A h) (R.move h) e = nextRound strategy h e := by
  simp only [record, R.responses_eq A h hg e]
  rfl

theorem state_step (h : History In₁ In₂ Graph Out₁ Out₂)
    (hg : StrategyGeneratedPrefix strategy h) (e : EnvironmentRound In₁ In₂) :
    R.state A (History.append h (nextRound strategy h e)) =
      L.next A (R.state A h) (R.move h) e := by
  simp only [next, R.responses_eq A h hg e, R.record_eq A h hg e]
  simp only [state, currentView, viewPair_append]
  cases he : e.graph <;>
    simp [advanceViews, nextRound,
      nextView, advanceViewsWithEnvironment, he, History.append, List.foldl_append]

private theorem prefix_on_branch (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    executionPrefixFromList strategy (branchNode env n) = executionPrefix strategy env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change executionPrefixFromList strategy (branchNode env n ++ [env n]) = _
    rw [executionPrefixFromList_snoc, ih]
    rfl

private theorem state_on_execution (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (R.state A (executionPrefix strategy env n)).2 = A.run (execution strategy env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [executionPrefix_succ]
    change (History.append (executionPrefix strategy env n)
      (nextRound strategy (executionPrefix strategy env n) (env n))).foldl A.step A.initial = _
    simp only [History.append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [run_succ, execution_apply]
    exact congrArg (fun q ↦ A.step q (nextRound strategy (executionPrefix strategy env n) (env n))) ih

include R in
/-- The accepted tree is supplied by the winning strategy using only the
blind realization laws. Its receive prescriptions may be history-dependent. -/
theorem accepting_tree (hwin : ∀ env, A.Accepts (execution strategy env)) :
    L.HasAcceptingTree A := by
  refine ⟨fun node ↦ R.move (executionPrefixFromList strategy node),
    fun node ↦ R.state A (executionPrefixFromList strategy node), ⟨?_, ?_⟩, ?_⟩
  · simp [state, initial, currentView, viewPair, R.initialOne, R.initialTwo]
  · intro node e
    dsimp only
    rw [executionPrefixFromList_snoc]
    exact R.state_step A _ (strategyGeneratedPrefix_executionPrefixFromList strategy node) e
  · intro env
    have heq :
        (fun n ↦ A.priority (R.state A (executionPrefixFromList strategy (branchNode env n))).2) =
        (fun n ↦ A.priority (A.run (execution strategy env) n)) := by
      funext n
      rw [prefix_on_branch, state_on_execution]
    rw [heq]
    exact hwin env

variable [Fintype L.OneControl] [Fintype L.TwoControl]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [Inhabited Out₁] [Inhabited Out₂]

include R in
/-- Finite blind summaries suffice; receive summaries need not be congruent
and no shared rank certificate is an extra hypothesis. -/
theorem finite_winner (hwin : ∀ env, A.Accepts (execution strategy env)) :
    ∃ C : FinitePairedPhysicalController.{u,v,x,y,max (max c₁ s) x,max (max c₂ s) y}
      In₁ In₂ Out₁ Out₂, ∀ env,
      A.Accepts (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) :=
  L.exists_winning_physical_controller A (R.accepting_tree A hwin)

end RealizesBlind
end BlindControllerLibrary
end DistributedSynthesis
