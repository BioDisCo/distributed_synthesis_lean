/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.SwitchComponents
import DistributedSynthesis.Formalizations.ComponentGames.CommonView
import DistributedSynthesis.Library.Distributed.DecisionTasks.Model

/- A fixed-round impossibility check using the existing full views and task
specification. The one-round reduction uses the three actual graph updates;
it does not assume a consensus impossibility theorem as an extra axiom. -/
namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation
set_option maxHeartbeats 1600000
variable {V : Type}

/-- Consensus as an instance of the shared decision-task relation. -/
def task (V : Type) : DecisionTasks.Task Proc (fun _ => V) (fun _ => V) where
  allows x o := o .one = o .two ∧ (o .one = x .one ∨ o .one = x .two)

/-- The proposal is repeated as the later input, as in the English proof's
simulation of a decision algorithm with initial proposals only. -/
def proposalHistory (x : Proc → V) (gs : List Graph) : EnvHistory V V :=
  gs.map (fun g => ⟨x .one,x .two,g,(),()⟩)

theorem proposalHistory_append (x : Proc → V) (gs : List Graph) (g : Graph) :
    proposalHistory x (gs++[g]) = proposalHistory x gs ++ [⟨x .one,x .two,g,(),()⟩] := by
  simp [proposalHistory]

theorem proposalViews_append (x : Proc → V) (gs : List Graph) (g : Graph) :
    viewPair (proposalHistory x (gs++[g])) =
      advanceViews (viewPair (proposalHistory x gs)) (⟨x .one,x .two,g,(),()⟩ : RoundRecord V V Graph Unit Unit) := by
  rw [proposalHistory_append]
  exact viewPair_append _ _

/-- The extra own-proposal argument only strengthens the impossibility
claim: it is available even before the first communication round. -/
def TableSolves (D : Nat) (one : V → View V V .one → V)
    (two : V → View V V .two → V) : Prop :=
  ∀ (x : Proc → V) (gs : List Graph), gs.length = D →
    (task V).allows x (fun p => match p with
      | .one => one (x .one) (currentView .one (proposalHistory x gs))
      | .two => two (x .two) (currentView .two (proposalHistory x gs)))

/-- Left/both/right connect the possible last-round decisions. Removing
that round leaves a solving table, contradicting the zero-round case. -/
theorem no_full_table [Nontrivial V] (D : Nat) :
    ¬ ∃ one two, TableSolves (V:=V) D one two := by
  induction D with
  | zero =>
    rintro ⟨one,two,solves⟩
    obtain ⟨a,b,ne⟩ := exists_pair_ne V
    have low := solves (fun _ => a) [] rfl
    have high := solves (fun _ => b) [] rfl
    have mixed := solves (fun p => match p with | .one => a | .two => b) [] rfl
    change one a (.empty .one) = two a (.empty .two) ∧
      (one a (.empty .one) = a ∨ one a (.empty .one) = a) at low
    change one b (.empty .one) = two b (.empty .two) ∧
      (one b (.empty .one) = b ∨ one b (.empty .one) = b) at high
    change one a (.empty .one) = two b (.empty .two) ∧ _ at mixed
    have first := low.2.elim id id
    have second := high.1.symm.trans (high.2.elim id id)
    exact ne (first.symm.trans (mixed.1.trans second))
  | succ D ih =>
    rintro ⟨one,two,solves⟩
    let one' x v := one x (.noRecv v (.inl x))
    let two' x v := two x (.noRecv v (.inr x))
    apply ih
    refine ⟨one',two',fun x gs len => ?_⟩
    have left := solves x (gs++[.left]) (by simp [len])
    have right := solves x (gs++[.right]) (by simp [len])
    have both := solves x (gs++[.both]) (by simp [len])
    simp only [task,currentView,proposalViews_append,advanceViews] at left right both
    change one (x .one) (.noRecv (viewPair (proposalHistory x gs)).1 (.inl (x .one))) =
      two (x .two) (.noRecv (viewPair (proposalHistory x gs)).2 (.inr (x .two))) ∧ _
    exact ⟨right.1.trans (both.1.symm.trans left.1),right.2⟩

end Characterisation.ComponentGames.Consensus
