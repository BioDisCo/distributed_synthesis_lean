/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PrefixHoles
import DistributedSynthesis.Library.Distributed.ViewPaths
import Mathlib.Logic.Relation

/-! Actual model views: every connected child component has a unique parent
component. No abstract replacement observation model is used here. -/

namespace Characterisation

open DistributedSynthesis DistributedSynthesis.FullViewPath

def previous {p : Proc} (v : View Unit Unit p) : View Unit Unit p :=
  v.nonFringe.previousView

theorem previous_one (h : List Graph) :
    previous (evaluate h).one = (evaluate h.dropLast).one := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g _ =>
    rw [at_append]
    simp only [List.dropLast_concat]
    cases g <;> rfl

theorem previous_two (h : List Graph) :
    previous (evaluate h).two = (evaluate h.dropLast).two := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g _ =>
    rw [at_append]
    simp only [List.dropLast_concat]
    cases g <;> rfl

def Adjacent (h k : List Graph) : Prop :=
  (evaluate h).one = (evaluate k).one ∨
    (evaluate h).two = (evaluate k).two

theorem adjacent_parent {h k : List Graph} (eqView : Adjacent h k) :
    Adjacent h.dropLast k.dropLast := by
  rcases eqView with eqOne | eqTwo
  · left
    simpa only [previous_one] using congrArg previous eqOne
  · right
    simpa only [previous_two] using congrArg previous eqTwo

def LiveAdjacent (P : List Graph → Prop) (h k : List Graph) : Prop :=
  P h ∧ P k ∧ Adjacent h k

def Connected (P : List Graph → Prop) : List Graph → List Graph → Prop :=
  Relation.ReflTransGen (LiveAdjacent P)

theorem live_parent (P : List Graph → Prop) (closed : PrefixClosed P)
    {h : List Graph} (hh : P h) : P h.dropLast := by
  induction h using List.reverseRecOn with
  | nil => exact hh
  | append_singleton h g _ =>
    simpa only [List.dropLast_concat] using closed h [g] hh

/-- A component cannot join histories belonging to different parent
components. This is the ancestry fact needed for a component-tree compiler. -/
theorem connected_parent (P : List Graph → Prop) (closed : PrefixClosed P)
    {h k : List Graph} (hc : Connected P h k) :
    Connected P h.dropLast k.dropLast := by
  apply Relation.ReflTransGen.lift List.dropLast _ hc
  intro u v huv
  exact ⟨live_parent P closed huv.1, live_parent P closed huv.2.1,
    adjacent_parent huv.2.2⟩

end Characterisation
