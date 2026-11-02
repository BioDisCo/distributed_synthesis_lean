/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropDynhier
import Mathlib.Data.List.Induction

/-!
# History embedding

This file formalizes the core recoverability content of Lemma
`lem:historyembedding` from `paper.tex`.
-/

namespace DistributedSynthesis

universe u v x y

/--
Accumulate the non-fringe views seen by process `p` along a history in
chronological order.
-/
def nonFringeSequenceStep
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (state : (View In₁ In₂ Proc.one × View In₁ In₂ Proc.two) × List (NonFringeView In₁ In₂ p))
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (View In₁ In₂ Proc.one × View In₁ In₂ Proc.two) × List (NonFringeView In₁ In₂ p) :=
  let views' := advanceViews state.1 r
  let nf := match p with
    | .one => views'.1.nonFringe
    | .two => views'.2.nonFringe
  (views', state.2 ++ [nf])

/-- The sequence `N_p^0(h), ..., N_p^t(h)` along a history of length `t+1`. -/
def nonFringeSequence
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc) (h : History In₁ In₂ Graph Out₁ Out₂) :
    List (NonFringeView In₁ In₂ p) :=
  (h.foldl (nonFringeSequenceStep p) ((.empty Proc.one, .empty Proc.two), [])).2

/-- Recover the earlier same-process non-fringe views by repeated stripping. -/
def recoverPreviousNonFringeChain
    {In₁ : Type u} {In₂ : Type v} (n : Nat) (nf : NonFringeView In₁ In₂ p) :
    List (NonFringeView In₁ In₂ p) :=
  match n with
  | 0 => []
  | Nat.succ m =>
      let prev := nf.previousNonFringe
      recoverPreviousNonFringeChain m prev ++ [prev]

/-- Recover the full same-process non-fringe history ending at the current one. -/
def recoverNonFringeSequenceFromCurrent
    {In₁ : Type u} {In₂ : Type v} (n : Nat) (nf : NonFringeView In₁ In₂ p) :
    List (NonFringeView In₁ In₂ p) :=
  recoverPreviousNonFringeChain n nf ++ [nf]

/-- Recover the trailing pair carried inside a receiver's quad, when present. -/
def recoverReceiverSubtuple
    {In₁ : Type u} {In₂ : Type v} {receiver : Proc}
    (nf : NonFringeView In₁ In₂ receiver) :
    Option (NonFringeView In₁ In₂ receiver.other) :=
  match nf with
  | .quad _ _ prev input => some (.pair prev input)
  | .empty _ => none
  | .pair _ _ => none

theorem nonFringeSequenceState_views
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  (p : Proc)
  (views : View In₁ In₂ Proc.one × View In₁ In₂ Proc.two)
  (acc : List (NonFringeView In₁ In₂ p))
  (h : History In₁ In₂ Graph Out₁ Out₂) :
  (h.foldl (nonFringeSequenceStep p) (views, acc)).1 = h.foldl advanceViews views := by
  induction h generalizing views acc with
  | nil =>
      rfl
  | cons r h ih =>
    simp [nonFringeSequenceStep, ih, advanceViews]

theorem nonFringeSequence_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    nonFringeSequence p (History.append h r) =
      nonFringeSequence p h ++ [currentNonFringe p (History.append h r)] := by
  cases p <;>
    simp [nonFringeSequence, History.append, List.foldl_append, nonFringeSequenceStep,
      nonFringeSequenceState_views (p := Proc.one) (views := (View.empty Proc.one, View.empty Proc.two))
        (acc := []) h,
      nonFringeSequenceState_views (p := Proc.two) (views := (View.empty Proc.one, View.empty Proc.two))
        (acc := []) h,
      currentNonFringe, currentView, viewPair, advanceViews]

theorem previousView_from_nonFringe_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentNonFringe p (History.append h r)).previousView = currentView p h := by
  cases p <;> cases hGraph : r.graph <;>
    simp [currentNonFringe, NonFringeView.previousView, View.nonFringe, hGraph]

theorem previousNonFringe_from_nonFringe_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentNonFringe p (History.append h r)).previousNonFringe = currentNonFringe p h := by
  cases p <;> cases hGraph : r.graph <;>
    simp [currentNonFringe, NonFringeView.previousNonFringe, NonFringeView.previousView,
      View.nonFringe, hGraph]

theorem previousReceiptTag_from_nonFringe_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentNonFringe p (History.append h r)).previousView.receiptTag =
      (currentView p h).receiptTag := by
  cases p <;> cases hGraph : r.graph <;>
    simp [currentNonFringe, NonFringeView.previousView, View.nonFringe, View.receiptTag, hGraph]

theorem recoverPreviousNonFringeChain_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    recoverPreviousNonFringeChain (History.length h) (currentNonFringe p (History.append h r)) =
      nonFringeSequence p h := by
  induction h using List.reverseRecOn generalizing r with
  | nil =>
      simp [recoverPreviousNonFringeChain, nonFringeSequence, History.length, History.empty]
  | append_singleton h r' ih =>
      simp [History.length, recoverPreviousNonFringeChain]
      rw [show (currentView p (History.append (h ++ [r']) r)).nonFringe.previousNonFringe =
        currentNonFringe p (History.append h r') by
        exact previousNonFringe_from_nonFringe_append p (History.append h r') r]
      rw [show nonFringeSequence p (h ++ [r']) =
          nonFringeSequence p h ++ [currentNonFringe p (History.append h r')] by
            simpa [History.append] using nonFringeSequence_append p h r']
      exact congrArg (fun xs => xs ++ [currentNonFringe p (History.append h r')]) (ih r')

theorem recoverNonFringeSequenceFromCurrent_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    recoverNonFringeSequenceFromCurrent (History.length h) (currentNonFringe p (History.append h r)) =
      nonFringeSequence p (History.append h r) := by
  rw [recoverNonFringeSequenceFromCurrent, recoverPreviousNonFringeChain_append, nonFringeSequence_append]

theorem recoverReceiverSubtuple_right
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hright : r.graph = .right) :
    recoverReceiverSubtuple (receiver := Proc.two) (currentNonFringe Proc.two (History.append h r)) =
      some (currentNonFringe Proc.one (History.append h r)) := by
  cases hGraph : r.graph with
  | left =>
      simp [hGraph] at hright
  | right =>
      rw [currentNonFringe, currentView_two_append, currentNonFringe, currentView_one_append, hGraph]
      rfl
  | both =>
      simp [hGraph] at hright

theorem recoverReceiverSubtuple_left
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hleft : r.graph = .left) :
    recoverReceiverSubtuple (receiver := Proc.one) (currentNonFringe Proc.one (History.append h r)) =
      some (currentNonFringe Proc.two (History.append h r)) := by
  cases hGraph : r.graph with
  | left =>
      rw [currentNonFringe, currentView_one_append, currentNonFringe, currentView_two_append, hGraph]
      rfl
  | right =>
      simp [hGraph] at hleft
  | both =>
      simp [hGraph] at hleft

/--
Paper-facing packaged form of `lem:historyembedding`.
-/
theorem history_embedding
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    NonFringeView.previousView (currentNonFringe p (History.append h r)) = currentView p h ∧
      NonFringeView.previousNonFringe (currentNonFringe p (History.append h r)) = currentNonFringe p h ∧
      recoverPreviousNonFringeChain (History.length h) (currentNonFringe p (History.append h r)) =
        nonFringeSequence p h := by
  exact ⟨previousView_from_nonFringe_append p h r,
    previousNonFringe_from_nonFringe_append p h r,
    recoverPreviousNonFringeChain_append p h r⟩

/--
Paper-facing packaged form of Corollary `cor:fullhistory`.
-/
theorem full_history_value_recovery
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (r.graph = .right →
      recoverReceiverSubtuple (receiver := Proc.two) (currentNonFringe Proc.two (History.append h r)) =
        some (currentNonFringe Proc.one (History.append h r)) ∧
      Option.map (recoverNonFringeSequenceFromCurrent (History.length h))
          (recoverReceiverSubtuple (receiver := Proc.two) (currentNonFringe Proc.two (History.append h r))) =
        some (nonFringeSequence Proc.one (History.append h r)) ∧
      recoverPreviousNonFringeChain (History.length h) (currentNonFringe Proc.two (History.append h r)) =
        nonFringeSequence Proc.two h) ∧
    (r.graph = .left →
      recoverReceiverSubtuple (receiver := Proc.one) (currentNonFringe Proc.one (History.append h r)) =
        some (currentNonFringe Proc.two (History.append h r)) ∧
      Option.map (recoverNonFringeSequenceFromCurrent (History.length h))
          (recoverReceiverSubtuple (receiver := Proc.one) (currentNonFringe Proc.one (History.append h r))) =
        some (nonFringeSequence Proc.two (History.append h r)) ∧
      recoverPreviousNonFringeChain (History.length h) (currentNonFringe Proc.one (History.append h r)) =
        nonFringeSequence Proc.one h) := by
  constructor
  · intro hright
    refine ⟨recoverReceiverSubtuple_right h r hright, ?_, recoverPreviousNonFringeChain_append Proc.two h r⟩
    rw [recoverReceiverSubtuple_right h r hright]
    change some (recoverNonFringeSequenceFromCurrent (History.length h)
        (currentNonFringe Proc.one (History.append h r))) =
      some (nonFringeSequence Proc.one (History.append h r))
    exact congrArg some (recoverNonFringeSequenceFromCurrent_append Proc.one h r)
  · intro hleft
    refine ⟨recoverReceiverSubtuple_left h r hleft, ?_, recoverPreviousNonFringeChain_append Proc.one h r⟩
    rw [recoverReceiverSubtuple_left h r hleft]
    change some (recoverNonFringeSequenceFromCurrent (History.length h)
        (currentNonFringe Proc.two (History.append h r))) =
      some (nonFringeSequence Proc.two (History.append h r))
    exact congrArg some (recoverNonFringeSequenceFromCurrent_append Proc.two h r)

end DistributedSynthesis
