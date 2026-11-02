/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# View invariance under the pending bit

This file starts the formalization of Lemma `lem:viewinv` from `paper.tex`.
It proves the first simple one-step invariance facts.
-/

namespace DistributedSynthesis

universe u v x y

/--
Changing a round from `left` to `both` does not change process `1`'s view in
that round, provided the two rounds have the same inputs.
-/
theorem viewinv_oneStep_procOne
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both) :
    currentView Proc.one (History.append h rLeft) =
      currentView Proc.one (History.append h rBoth) := by
  simpa [currentView_one_append, hleft, hboth, hinputOne, hinputTwo]

/--
Changing a round from `right` to `both` does not change process `2`'s view in
that round, provided the two rounds have the same inputs.
-/
theorem viewinv_oneStep_procTwo
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both) :
    currentView Proc.two (History.append h rRight) =
      currentView Proc.two (History.append h rBoth) := by
  simpa [currentView_two_append, hright, hboth, hinputOne, hinputTwo]

/--
If process `1` has the same current view on two prefixes, then appending the
same suffix of `right` rounds preserves that equality.
-/
theorem procOne_eq_preserved_by_right_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂)
    (heq : currentView Proc.one h₁ = currentView Proc.one h₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hsuffix : suffix.Forall (fun r => r.graph = .right)) :
    currentView Proc.one (h₁ ++ suffix) = currentView Proc.one (h₂ ++ suffix) := by
  induction suffix generalizing h₁ h₂ with
  | nil =>
      simpa using heq
  | cons r suffix ih =>
      have hsplit : r.graph = .right ∧ suffix.Forall (fun r => r.graph = .right) := by
        simpa using hsuffix
      have hright : r.graph = .right := hsplit.1
      have hsuffixTail : suffix.Forall (fun r => r.graph = .right) := hsplit.2
      have hstep : currentView Proc.one (History.append h₁ r) = currentView Proc.one (History.append h₂ r) := by
        simp [currentView_one_append, hright, heq]
      simpa [History.append, List.append_assoc] using
        ih (History.append h₁ r) (History.append h₂ r) hstep hsuffixTail

/--
Changing the pending bit from `left` to `both` and then following any shared
suffix of `right` rounds leaves process `1`'s current view unchanged.
-/
theorem viewinv_procOne_right_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right)) :
    currentView Proc.one (History.append h rLeft ++ suffix) =
      currentView Proc.one (History.append h rBoth ++ suffix) := by
  apply procOne_eq_preserved_by_right_suffix
  · exact viewinv_oneStep_procOne h rLeft rBoth hinputOne hinputTwo hleft hboth
  · exact hsuffix

/--
If process `2` has the same current view on two prefixes, then appending the
same suffix of `left` rounds preserves that equality.
-/
theorem procTwo_eq_preserved_by_left_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂)
    (heq : currentView Proc.two h₁ = currentView Proc.two h₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hsuffix : suffix.Forall (fun r => r.graph = .left)) :
    currentView Proc.two (h₁ ++ suffix) = currentView Proc.two (h₂ ++ suffix) := by
  induction suffix generalizing h₁ h₂ with
  | nil =>
      simpa using heq
  | cons r suffix ih =>
      have hsplit : r.graph = .left ∧ suffix.Forall (fun r => r.graph = .left) := by
        simpa using hsuffix
      have hleft : r.graph = .left := hsplit.1
      have hsuffixTail : suffix.Forall (fun r => r.graph = .left) := hsplit.2
      have hstep : currentView Proc.two (History.append h₁ r) = currentView Proc.two (History.append h₂ r) := by
        simp [currentView_two_append, hleft, heq]
      simpa [History.append, List.append_assoc] using
        ih (History.append h₁ r) (History.append h₂ r) hstep hsuffixTail

/--
Changing the pending bit from `right` to `both` and then following any shared
suffix of `left` rounds leaves process `2`'s current view unchanged.
-/
theorem viewinv_procTwo_left_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left)) :
    currentView Proc.two (History.append h rRight ++ suffix) =
      currentView Proc.two (History.append h rBoth ++ suffix) := by
  apply procTwo_eq_preserved_by_left_suffix
  · exact viewinv_oneStep_procTwo h rRight rBoth hinputOne hinputTwo hright hboth
  · exact hsuffix

/-- Taking a prefix of an all-`right` suffix preserves the all-`right` property. -/
theorem forall_right_take
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (n : Nat) :
    (suffix.take n).Forall (fun r => r.graph = .right) := by
  induction suffix generalizing n with
  | nil =>
      simp
  | cons r suffix ih =>
      cases n with
      | zero => simp
      | succ n =>
          have hsplit : r.graph = .right ∧ suffix.Forall (fun r => r.graph = .right) := by
            simpa using hsuffix
          simp [hsplit.1, ih hsplit.2 n]

/-- Taking a prefix of an all-`left` suffix preserves the all-`left` property. -/
theorem forall_left_take
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (n : Nat) :
    (suffix.take n).Forall (fun r => r.graph = .left) := by
  induction suffix generalizing n with
  | nil =>
      simp
  | cons r suffix ih =>
      cases n with
      | zero => simp
      | succ n =>
          have hsplit : r.graph = .left ∧ suffix.Forall (fun r => r.graph = .left) := by
            simpa using hsuffix
          simp [hsplit.1, ih hsplit.2 n]

/--
Paper-style prefix form of the process-`1` pending-bit invariance: every prefix
of a shared all-`right` suffix preserves equality.
-/
theorem viewinv_procOne_right_prefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (n : Nat)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right)) :
    currentView Proc.one (History.append h rLeft ++ suffix.take n) =
      currentView Proc.one (History.append h rBoth ++ suffix.take n) := by
  apply procOne_eq_preserved_by_right_suffix
  · exact viewinv_oneStep_procOne h rLeft rBoth hinputOne hinputTwo hleft hboth
  · exact forall_right_take suffix hsuffix n

/--
Paper-style prefix form of the symmetric process-`2` pending-bit invariance.
-/
theorem viewinv_procTwo_left_prefix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (n : Nat)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left)) :
    currentView Proc.two (History.append h rRight ++ suffix.take n) =
      currentView Proc.two (History.append h rBoth ++ suffix.take n) := by
  apply procTwo_eq_preserved_by_left_suffix
  · exact viewinv_oneStep_procTwo h rRight rBoth hinputOne hinputTwo hright hboth
  · exact forall_left_take suffix hsuffix n

/--
Packaged process-`1` form of `lem:viewinv`: after one `left` versus `both`
choice at the boundary round, every shared suffix of `right` rounds preserves
equality of process `1` views at all later prefix lengths.
-/
theorem viewinv_procOne
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right)) :
    ∀ n : Nat,
      currentView Proc.one (History.append h rLeft ++ suffix.take n) =
        currentView Proc.one (History.append h rBoth ++ suffix.take n) := by
  intro n
  exact viewinv_procOne_right_prefix h rLeft rBoth suffix n hinputOne hinputTwo hleft hboth hsuffix

/--
Packaged symmetric process-`2` form of `lem:viewinv`.
-/
theorem viewinv_procTwo
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left)) :
    ∀ n : Nat,
      currentView Proc.two (History.append h rRight ++ suffix.take n) =
        currentView Proc.two (History.append h rBoth ++ suffix.take n) := by
  intro n
  exact viewinv_procTwo_left_prefix h rRight rBoth suffix n hinputOne hinputTwo hright hboth hsuffix

end DistributedSynthesis
