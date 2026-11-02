/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingSourceAlignment

/-! One local implementation for windows with comparable input-tree
sources. The windows may start at arbitrarily late and different rounds. -/
namespace Characterisation
open DistributedSynthesis

-- The parent project's getD-prefix helpers are private. This uses the same
-- list-prefix identity without changing their visibility or the parent files.
theorem rollingBranch_take {B : Type} [Inhabited B]
    (word : List B) (n : Nat) (within : n ≤ word.length) :
    branchNode (fun i => word.getD i default) n = word.take n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [branchNode,ih (by omega),List.getD_eq_getElem word default (by omega),
      List.take_add_one,List.getElem?_eq_getElem (by omega)]
    rfl

section Banks
variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
variable (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
variable (rep : RepresentsInputShape past shape)
variable (L : Nat) (depth : ∀ h, List.length (past h) = L)
variable (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
variable (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
variable (overlap : ∀ node r h, RollingClosingOverlap (banks node h)
  (banks (node ++ [r]) h) (r.2,r.1,.right))
variable (coherent : ∀ node, ClosingBankCoherent shape (banks node))

include rep depth leaders coherent in
/-- A bank at an arbitrary input-tree node has a local implementation on
its actual source histories, with their original absolute depths. -/
theorem rollingBank_node_local (node : List (I₂ × I₁)) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ h future (t : Fin (D+1)),
      σ.one (currentView .one (closingEntryHistory (rollingSourceHistory past node h) future t.val)) =
          (closingPlanEntry (banks node h) future t).1 ∧
      σ.two (currentView .two (closingEntryHistory (rollingSourceHistory past node h) future t.val)) =
          (closingPlanEntry (banks node h) future t).2 := by
  obtain ⟨σ,correct⟩ := closingBankCoherent_local (rollingSourceHistory past node) shape
    (rollingSourceHistory_shape past shape rep leaders node) (L+node.length)
    (fun h => by rw [rollingSourceHistory_length,depth]) (banks node) (coherent node)
  exact ⟨σ,fun h future t => correct h ((),⟨t,fun j => future j.val⟩)⟩

variable [Inhabited I₁] [Inhabited I₂]

include rep depth leaders overlap coherent in
/-- One local strategy implements a source bank and every still-covered
entry of a later bank on the same input-tree branch. The same strategy is
used for all roots and all arbitrary closing continuations of both banks. -/
theorem rollingBanks_extension_local (node extra : List (I₂ × I₁)) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ h future (t : Fin (D+1)),
        σ.one (currentView .one (closingEntryHistory (rollingSourceHistory past node h) future t.val)) =
            (closingPlanEntry (banks node h) future t).1 ∧
        σ.two (currentView .two (closingEntryHistory (rollingSourceHistory past node h) future t.val)) =
            (closingPlanEntry (banks node h) future t).2) ∧
      (∀ h future (t : Fin (D+1)), extra.length+t.val < D+1 →
        σ.one (currentView .one (closingEntryHistory (rollingSourceHistory past (node++extra) h) future t.val)) =
            (closingPlanEntry (banks (node++extra) h) future t).1 ∧
        σ.two (currentView .two (closingEntryHistory (rollingSourceHistory past (node++extra) h) future t.val)) =
            (closingPlanEntry (banks (node++extra) h) future t).2) := by
  obtain ⟨σ,correct⟩ := rollingBank_node_local past shape rep L depth leaders banks coherent node
  refine ⟨σ,correct,fun h future t within => ?_⟩
  let env : Nat → I₂ × I₁ := fun n => extra.getD n default
  have branch : branchNode env extra.length = extra := by
    simpa only [List.take_length] using rollingBranch_take extra extra.length le_rfl
  let joined : Nat → I₁ × I₂ × Graph := fun n =>
    if n < extra.length then ((env n).2,(env n).1,.right) else future (n-extra.length)
  have follows : ∀ n, n < extra.length → joined n = ((env n).2,(env n).1,.right) := by
    intro n hn
    simp only [joined,if_pos hn]
  have tail : (fun n => joined (extra.length+n)) = future := by
    funext n
    simp only [joined,Nat.not_lt.mpr (Nat.le_add_right _ _),if_false,Nat.add_sub_cancel_left]
  have output := rollingBanks_transport banks overlap node h env joined extra.length t.val within follows
  have history := rollingSourceHistory_closing_split past node h env joined extra.length t.val follows
  rw [branch,tail] at output history
  have result := correct h joined ⟨extra.length+t.val,within⟩
  rw [history,output] at result
  exact result

include rep depth leaders overlap coherent in
/-- Comparable source nodes and equal actual views force equal
prescriptions. The horizon bound follows from equality of absolute output
rounds; it is not an additional assumption about the phase duration. -/
theorem rollingBanks_aligned_agree (p : Proc)
    (node word : List (I₂ × I₁)) (isPrefix : node = word.take node.length) (h k : H)
    (future other : Nat → I₁ × I₂ × Graph) (t u : Fin (D+1))
    (same : currentView p (closingEntryHistory (rollingSourceHistory past node h) future t.val) =
      currentView p (closingEntryHistory (rollingSourceHistory past word k) other u.val)) :
    match p with
    | .one => (closingPlanEntry (banks node h) future t).1 = (closingPlanEntry (banks word k) other u).1
    | .two => (closingPlanEntry (banks node h) future t).2 = (closingPlanEntry (banks word k) other u).2 := by
  obtain ⟨extra,rfl⟩ := List.prefix_iff_eq_take.mpr isPrefix
  have time := closingEntryHistory_same_round p _ _ future other t.val u.val same
  simp only [rollingSourceHistory_length,depth,List.length_append] at time
  have within : extra.length+u.val < D+1 := by have := t.isLt; omega
  obtain ⟨σ,first,later⟩ := rollingBanks_extension_local past shape rep L depth leaders banks overlap coherent node extra
  have one := first h future t
  have two := later k other u within
  cases p
  · exact one.1.symm.trans ((congrArg σ.one same).trans two.1)
  · exact one.2.symm.trans ((congrArg σ.two same).trans two.2)

include rep depth leaders overlap coherent in
/-- All receiver prescriptions in the unbounded family of closing windows
agree on equal actual receiver views. This includes incomparable-looking
input threads: source recovery makes their relevant nodes comparable. -/
theorem rollingBanks_receiver_agree
    (node word : List (I₂ × I₁)) (h k : H)
    (future other : Nat → I₁ × I₂ × Graph) (t u : Fin (D+1))
    (same : currentView .two (closingEntryHistory (rollingSourceHistory past node h) future t.val) =
      currentView .two (closingEntryHistory (rollingSourceHistory past word k) other u.val)) :
    (closingPlanEntry (banks node h) future t).2 = (closingPlanEntry (banks word k) other u).2 := by
  have orderedCase : ∀ (node word : List (I₂ × I₁)) (h k : H)
      (future other : Nat → I₁ × I₂ × Graph) (t u : Fin (D+1)),
      node.length ≤ word.length →
      currentView .two (closingEntryHistory (rollingSourceHistory past node h) future t.val) =
        currentView .two (closingEntryHistory (rollingSourceHistory past word k) other u.val) →
      (closingPlanEntry (banks node h) future t).2 = (closingPlanEntry (banks word k) other u).2 := by
    intro node word h k future other t u ordered same
    have aligned := receiver_windows_source_alignment past L depth leaders node word h k _ _ ordered same
    exact rollingBanks_aligned_agree past shape rep L depth leaders banks overlap coherent .two
      node word aligned.2 h k future other t u same
  rcases Nat.le_total node.length word.length with ordered | ordered
  · exact orderedCase node word h k future other t u ordered same
  · exact (orderedCase word node k h other future u t ordered same.symm).symm

end Banks
end Characterisation
