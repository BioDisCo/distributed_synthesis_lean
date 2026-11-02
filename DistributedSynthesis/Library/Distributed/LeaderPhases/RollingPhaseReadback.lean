/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingAlignedReadback

/-! A single local strategy implements the entire unbounded family of
closing banks of a fixed leader phase. Every prescribed output keeps its
absolute round and its actual private-input view. -/
namespace Characterisation
open DistributedSynthesis

/-- An outgoing suffix increases silent age by exactly its physical length. -/
theorem outgoing_suffix_silentAge {I₁ I₂ : Type*} (p : Proc)
    (h u : EnvHistory I₁ I₂) (outgoing : ∀ r ∈ u, r.graph = leaderOutgoingGraph p) :
    silentAge (currentView p (h++u)) = silentAge (currentView p h) + List.length u := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u r ih =>
    have last := outgoing r (by simp)
    have old : ∀ s ∈ u, s.graph = leaderOutgoingGraph p := fun s hs => outgoing s (by simp [hs])
    rw [← List.append_assoc,leader_view_append_outgoing p _ r last]
    simp only [silentAge,ih old,List.length_append,List.length_singleton,Nat.add_assoc]

/-- The leader has no receptions along the pair-input source word. -/
theorem rollingSourceHistory_leader_age {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (node : List (I₂ × I₁)) (h : H) :
    silentAge (currentView .one (rollingSourceHistory past node h)) =
      silentAge (currentView .one (past h)) + node.length := by
  have outgoing : ∀ r ∈ rightInputHistory node, r.graph = leaderOutgoingGraph .one := by
    intro r member
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp member
    rfl
  simpa only [rollingSourceHistory,rightInputHistory,List.length_map] using
    outgoing_suffix_silentAge .one (past h) (rightInputHistory node) outgoing

theorem closingEntryHistory_congr {I₁ I₂ : Type*} (h : EnvHistory I₁ I₂)
    (future other : Nat → I₁ × I₂ × Graph) (t : Nat)
    (same : ∀ n, n ≤ t → future n = other n) :
    closingEntryHistory h future t = closingEntryHistory h other t := by
  unfold closingEntryHistory
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [same i.val (Nat.le_of_lt_succ i.isLt)]

section Banks
variable {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable [Inhabited I₁] [Inhabited I₂]
variable [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
variable (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
variable (rep : RepresentsInputShape past shape)
variable (L : Nat) (depth : ∀ h, List.length (past h) = L)
variable (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
variable (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
variable (leader : SenderBlockStrategy I₁ O₁)
variable (overlap : ∀ node r h, RollingClosingOverlap (banks node h)
  (banks (node ++ [r]) h) (r.2,r.1,.right))
variable (coherent : ∀ node, ClosingBankCoherent shape (banks node))
variable (first : ∀ node (r : I₂ × I₁) h,
  (closingPlanEntry (banks node h) (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩).1 =
    leader (senderWord node) r.2)

include leaders overlap first in
omit [Inhabited I₁] [Inhabited I₂] [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂] in
private theorem finite_outgoing_leader_agree
    (node word : List (I₂ × I₁)) (h k : H)
    (future other : Nat → I₁ × I₂ × Graph) (t u : Fin (D+1))
    (outgoing : ∀ n, n ≤ t.val → (future n).2.2 = .right)
    (outgoingOther : ∀ n, n ≤ u.val → (other n).2.2 = .right)
    (same : currentView .one (closingEntryHistory (rollingSourceHistory past node h) future t.val) =
      currentView .one (closingEntryHistory (rollingSourceHistory past word k) other u.val)) :
    (closingPlanEntry (banks node h) future t).1 = (closingPlanEntry (banks word k) other u).1 := by
  let env : Nat → I₂ × I₁ := fun n => ((future n).2.1,(future n).1)
  let envOther : Nat → I₂ × I₁ := fun n => ((other n).2.1,(other n).1)
  have eqFuture : ∀ n, n ≤ t.val → future n = ((env n).2,(env n).1,.right) := by
    intro n hn
    exact Prod.ext rfl (Prod.ext rfl (outgoing n hn))
  have eqOther : ∀ n, n ≤ u.val → other n = ((envOther n).2,(envOther n).1,.right) := by
    intro n hn
    exact Prod.ext rfl (Prod.ext rfl (outgoingOther n hn))
  rw [closingEntryHistory_congr _ _ _ _ eqFuture,closingEntryHistory_congr _ _ _ _ eqOther] at same
  rw [closingPlanEntry_congr _ _ _ _ eqFuture,closingPlanEntry_congr _ _ _ _ eqOther]
  exact rollingBanks_outgoing_leader_agree past leaders banks leader overlap first
    node word h k env envOther t.val u.val t.isLt u.isLt same

include rep depth leaders overlap coherent first in
private theorem rollingBanks_leader_agree_ordered
    (node word : List (I₂ × I₁)) (h k : H)
    (future other : Nat → I₁ × I₂ × Graph) (t u : Fin (D+1))
    (ordered : node.length ≤ word.length)
    (same : currentView .one (closingEntryHistory (rollingSourceHistory past node h) future t.val) =
      currentView .one (closingEntryHistory (rollingSourceHistory past word k) other u.val)) :
    (closingPlanEntry (banks node h) future t).1 = (closingPlanEntry (banks word k) other u).1 := by
  let tail : EnvHistory I₁ I₂ := List.ofFn (fun i : Fin (t.val+1) =>
    let r := future i.val
    ⟨r.1,r.2.1,r.2.2,(),()⟩)
  let otherTail : EnvHistory I₁ I₂ := List.ofFn (fun i : Fin (u.val+1) =>
    let r := other i.val
    ⟨r.1,r.2.1,r.2.2,(),()⟩)
  have sameHist : currentView .one (rollingSourceHistory past node h ++ tail) =
      currentView .one (rollingSourceHistory past word k ++ otherTail) := same
  rcases equal_view_source_or_outgoing .one (rollingSourceHistory past node h) tail _ sameHist with recovered | outgoing
  · rw [List.take_append_of_le_length (by rw [rollingSourceHistory_length,rollingSourceHistory_length,depth,depth]; omega)] at recovered
    have aligned := rollingSourceHistory_prefix_coordinates past L depth node word h k recovered
    exact rollingBanks_aligned_agree past shape rep L depth leaders banks overlap coherent .one
      node word aligned.2 h k future other t u same
  · have tailLength : List.length tail = t.val+1 := List.length_ofFn
    have otherLength : List.length otherTail = u.val+1 := List.length_ofFn
    have age := outgoing_suffix_silentAge .one (rollingSourceHistory past node h) tail outgoing
    rw [rollingSourceHistory_leader_age,tailLength] at age
    have time := closingEntryHistory_same_round .one _ _ future other t.val u.val same
    simp only [rollingSourceHistory_length,depth] at time
    have otherSilent : List.length otherTail ≤
        silentAge (currentView .one (rollingSourceHistory past word k ++ otherTail)) := by
      rw [← sameHist,age,otherLength]
      omega
    have outgoingOther := silent_suffix_outgoing .one (rollingSourceHistory past word k) otherTail otherSilent
    have graphs : ∀ n, n ≤ t.val → (future n).2.2 = .right := by
      intro n hn
      exact outgoing _ (List.mem_ofFn.mpr ⟨⟨n,by omega⟩,rfl⟩)
    have otherGraphs : ∀ n, n ≤ u.val → (other n).2.2 = .right := by
      intro n hn
      exact outgoingOther _ (List.mem_ofFn.mpr ⟨⟨n,by omega⟩,rfl⟩)
    exact finite_outgoing_leader_agree past leaders banks leader overlap first
      node word h k future other t u graphs otherGraphs same

include rep depth leaders overlap coherent first in
/-- All leader prescriptions agree on equal actual leader views, including
windows with receptions and windows started on different input threads. -/
theorem rollingBanks_leader_agree
    (node word : List (I₂ × I₁)) (h k : H)
    (future other : Nat → I₁ × I₂ × Graph) (t u : Fin (D+1))
    (same : currentView .one (closingEntryHistory (rollingSourceHistory past node h) future t.val) =
      currentView .one (closingEntryHistory (rollingSourceHistory past word k) other u.val)) :
    (closingPlanEntry (banks node h) future t).1 = (closingPlanEntry (banks word k) other u).1 := by
  rcases Nat.le_total node.length word.length with ordered | ordered
  · exact rollingBanks_leader_agree_ordered past shape rep L depth leaders banks leader overlap coherent first
      node word h k future other t u ordered same
  · exact (rollingBanks_leader_agree_ordered past shape rep L depth leaders banks leader overlap coherent first
      word node k h other future u t ordered same.symm).symm

include rep depth leaders overlap coherent first in
/-- One strategy pair implements every entry of every bank throughout the
unbounded leader phase. No bound on the source word or common-window
hypothesis remains. Closing graphs and private inputs are arbitrary. -/
theorem rollingBanks_phase_local :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ node h future (t : Fin (D+1)),
      σ.one (currentView .one (closingEntryHistory (rollingSourceHistory past node h) future t.val)) =
          (closingPlanEntry (banks node h) future t).1 ∧
      σ.two (currentView .two (closingEntryHistory (rollingSourceHistory past node h) future t.val)) =
          (closingPlanEntry (banks node h) future t).2 := by
  let hist (j : List (I₂ × I₁) × H) (s : (Nat → I₁ × I₂ × Graph) × Fin (D+1)) :=
    closingEntryHistory (rollingSourceHistory past j.1 j.2) s.1 s.2.val
  let out (j : List (I₂ × I₁) × H) (s : (Nat → I₁ × I₂ × Graph) × Fin (D+1)) :=
    closingPlanEntry (banks j.1 j.2) s.1 s.2
  have compatible : TablesCompatible hist out := by
    constructor
    · intro j k s r same
      exact rollingBanks_leader_agree past shape rep L depth leaders banks leader overlap coherent first
        j.1 k.1 j.2 k.2 s.1 r.1 s.2 r.2 same
    · intro j k s r same
      exact rollingBanks_receiver_agree past shape rep L depth leaders banks overlap coherent
        j.1 k.1 j.2 k.2 s.1 r.1 s.2 r.2 same
  obtain ⟨σ,correct⟩ := (tables_compatible_iff_local hist out).mp compatible
  exact ⟨σ,fun node h future t => correct (node,h) (future,t)⟩

include rep depth leaders overlap coherent first in
/-- The semantic readback implements the complete finite plans, not just
entries presented through one particular infinite extension. -/
theorem rollingBanks_phase_plans :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ node h,
      closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) = banks node h := by
  obtain ⟨σ,correct⟩ := rollingBanks_phase_local past shape rep L depth leaders banks leader overlap coherent first
  refine ⟨σ,fun node h => ?_⟩
  funext s
  rcases s with ⟨⟨⟩,t,word⟩
  let future : Nat → I₁ × I₂ × Graph := fun n =>
    if hn : n < t.val+1 then word ⟨n,hn⟩ else (default,default,.right)
  have scenario : ((),⟨t,fun j => future j.val⟩) =
      (((),⟨t,word⟩) : ClosingScenario I₁ I₂ (D+1)) := by
    apply Prod.ext
    · rfl
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext j
    simp only [future,dif_pos j.isLt]
  have result := correct node h future t
  have pair : closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1)
        ((),⟨t,fun j => future j.val⟩) =
      banks node h ((),⟨t,fun j => future j.val⟩) := Prod.ext result.1 result.2
  simpa only [scenario] using pair

end Banks
end Characterisation
