/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryPhaseHistory

/-! The one-way portion of a phase is one common input/graph word across
the entire next-boundary component. Its roots can stay at the preceding
agreed boundary; no retrospective choice of a new input fiber is needed. -/
namespace Characterisation
open DistributedSynthesis

def phaseClosingCut {I₁ I₂ : Type*} (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat) : Nat :=
  max a (List.length h-(d+1))

def boundaryPhaseWord {I₁ I₂ : Type*} (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat) : EnvHistory I₁ I₂ :=
  (h.take (phaseClosingCut d h a)).drop a

theorem phaseClosingCut_bounds {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a) :
    a ≤ phaseClosingCut d h a ∧ phaseClosingCut d h a < List.length h ∧
      List.length h-phaseClosingCut d h a ≤ d+1 := by
  have := phase.start_lt
  unfold phaseClosingCut
  omega

/-- The finite-history version of the existing phase decomposition. It
retains every physical round of the one-way prefix. -/
theorem boundaryPhaseWord_outgoing {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a) :
    ∀ r ∈ boundaryPhaseWord d h a, r.graph = leaderOutgoingGraph
      (componentLeader P d (History.graphSequence (h.take a))) := by
  letI : Inhabited (RoundRecord I₁ I₂ Graph Unit Unit) :=
    ⟨h[0]'(by have := phase.start_lt; omega)⟩
  let env : Nat → RoundRecord I₁ I₂ Graph Unit Unit := fun n => h.getD n default
  have noBoundary : ∀ n, a < n → n < List.length h →
      leaderBoundary P d (branchNode env n) = false := by
    intro n lower upper
    rw [rollingBranch_take h n (Nat.le_of_lt upper)]
    exact phase.no_boundary n lower upper
  have old : branchNode env a = h.take a := rollingBranch_take h a (Nat.le_of_lt phase.start_lt)
  have bounds := phaseClosingCut_bounds P d h a phase
  intro r member
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp member
  have index : i < phaseClosingCut d h a-a := by
    simpa only [boundaryPhaseWord,List.length_drop,List.length_take,
      min_eq_left (Nat.le_of_lt bounds.2.1)] using hi
  have inside : a+i < List.length h := by omega
  have early : a+i+1+d < List.length h := by
    unfold phaseClosingCut at index
    omega
  have outgoing := leader_phase_oneway_prefix P d (branchNode env) env (fun _ => rfl)
    a (List.length h) noBoundary (a+i) (by omega) early
  rw [old] at outgoing
  change (h.getD (a+i) default).graph = _ at outgoing
  rw [List.getD_eq_getElem h default inside] at outgoing
  simpa only [boundaryPhaseWord,List.getElem_drop,List.getElem_take] using outgoing

/-- Both complete input words determine a history when every graph is the
same outgoing graph. This is equality of histories, not a quotient by time. -/
theorem outgoing_history_inputs_injective {I₁ I₂ : Type*} (p : Proc)
    (h k : EnvHistory I₁ I₂)
    (outH : ∀ r ∈ h, r.graph = leaderOutgoingGraph p)
    (outK : ∀ r ∈ k, r.graph = leaderOutgoingGraph p)
    (one : inputWord .one h = inputWord .one k)
    (two : inputWord .two h = inputWord .two k) : h = k := by
  have len : List.length h = List.length k := by
    simpa only [inputWord,List.length_map] using congrArg List.length one
  apply List.ext_getElem len
  intro i hi hk
  have oi := congrArg (fun w => w[i]?) one
  have ti := congrArg (fun w => w[i]?) two
  simp [inputWord,RoundRecord.input,hi,hk] at oi ti
  have gi := (outH _ (List.getElem_mem hi)).trans (outK _ (List.getElem_mem hk)).symm
  have records : ∀ r s : RoundRecord I₁ I₂ Graph Unit Unit,
      r.inputOne = s.inputOne → r.inputTwo = s.inputTwo → r.graph = s.graph → r = s := by
    intro r s x y g
    cases r; cases s
    simp_all
  exact records _ _ oi ti gi

/-- Every member of the next-boundary component has the same one-way
input/graph word after the previous agreed boundary. Initial roots remain
free to differ, and the short-phase case has the empty common word. -/
theorem boundaryPhaseWord_component {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h))
    (conn : InputConnected P h k) (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a) :
    boundaryPhaseWord d h a = boundaryPhaseWord d k a := by
  have len := inputConnected_length P conn
  have otherPhase := consecutiveLeaderBoundaries_component P closed d recent live conn a phase
  have cut : phaseClosingCut d h a = phaseClosingCut d k a := by simp only [phaseClosingCut,len]
  by_cases short : List.length h-(d+1) ≤ a
  · have cutH : phaseClosingCut d h a = a := max_eq_left short
    have cutK : phaseClosingCut d k a = a := cut.symm.trans cutH
    simp only [boundaryPhaseWord,cutH,cutK,List.drop_take,Nat.sub_self,List.take_zero]
  · have cutH : phaseClosingCut d h a = List.length h-(d+1) := max_eq_right (by omega)
    obtain ⟨s,source⟩ := leaderBoundary_ancestors_in_fiber P closed d recent h live phase.end_boundary
      (phaseClosingCut d h a) (by rw [cutH]; exact le_rfl) k conn
    have one := s.property.2.1
    have two := s.property.2.2
    rw [source] at one two
    have inputs : ∀ p, inputWord p (h.take (phaseClosingCut d h a)) =
        inputWord p (k.take (phaseClosingCut d h a)) →
        inputWord p (boundaryPhaseWord d h a) = inputWord p (boundaryPhaseWord d k a) := by
      intro p eq
      have dropped := congrArg (List.drop a) eq
      simpa only [boundaryPhaseWord,inputWord,List.map_drop,← cut] using dropped
    have leader := componentLeader_history_component P closed d conn a
    apply outgoing_history_inputs_injective
      (componentLeader P d (History.graphSequence (h.take a))) _ _
      (boundaryPhaseWord_outgoing P d h a phase) ?_ (inputs .one one) (inputs .two two)
    intro r member
    rw [leader]
    exact boundaryPhaseWord_outgoing P d k a otherPhase r member

end Characterisation
