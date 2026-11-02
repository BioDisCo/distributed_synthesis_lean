/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableSimulation
import DistributedSynthesis.Formalizations.ComponentGames.ComponentSoundness
import DistributedSynthesis.Library.Distributed.LeaderPhases.InputKnowledge

namespace Characterisation.ComponentGames.ExecutableReadback
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open HistoryGame ExecutableHistories
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def successors (m : Move I₁ I₂ O₁ O₂ Q D) : Finset (Position I₁ I₂ Q D) :=
  ((Finset.univ.filter (fun K : Finset m.source.End => IsComponent M m K)).attach).image
    (fun K => componentPosition M step m K.val (Finset.mem_filter.mp K.property).2)

theorem mem_successors (m : Move I₁ I₂ O₁ O₂ Q D) (P : Position I₁ I₂ Q D) :
    P ∈ successors M step m ↔ Next M step m P := by
  constructor
  · intro mem
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp mem
    exact componentPosition_next M step m K.val _
  · intro next
    obtain ⟨phase,K,component,histories,states⟩ := next
    let k : (Finset.univ.filter (fun K : Finset m.source.End => IsComponent M m K)) :=
      ⟨K,Finset.mem_filter.mpr ⟨Finset.mem_univ _,component⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨k,Finset.mem_attach _ _,?_⟩
    apply position_ext _ P phase.symm histories.symm
    intro h j eq
    obtain ⟨e,inside,he⟩ := Finset.mem_image.mp h.property
    exact (componentPosition_states M step m K component h e inside he.symm).trans
      (states j e inside (eq.symm.trans he.symm)).symm

variable (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))

def nodes : Nat → Finset (List (Position I₁ I₂ Q D))
  | 0 => {[]}
  | n+1 => (nodes n).biUnion (fun node => (successors M step (tree node)).image (fun P => node ++ [P]))

theorem mem_nodes (n : Nat) (node : List (Position I₁ I₂ Q D)) :
    node ∈ nodes M step tree n ↔ node.length = n ∧ publicSupport (HistoryGame.offers M step) tree node = true := by
  induction n generalizing node with
  | zero =>
    simp only [nodes,Finset.mem_singleton,List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl,publicSupport_nil _ _⟩
    · exact And.left
  | succ n ih =>
    constructor
    · intro mem
      obtain ⟨old,oldmem,pmem⟩ := Finset.mem_biUnion.mp mem
      obtain ⟨P,next,rfl⟩ := Finset.mem_image.mp pmem
      have oldspec := (ih old).mp oldmem
      refine ⟨by simp [oldspec.1],?_⟩
      rw [publicSupport_append,oldspec.2,Bool.true_and]
      exact @decide_eq_true _ (Classical.propDecidable _) ((mem_successors M step _ _).mp next)
    · rintro ⟨len,supported⟩
      cases node using List.reverseRecOn with
      | nil => simp at len
      | append_singleton old P =>
        have both : publicSupport (HistoryGame.offers M step) tree old = true ∧
            HistoryGame.offers M step (tree old) P = true := by
          simpa only [publicSupport_append,Bool.and_eq_true] using supported
        apply Finset.mem_biUnion.mpr
        refine ⟨old,(ih old).mpr ⟨by simpa using len,both.1⟩,?_⟩
        exact Finset.mem_image.mpr ⟨P,(mem_successors M step _ _).mpr
          (@of_decide_eq_true _ (Classical.propDecidable _) both.2),rfl⟩

abbrev Raw (node : List (Position I₁ I₂ Q D)) :=
  (t : Fin D) × ClosingLayer (tree node).source.Root I₁ I₂ (t.val+1)

def rawHistory (node : List (Position I₁ I₂ Q D)) (x : Raw tree node) : EnvHistory I₁ I₂ :=
  closingLayerHistory (tree node).source.past (x.1.val+1) x.2

def rawOutput (node : List (Position I₁ I₂ Q D)) (x : Raw tree node) : O₁ × O₂ :=
  (tree node).rule x.1 x.2

variable [LinearOrder O₁] [LinearOrder O₂]

def candidates (p : Proc) (v : View I₁ I₂ p) : Finset (O₁ × O₂) :=
  (Finset.range ((ownInputs v).length+1)).biUnion (fun n =>
    (nodes M step tree n).biUnion (fun node =>
      (Finset.univ.filter (fun x : Raw tree node =>
        M.eval (History.graphSequence (rawHistory tree node x)) ∈ M.accept ∧
        currentView p (rawHistory tree node x) = v)).image (rawOutput tree node)))

theorem candidate_sound (p : Proc) (v : View I₁ I₂ p) (o : O₁ × O₂)
    (mem : o ∈ candidates M step tree p v) :
    ∃ x : Prescription M step tree, currentView p (prescribedHistory M step tree x) = v ∧
      prescribedOutput M step tree x = o := by
  obtain ⟨n,_,node,nodemem,raw,rawmem,eq⟩ := by
    simpa only [candidates,Finset.mem_biUnion,Finset.mem_image] using mem
  have spec := (Finset.mem_filter.mp rawmem).2
  exact ⟨⟨node,((mem_nodes M step tree n node).mp nodemem).2,raw.1,raw.2,spec.1⟩,spec.2,eq⟩

variable (q₀ : Q)
variable (legal : SupportedMovesValid (HistoryGame.offers M step) (Position.initial q₀) (Legal M step .component) tree)

include legal in
theorem candidate_complete (x : Prescription M step tree) (p : Proc) :
    prescribedOutput M step tree x ∈ candidates M step tree p (currentView p (prescribedHistory M step tree x)) := by
  have clock : (ownInputs (currentView p (prescribedHistory M step tree x))).length =
      List.length (prescribedHistory M step tree x) := by
    cases p <;> simp only [(ownInputs_history _).1,(ownInputs_history _).2,inputWord,List.length_map]
  have positive : 0 < D := Nat.zero_lt_of_lt x.time.isLt
  have size : x.node.length < (ownInputs (currentView p (prescribedHistory M step tree x))).length+1 := by
    rw [clock,prescribed_length M step tree q₀ legal x]
    have le : x.node.length ≤ x.node.length*D := Nat.le_mul_of_pos_right _ positive
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨x.node.length,Finset.mem_range.mpr size,Finset.mem_biUnion.mpr ?_⟩
  refine ⟨x.node,(mem_nodes M step tree _ _).mpr ⟨rfl,x.supported⟩,Finset.mem_image.mpr ?_⟩
  exact ⟨⟨x.time,x.scenario⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.live,rfl⟩,rfl⟩

variable (fallback : O₁ × O₂)

def chooseOutput (p : Proc) (v : View I₁ I₂ p) : O₁ × O₂ :=
  if available : (candidates M step tree p v).Nonempty then
    (candidates M step tree p v).min' available else fallback

def strategy : StrategyPair I₁ I₂ O₁ O₂ where
  one := fun v => (chooseOutput M step tree fallback .one v).1
  two := fun v => (chooseOutput M step tree fallback .two v).2

attribute [local irreducible] candidates chooseOutput

include legal in
theorem strategy_implements (x : Prescription M step tree) :
    ((strategy M step tree fallback).one (currentView .one (prescribedHistory M step tree x)),
     (strategy M step tree fallback).two (currentView .two (prescribedHistory M step tree x))) =
       prescribedOutput M step tree x := by
  have chosen (p : Proc) : ∃ y : Prescription M step tree,
      currentView p (prescribedHistory M step tree y) = currentView p (prescribedHistory M step tree x) ∧
      prescribedOutput M step tree y = chooseOutput M step tree fallback p (currentView p (prescribedHistory M step tree x)) := by
    have nonempty : (candidates M step tree p (currentView p (prescribedHistory M step tree x))).Nonempty :=
      ⟨_,candidate_complete M step tree q₀ legal x p⟩
    apply candidate_sound M step tree p (currentView p (prescribedHistory M step tree x))
      (chooseOutput M step tree fallback p (currentView p (prescribedHistory M step tree x)))
    rw [chooseOutput,dif_pos nonempty]
    exact Finset.min'_mem _ _
  apply Prod.ext
  · obtain ⟨y,views,output⟩ := chosen .one
    have same := prescriptions_consistent M step tree q₀ legal y x .one views
    exact (congrArg Prod.fst output).symm.trans same
  · obtain ⟨y,views,output⟩ := chosen .two
    have same := prescriptions_consistent M step tree q₀ legal y x .two views
    exact (congrArg Prod.snd output).symm.trans same

end Characterisation.ComponentGames.ExecutableReadback
