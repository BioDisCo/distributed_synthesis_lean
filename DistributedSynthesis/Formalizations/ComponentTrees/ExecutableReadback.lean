/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreePrescriptions
import DistributedSynthesis.Library.Distributed.LeaderPhases.InputKnowledge

/-! Finite search for the local output prescribed by an effectively given
uncompressed tree. This module is outside any noncomputable section.
-/
namespace Characterisation.ComponentTrees.ExecutableReadback
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation.FiniteArena DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)] [DecidableEq B.State]

def successors (m : Move I₁ I₂ O₁ O₂ B.State D) : Finset (Position I₁ I₂ B.State D) :=
  ((Finset.univ.filter (fun K : Finset m.source.End => IsComponent M m K)).attach).image
    (fun K => ExecutableReverse.componentPosition B M m K.val (Finset.mem_filter.mp K.property).2)

theorem mem_successors (m : Move I₁ I₂ O₁ O₂ B.State D) (P : Position I₁ I₂ B.State D) :
    P ∈ successors B M m ↔ ComponentSuccessor B M m P := by
  constructor
  · intro mem
    obtain ⟨K,_,rfl⟩ := Finset.mem_image.mp mem
    exact ExecutableReverse.componentPosition_successor B M m K.val _
  · intro next
    obtain ⟨K,component,phase,histories,states⟩ := next
    let k : (Finset.univ.filter (fun K : Finset m.source.End => IsComponent M m K)) :=
      ⟨K,Finset.mem_filter.mpr ⟨Finset.mem_univ _,component⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨k,Finset.mem_attach _ _,?_⟩
    apply position_ext _ P phase.symm histories.symm
    intro h j eq
    obtain ⟨e,inside,he⟩ := Finset.mem_image.mp h.property
    exact (ExecutableReverse.componentPosition_states B M m K component h ⟨e,inside⟩ he.symm).trans
      (states j ⟨e,inside⟩ (eq.symm.trans he.symm)).symm

variable (tree : UncompressedTree B M)

def nodes : Nat → Finset (List (Position I₁ I₂ B.State D))
  | 0 => {[]}
  | n+1 => (nodes n).biUnion (fun node => (successors B M (tree node).move).image (fun P => node ++ [P]))

theorem mem_nodes (n : Nat) (node : List (Position I₁ I₂ B.State D)) :
    node ∈ nodes B M tree n ↔ node.length = n ∧ publicSupport (UncompressedNode.offers) tree node = true := by
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
      exact @decide_eq_true _ (Classical.propDecidable _) ((mem_successors B M _ _).mp next)
    · rintro ⟨len,supported⟩
      cases node using List.reverseRecOn with
      | nil => simp at len
      | append_singleton old P =>
        have both : publicSupport (UncompressedNode.offers) tree old = true ∧
            UncompressedNode.offers (tree old) P = true := by
          simpa only [publicSupport_append,Bool.and_eq_true] using supported
        apply Finset.mem_biUnion.mpr
        refine ⟨old,(ih old).mpr ⟨by simpa using len,both.1⟩,?_⟩
        exact Finset.mem_image.mpr ⟨P,(mem_successors B M _ _).mpr
          (@of_decide_eq_true _ (Classical.propDecidable _) both.2),rfl⟩

abbrev Raw (node : List (Position I₁ I₂ B.State D)) :=
  (t : Fin D) × ClosingLayer (tree node).position.Root I₁ I₂ (t.val+1)

def rawHistory (node : List (Position I₁ I₂ B.State D)) (x : Raw B M tree node) : EnvHistory I₁ I₂ :=
  closingLayerHistory (tree node).position.past (x.1.val+1) x.2

def rawOutput (node : List (Position I₁ I₂ B.State D)) (x : Raw B M tree node) : O₁ × O₂ :=
  (tree node).rule x.1 x.2

variable [LinearOrder O₁] [LinearOrder O₂]

def candidates (p : Proc) (v : View I₁ I₂ p) : Finset (O₁ × O₂) :=
  (Finset.range ((ownInputs v).length+1)).biUnion (fun n =>
    (nodes B M tree n).biUnion (fun node =>
      (Finset.univ.filter (fun x : Raw B M tree node =>
        M.eval (History.graphSequence (rawHistory B M tree node x)) ∈ M.accept ∧
        currentView p (rawHistory B M tree node x) = v)).image (rawOutput B M tree node)))

theorem candidate_sound (p : Proc) (v : View I₁ I₂ p) (o : O₁ × O₂)
    (mem : o ∈ candidates B M tree p v) :
    ∃ x : UncompressedTree.Prescription tree, currentView p (UncompressedTree.prescribedHistory tree x) = v ∧
      UncompressedTree.prescribedOutput tree x = o := by
  obtain ⟨n,_,node,nodemem,raw,rawmem,eq⟩ := by
    simpa only [candidates,Finset.mem_biUnion,Finset.mem_image] using mem
  have spec := (Finset.mem_filter.mp rawmem).2
  exact ⟨⟨node,((mem_nodes B M tree n node).mp nodemem).2,raw.1,raw.2,spec.1⟩,spec.2,eq⟩

variable (valid : tree.Valid)

include valid in
theorem candidate_complete (x : UncompressedTree.Prescription tree) (p : Proc) :
    UncompressedTree.prescribedOutput tree x ∈ candidates B M tree p (currentView p (UncompressedTree.prescribedHistory tree x)) := by
  have clock : (ownInputs (currentView p (UncompressedTree.prescribedHistory tree x))).length =
      List.length (UncompressedTree.prescribedHistory tree x) := by
    cases p <;> simp only [(ownInputs_history _).1,(ownInputs_history _).2,inputWord,List.length_map]
  have positive : 0 < D := Nat.zero_lt_of_lt x.time.isLt
  have size : x.node.length < (ownInputs (currentView p (UncompressedTree.prescribedHistory tree x))).length+1 := by
    rw [clock,UncompressedTree.prescribed_length tree valid x]
    have le : x.node.length ≤ x.node.length*D := Nat.le_mul_of_pos_right _ positive
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨x.node.length,Finset.mem_range.mpr size,Finset.mem_biUnion.mpr ?_⟩
  refine ⟨x.node,(mem_nodes B M tree _ _).mpr ⟨rfl,x.supported⟩,Finset.mem_image.mpr ?_⟩
  exact ⟨⟨x.time,x.scenario⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.live,rfl⟩,rfl⟩

variable (fallback : O₁ × O₂)

def chooseOutput (p : Proc) (v : View I₁ I₂ p) : O₁ × O₂ :=
  if available : (candidates B M tree p v).Nonempty then
    (candidates B M tree p v).min' available else fallback

def strategy : StrategyPair I₁ I₂ O₁ O₂ where
  one := fun v => (chooseOutput B M tree fallback .one v).1
  two := fun v => (chooseOutput B M tree fallback .two v).2

attribute [local irreducible] candidates chooseOutput

include valid in
theorem strategy_implements (x : UncompressedTree.Prescription tree) :
    ((strategy B M tree fallback).one (currentView .one (UncompressedTree.prescribedHistory tree x)),
     (strategy B M tree fallback).two (currentView .two (UncompressedTree.prescribedHistory tree x))) =
       UncompressedTree.prescribedOutput tree x := by
  have chosen (p : Proc) : ∃ y : UncompressedTree.Prescription tree,
      currentView p (UncompressedTree.prescribedHistory tree y) = currentView p (UncompressedTree.prescribedHistory tree x) ∧
      UncompressedTree.prescribedOutput tree y = chooseOutput B M tree fallback p (currentView p (UncompressedTree.prescribedHistory tree x)) := by
    have nonempty : (candidates B M tree p (currentView p (UncompressedTree.prescribedHistory tree x))).Nonempty :=
      ⟨_,candidate_complete B M tree valid x p⟩
    apply candidate_sound B M tree p (currentView p (UncompressedTree.prescribedHistory tree x))
      (chooseOutput B M tree fallback p (currentView p (UncompressedTree.prescribedHistory tree x)))
    rw [chooseOutput,dif_pos nonempty]
    exact Finset.min'_mem _ _
  apply Prod.ext
  · obtain ⟨y,views,output⟩ := chosen .one
    have same := UncompressedTree.prescriptions_consistent tree valid y x .one views
    exact (congrArg Prod.fst output).symm.trans same
  · obtain ⟨y,views,output⟩ := chosen .two
    have same := UncompressedTree.prescriptions_consistent tree valid y x .two views
    exact (congrArg Prod.snd output).symm.trans same

end Characterisation.ComponentTrees.ExecutableReadback
