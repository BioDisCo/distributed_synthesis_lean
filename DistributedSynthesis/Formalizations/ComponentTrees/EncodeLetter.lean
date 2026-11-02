/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.FiniteAlphabet

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees.FiniteAlphabet
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [DecidableEq B.State]
variable (live : B.State → Bool) (bound : Nat)
variable (m : Move (capacity:=capacity) B)
variable (small : (Finset.univ.image m.replacement).card ≤ bound)
variable (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity)

abbrev Components := {K : Finset m.End // Component B live m K}

instance componentsFintype : Fintype (Components B live m) := by unfold Components; infer_instance

noncomputable def anchor (K : Components B live m) : m.End := K.property.choose

theorem anchor_spec (K : Components B live m) : liveEnd B live m (anchor B live m K) = true ∧
    ∀ x, x ∈ K.val ↔ closingComponentMask (closingLayerShape m.source.2.shape D)
      (liveEnd B live m) (anchor B live m K) x = true := K.property.choose_spec

theorem component_anchor (K : Components B live m) : anchor B live m K ∈ K.val := by
  apply ((anchor_spec B live m K).2 _).mpr
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨(anchor_spec B live m K).1,SimpleGraph.Reachable.refl _⟩

theorem component_equal (K L : Components B live m) (x : m.End) (hx : x ∈ K.val) (hy : x ∈ L.val) : K = L := by
  apply Subtype.ext
  apply Finset.ext
  intro z
  have hx' := ((anchor_spec B live m K).2 x).mp hx
  have hy' := ((anchor_spec B live m L).2 x).mp hy
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq] at hx' hy'
  rw [(anchor_spec B live m K).2 z,(anchor_spec B live m L).2 z]
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨alive,path⟩
    exact ⟨alive,hy'.2.trans (hx'.2.symm.trans path)⟩
  · rintro ⟨alive,path⟩
    exact ⟨alive,hx'.2.trans (hy'.2.symm.trans path)⟩

include small fits in
theorem components_card : Fintype.card (Components B live m) ≤ capacity := by
  let alive := Finset.univ.filter (fun x : m.End => liveEnd B live m x = true)
  let pick (K : Components B live m) : alive :=
    ⟨anchor B live m K,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(anchor_spec B live m K).1⟩⟩
  have inj : Function.Injective pick := by
    intro K L eq
    have same : anchor B live m K = anchor B live m L := congrArg Subtype.val eq
    exact component_equal B live m K L _ (component_anchor B live m K)
      (same.symm ▸ component_anchor B live m L)
  have card := Fintype.card_le_of_injective pick inj
  rw [Fintype.card_coe] at card
  exact card.trans ((liveEnd_card B live bound m small).trans fits)

variable [LinearOrder I₁] [LinearOrder I₂]

/-- A fixed computable ordering of the endpoint components. -/
def componentEnumeration : Components B live m ≃ Fin (Fintype.card (Components B live m)) :=
  (Fintype.orderIsoFinOfCardEq (Components B live m) rfl).toEquiv.symm

def componentIndex : Components B live m ↪ Fin capacity :=
  (componentEnumeration B live m).toEmbedding.trans
    (Fin.castLEEmb (components_card B live bound m small fits))

def componentData (K : Components B live m) : Representation.Data K.val Unit B.State where
  shape p h k := closingLayerShape m.source.2.shape D p h.val k.val
  graph _ := ()
  state h := endState B m h.val

def componentChild (K : Components B live m) : Child B m :=
  ⟨Representation.pack K.val ((component_card B live bound m K.val K.property small).trans fits)
      (componentData B live m K),
    fun k => ((Representation.numberSubset K.val).symm k).val⟩

theorem componentChild_edges (K : Components B live m) :
    childEdges B m (componentChild B live bound m small fits K) = K.val := by
  ext x
  simp only [childEdges,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,rfl⟩
    exact ((Representation.numberSubset K.val).symm k).property
  · intro mem
    exact ⟨Representation.numberSubset K.val ⟨x,mem⟩,
      congrArg Subtype.val ((Representation.numberSubset K.val).symm_apply_apply ⟨x,mem⟩)⟩

theorem componentChild_correct (K : Components B live m) :
    ChildCorrect B live m (componentChild B live bound m small fits K) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h k eq
    exact (Representation.numberSubset K.val).symm.injective (Subtype.ext eq)
  · rw [componentChild_edges]
    exact K.property
  · intro p h k; rfl
  · intro h; rfl

def children (d : Fin capacity) : Option (Child B m) :=
  if before : d.val < Fintype.card (Components B live m) then
    some (componentChild B live bound m small fits
      ((componentEnumeration B live m).symm ⟨d.val,before⟩)) else none

theorem children_iff (d : Fin capacity) (c : Child B m) :
    children B live bound m small fits d = some c ↔
      ∃ K, componentIndex B live bound m small fits K = d ∧ componentChild B live bound m small fits K = c := by
  unfold children
  split
  · rename_i before
    simp only [Option.some.injEq]
    constructor
    · intro eq
      refine ⟨(componentEnumeration B live m).symm ⟨d.val,before⟩,?_,eq⟩
      apply Fin.ext
      simp [componentIndex]
    · rintro ⟨K,index,eq⟩
      have indexed : componentIndex B live bound m small fits
          ((componentEnumeration B live m).symm ⟨d.val,before⟩) = d := by
        apply Fin.ext
        simp [componentIndex]
      have same := (componentIndex B live bound m small fits).injective
        (indexed.trans index.symm)
      simpa only [same] using eq
  · rename_i absent
    constructor
    · intro impossible; cases impossible
    · rintro ⟨K,index,_⟩
      have before : d.val < Fintype.card (Components B live m) := by
        rw [← index]
        exact ((componentEnumeration B live m) K).isLt
      exact False.elim (absent before)

/-- All components are represented exactly once; unused slots are padding. -/
theorem raw_legal (nonempty : 0 < m.source.1.val) (alive : ∀ h, live (m.source.2.state h) = true)
    (checks : FinitePositions.ReductionChecks m.source.2 bound m.replacement)
    (coherent : ClosingPolicyCoherent m.source.2.shape m.rule) :
    Legal B live bound ⟨m,children B live bound m small fits⟩ := by
  refine ⟨nonempty,alive,checks,coherent,?_,?_,?_⟩
  · intro d c entry
    obtain ⟨K,_,rfl⟩ := (children_iff B live bound m small fits d c).mp entry
    exact componentChild_correct B live bound m small fits K
  · intro K component
    let C : Components B live m := ⟨K,component⟩
    refine ⟨componentIndex B live bound m small fits C,componentChild B live bound m small fits C,?_,?_⟩
    · exact (children_iff B live bound m small fits _ _).mpr ⟨C,rfl,rfl⟩
    · exact componentChild_edges B live bound m small fits C
  · intro d c f e first second same
    obtain ⟨K,indexK,rfl⟩ := (children_iff B live bound m small fits d c).mp first
    obtain ⟨L,indexL,rfl⟩ := (children_iff B live bound m small fits f e).mp second
    rw [componentChild_edges,componentChild_edges] at same
    have eq : K = L := Subtype.ext same
    exact indexK.symm.trans ((congrArg (componentIndex B live bound m small fits) eq).trans indexL)

end Characterisation.ComponentTrees.FiniteAlphabet
