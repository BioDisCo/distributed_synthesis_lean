/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentTrees.CanonicalPositions
import DistributedSynthesis.Formalizations.ComponentTrees.EncodeNode

namespace Characterisation.ComponentTrees.CanonicalChildren
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames FiniteAlphabet CanonicalPositions
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (live : B.State → Bool) (bound : Nat)
variable (root : FinitePositions.Position B.State capacity)

def normalizeChild (m : Move (capacity:=capacity) B) (c : Child B m) : Child B m :=
  ⟨normalizeWith root c.1,fun k => c.2 ((normalizeWithIso root c.1).toEquiv.symm k)⟩

theorem normalizeChild_edges (m : Move (capacity:=capacity) B) (c : Child B m) :
    childEdges B m (normalizeChild B root m c) = childEdges B m c := by
  ext x
  simp only [childEdges,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨(normalizeWithIso root c.1).toEquiv.symm k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨(normalizeWithIso root c.1).toEquiv k,by simp [normalizeChild]⟩

theorem normalizeChild_correct (m : Move (capacity:=capacity) B) (c : Child B m)
    (correct : ChildCorrect B live m c) : ChildCorrect B live m (normalizeChild B root m c) := by
  refine ⟨correct.1.comp (normalizeWithIso root c.1).toEquiv.symm.injective,?_,?_,?_⟩
  · rw [normalizeChild_edges]
    exact correct.2.1
  · intro p h k
    have iso := (normalizeWithIso root c.1).shape_same p
      ((normalizeWithIso root c.1).toEquiv.symm h) ((normalizeWithIso root c.1).toEquiv.symm k)
    simp only [Equiv.apply_symm_apply] at iso
    exact iso.trans (correct.2.2.1 p _ _)
  · intro h
    have iso := (normalizeWithIso root c.1).state_same ((normalizeWithIso root c.1).toEquiv.symm h)
    simp only [Equiv.apply_symm_apply] at iso
    exact iso.trans (correct.2.2.2 _)

def normalizeRaw (a : Raw (capacity:=capacity) B) : Raw (capacity:=capacity) B :=
  ⟨a.1,fun d => (a.2 d).map (normalizeChild B root a.1)⟩

theorem normalizeRaw_legal (a : Raw (capacity:=capacity) B) (legal : Legal B live bound a) :
    Legal B live bound (normalizeRaw B root a) := by
  refine ⟨legal.1,legal.2.1,legal.2.2.1,legal.2.2.2.1,?_,?_,?_⟩
  · intro d c entry
    obtain ⟨old,present,rfl⟩ := Option.map_eq_some_iff.mp entry
    exact normalizeChild_correct B live root a.1 old (legal.2.2.2.2.1 d old present)
  · intro K component
    obtain ⟨d,c,present,edges⟩ := legal.2.2.2.2.2.1 K component
    exact ⟨d,normalizeChild B root a.1 c,by simp [normalizeRaw,present],
      (normalizeChild_edges B root a.1 c).trans edges⟩
  · intro d c f e first second same
    obtain ⟨old,present,rfl⟩ := Option.map_eq_some_iff.mp first
    obtain ⟨old',present',rfl⟩ := Option.map_eq_some_iff.mp second
    change childEdges B a.1 (normalizeChild B root a.1 old) = childEdges B a.1 (normalizeChild B root a.1 old') at same
    rw [normalizeChild_edges,normalizeChild_edges] at same
    exact legal.2.2.2.2.2.2 d old f old' present present' same

def normalizeLetter (a : {raw : Raw (capacity:=capacity) B // Legal B live bound raw}) :
    {raw : Raw (capacity:=capacity) B // Legal B live bound raw} :=
  ⟨normalizeRaw B root a.val,normalizeRaw_legal B live bound root a.val a.property⟩

theorem child_normalized (a : {raw : Raw (capacity:=capacity) B // Legal B live bound raw})
    (d : Fin capacity) (c : Child B (normalizeLetter B live bound root a).val.1)
    (entry : (normalizeLetter B live bound root a).val.2 d = some c) :
    normalizeWith root c.1 = c.1 := by
  obtain ⟨old,_,rfl⟩ := Option.map_eq_some_iff.mp entry
  exact normalizeWith_idempotent root old.1

end Characterisation.ComponentTrees.CanonicalChildren
