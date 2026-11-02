/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentTrees.FinitePositions
import DistributedSynthesis.Formalizations.ComponentGames.FiniteOrders
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

namespace Characterisation.ComponentTrees.CanonicalPositions
open DistributedSynthesis Characterisation Characterisation.ComponentGames
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
set_option linter.unusedSectionVars false
variable {Q : Type} {capacity : Nat}
variable [Fintype Q] [LinearOrder Q]

abbrev Position := FinitePositions.Position Q capacity

/-- A finite test for the existing owner- and label-preserving isomorphism. -/
def IsIsoMap (a b : Position (Q:=Q) (capacity:=capacity)) (f : a.Root → b.Root) : Prop :=
  Function.Bijective f ∧ (∀ p h k, b.2.shape p (f h) (f k) = a.2.shape p h k) ∧
    ∀ h, b.2.state (f h) = a.2.state h

instance isIsoMapDecidable (a b : Position (Q:=Q) (capacity:=capacity)) (f : a.Root → b.Root) :
    Decidable (IsIsoMap a b f) := by unfold IsIsoMap Function.Bijective Function.Injective Function.Surjective; infer_instance

def Isomorphic (a b : Position (Q:=Q) (capacity:=capacity)) : Prop := ∃ f, IsIsoMap a b f
instance isomorphicDecidable (a b : Position (Q:=Q) (capacity:=capacity)) : Decidable (Isomorphic a b) := by
  unfold Isomorphic; infer_instance

def isoOfMap (a b : Position (Q:=Q) (capacity:=capacity)) (f : a.Root → b.Root)
    (valid : IsIsoMap a b f) : Representation.Iso a.2 b.2 where
  toEquiv := ExecutableHistories.finiteEquiv f valid.1
  shape_same := valid.2.1
  graph_same _ := rfl
  state_same := valid.2.2

theorem isomorphic_iff (a b : Position (Q:=Q) (capacity:=capacity)) :
    Isomorphic a b ↔ Nonempty (Representation.Iso a.2 b.2) := by
  constructor
  · rintro ⟨f,valid⟩
    exact ⟨isoOfMap a b f valid⟩
  · rintro ⟨e⟩
    exact ⟨e.toEquiv,e.toEquiv.bijective,e.shape_same,e.state_same⟩

theorem isomorphic_refl (a : Position (Q:=Q) (capacity:=capacity)) : Isomorphic a a :=
  ⟨id,Function.bijective_id,fun _ _ _ => rfl,fun _ => rfl⟩

theorem isomorphic_symm {a b : Position (Q:=Q) (capacity:=capacity)} (h : Isomorphic a b) : Isomorphic b a := by
  obtain ⟨e⟩ := (isomorphic_iff a b).mp h
  exact (isomorphic_iff b a).mpr ⟨e.symm⟩

theorem isomorphic_trans {a b c : Position (Q:=Q) (capacity:=capacity)}
    (h : Isomorphic a b) (k : Isomorphic b c) : Isomorphic a c := by
  obtain ⟨e⟩ := (isomorphic_iff a b).mp h
  obtain ⟨f⟩ := (isomorphic_iff b c).mp k
  exact (isomorphic_iff a c).mpr ⟨e.trans f⟩

def isoClass (a : Position (Q:=Q) (capacity:=capacity)) : Finset (Position (Q:=Q) (capacity:=capacity)) :=
  Finset.univ.filter (Isomorphic a)

theorem isoClass_nonempty (a : Position (Q:=Q) (capacity:=capacity)) : (isoClass a).Nonempty :=
  ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,isomorphic_refl a⟩⟩

/-- Choose the first representative by finite enumeration. The choice is
computable; it does not add an order to the mathematical graph. -/
def normalize (a : Position (Q:=Q) (capacity:=capacity)) : Position (Q:=Q) (capacity:=capacity) :=
  (isoClass a).min' (isoClass_nonempty a)

theorem normalize_isomorphic (a : Position (Q:=Q) (capacity:=capacity)) : Isomorphic a (normalize a) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

theorem normalize_eq_of_isomorphic {a b : Position (Q:=Q) (capacity:=capacity)} (h : Isomorphic a b) :
    normalize a = normalize b := by
  have same : isoClass a = isoClass b := by
    ext c
    simp only [isoClass,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun k => isomorphic_trans (isomorphic_symm h) k,fun k => isomorphic_trans h k⟩
  unfold normalize
  simp only [same]

theorem normalize_idempotent (a : Position (Q:=Q) (capacity:=capacity)) :
    normalize (normalize a) = normalize a :=
  (normalize_eq_of_isomorphic (normalize_isomorphic a)).symm

theorem normalize_eq_iff (a b : Position (Q:=Q) (capacity:=capacity)) :
    normalize a = normalize b ↔ Isomorphic a b := by
  constructor
  · intro same
    have h := normalize_isomorphic a
    rw [same] at h
    exact isomorphic_trans h (isomorphic_symm (normalize_isomorphic b))
  · exact normalize_eq_of_isomorphic

/-- A witness is found by finite search over maps and inverted using the
existing executable finite-equivalence constructor. -/
def chooseIso (a b : Position (Q:=Q) (capacity:=capacity)) (iso : Isomorphic a b) : Representation.Iso a.2 b.2 := by
  let candidates := Finset.univ.filter (IsIsoMap a b)
  have existsMap : candidates.Nonempty := by
    obtain ⟨f,valid⟩ := iso
    exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,valid⟩⟩
  let f := candidates.min' existsMap
  exact isoOfMap a b f (Finset.mem_filter.mp (Finset.min'_mem candidates existsMap)).2

def normalizeIso (a : Position (Q:=Q) (capacity:=capacity)) : Representation.Iso a.2 (normalize a).2 :=
  chooseIso a (normalize a) (normalize_isomorphic a)

/-- Reserve the manuscript's initial graph as its class representative. -/
def normalizeWith (root a : Position (Q:=Q) (capacity:=capacity)) : Position (Q:=Q) (capacity:=capacity) :=
  if Isomorphic a root then root else normalize a

theorem normalizeWith_isomorphic (root a : Position (Q:=Q) (capacity:=capacity)) :
    Isomorphic a (normalizeWith root a) := by
  unfold normalizeWith
  split_ifs with h
  · exact h
  · exact normalize_isomorphic a

theorem normalizeWith_eq {root a b : Position (Q:=Q) (capacity:=capacity)} (h : Isomorphic a b) :
    normalizeWith root a = normalizeWith root b := by
  have same : Isomorphic a root ↔ Isomorphic b root :=
    ⟨fun k => isomorphic_trans (isomorphic_symm h) k,fun k => isomorphic_trans h k⟩
  unfold normalizeWith
  simp only [same,normalize_eq_of_isomorphic h]

theorem normalizeWith_idempotent (root a : Position (Q:=Q) (capacity:=capacity)) :
    normalizeWith root (normalizeWith root a) = normalizeWith root a :=
  (normalizeWith_eq (normalizeWith_isomorphic root a)).symm

@[simp] theorem normalizeWith_root (root : Position (Q:=Q) (capacity:=capacity)) :
    normalizeWith root root = root := by simp [normalizeWith,isomorphic_refl]

def normalizeWithIso (root a : Position (Q:=Q) (capacity:=capacity)) :
    Representation.Iso a.2 (normalizeWith root a).2 := chooseIso a _ (normalizeWith_isomorphic root a)

abbrev Representative := {a : Position (Q:=Q) (capacity:=capacity) // normalize a = a}
instance representativeFintype : Fintype (Representative (Q:=Q) (capacity:=capacity)) := inferInstance

/-- Distinct representatives cannot describe isomorphic owner-labelled graphs. -/
theorem representatives_unique (a b : Representative (Q:=Q) (capacity:=capacity))
    (iso : Representation.Iso a.val.2 b.val.2) : a = b := by
  apply Subtype.ext
  rw [← a.property,← b.property]
  exact normalize_eq_of_isomorphic ((isomorphic_iff _ _).mpr ⟨iso⟩)

end Characterisation.ComponentTrees.CanonicalPositions
