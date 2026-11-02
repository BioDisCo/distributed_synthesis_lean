/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds

/-! A finite one-round interface for graph rows. Absolute coordinates and
history depth are absent from the representation; repeated automaton states
are retained in distinct history slots. This interface does not summarize
private-input histories or establish the synthesis compiler. -/
namespace Characterisation
open DistributedSynthesis DistributedSynthesis.FullViewPath

def rowEndpoint (h : List Graph) (rightSide : Bool) : Vertex :=
  if rightSide then right (evaluate h) else left (evaluate h)

def endpointNumber (j : Nat) (rightSide : Bool) : Nat :=
  j + if rightSide then 1 else 0

theorem rowEndpoint_reachable (h : List Graph) (b : Bool) :
    PaddingProjection.Reachable h.length (rowEndpoint h b) := by
  refine ⟨h,rfl,?_⟩
  cases b <;> cases he : (evaluate h).oneLeft <;>
    simp [rowEndpoint, left, right, he]

theorem rowEndpoint_coordinate (h : List Graph) (b : Bool) :
    PaddingProjection.coordinate (rowEndpoint h b) = endpointNumber (pathIndex h) b := by
  cases b
  · exact (actual_endpoint_indices h).1
  · exact (actual_endpoint_indices h).2

theorem rowEndpoint_eq_iff (h k : List Graph) (sameDepth : h.length = k.length)
    (b c : Bool) : rowEndpoint h b = rowEndpoint k c ↔
      endpointNumber (pathIndex h) b = endpointNumber (pathIndex k) c := by
  constructor
  · intro eq
    simpa only [rowEndpoint_coordinate] using congrArg PaddingProjection.coordinate eq
  · intro eq
    apply PaddingProjection.coordinate_injective (rowEndpoint_reachable h b)
      (sameDepth ▸ rowEndpoint_reachable k c)
    simpa only [rowEndpoint_coordinate] using eq

/-- Refine slot i using only the parity of the row origin. -/
def relativeStep (parity i : Nat) (g : Graph) : Nat :=
  3 * i + if (parity + i) % 2 = 0 then graphDigit g else 2 - graphDigit g

theorem indexStep_relative (a i : Nat) (g : Graph) :
    indexStep (a+i) g = 3*a + relativeStep (a%2) i g := by
  have parity : (a+i)%2 = (a%2+i)%2 := by omega
  simp only [indexStep, relativeStep, parity]
  split <;> omega

theorem relativeStep_bounds (p i : Nat) (g : Graph) :
    3*i ≤ relativeStep p i g ∧ relativeStep p i g < 3*i+3 := by
  unfold relativeStep
  split <;> cases g <;> simp [graphDigit]

/-- Exact equality of actual child views can be checked using finite slot
coordinates. Both sides are tagged vertices, so process identity is retained. -/
theorem child_endpoint_eq_iff (h k : List Graph) (sameDepth : h.length = k.length)
    (a i j : Nat) (hi : pathIndex h = a+i) (kj : pathIndex k = a+j)
    (g z : Graph) (b c : Bool) :
    rowEndpoint (h++[g]) b = rowEndpoint (k++[z]) c ↔
      endpointNumber (relativeStep (a%2) i g) b =
        endpointNumber (relativeStep (a%2) j z) c := by
  rw [rowEndpoint_eq_iff _ _ (by simp [sameDepth]), pathIndex_append,
    pathIndex_append, hi, kj, indexStep_relative, indexStep_relative]
  simp only [endpointNumber]
  omega

/-- Absent slots are permitted. A slot stores its own automaton state even
when another slot has the same state. -/
abbrev GraphRow (Q : Type*) (K : Nat) := Fin 2 × (Fin K → Option Q)

instance graphRow_finite {Q : Type*} [Finite Q] (K : Nat) : Finite (GraphRow Q K) := by
  unfold GraphRow
  infer_instance

def childSlotState {Q : Type*} {K : Nat} (step : Q → Graph → Q)
    (row : GraphRow Q K) (i : Fin K) (g : Graph) : Option Q :=
  (row.2 i).map (fun q => step q g)

/-- Child endpoint numbers fit in one fixed finite set, independently of
the depth and of the absolute location of the parent row. -/
def childSlotEndpoint {Q : Type*} {K : Nat} (row : GraphRow Q K)
    (i : Fin K) (g : Graph) (b : Bool) : Fin (3*K+1) :=
  ⟨endpointNumber (relativeStep row.1.val i.val g) b, by
    have bounds := relativeStep_bounds row.1.val i.val g
    have bound := i.isLt
    cases b <;> simp only [endpointNumber, Bool.false_eq_true, ↓reduceIte] <;> omega⟩

/-- This representation preserves all endpoint identifications in a
one-round expansion of the represented histories. -/
theorem childSlotEndpoint_exact {Q : Type*} {K : Nat} (row : GraphRow Q K)
    (a : Nat) (parity : row.1.val = a%2)
    (h k : List Graph) (i j : Fin K)
    (hi : pathIndex h = a+i.val) (kj : pathIndex k = a+j.val)
    (sameDepth : h.length = k.length) (g z : Graph) (b c : Bool) :
    childSlotEndpoint row i g b = childSlotEndpoint row j z c ↔
      rowEndpoint (h++[g]) b = rowEndpoint (k++[z]) c := by
  rw [child_endpoint_eq_iff _ _ sameDepth a i.val j.val hi kj]
  simp only [childSlotEndpoint, Fin.mk.injEq, parity]

/-- A semantic representation map; constructing this map need not be part
of the compiler. The compiler works on the finite row descriptions. -/
noncomputable def encodeGraphRow {Q : Type*} (P : List Graph → Prop)
    (label : List Graph → Q) (h : List Graph) (a K : Nat) : GraphRow Q K := by
  classical
  exact (⟨a%2, Nat.mod_lt _ (by omega)⟩, fun i =>
    if witness : ∃ k, Connected P h k ∧ pathIndex k = a+i.val
    then some (label witness.choose) else none)

theorem encodeGraphRow_slot {Q : Type*} (P : List Graph → Prop)
    (label : List Graph → Q) (h : List Graph) (a K : Nat) (i : Fin K) (q : Q) :
    (encodeGraphRow P label h a K).2 i = some q ↔
      ∃ k, Connected P h k ∧ pathIndex k = a+i.val ∧ label k = q := by
  classical
  unfold encodeGraphRow
  dsimp only
  split
  · rename_i witness
    constructor
    · intro eq
      exact ⟨witness.choose, witness.choose_spec.1, witness.choose_spec.2,
        Option.some.inj eq⟩
    · rintro ⟨k,conn,index,lab⟩
      have same : witness.choose = k := pathIndex_injective _ _
        ((connected_same_depth P witness.choose_spec.1).symm.trans
          (connected_same_depth P conn)) (witness.choose_spec.2.trans index.symm)
      simp [same,lab]
  · rename_i noWitness
    constructor
    · intro eq
      cases eq
    · rintro ⟨k,conn,index,_⟩
      exact (noWitness ⟨k,conn,index⟩).elim

/-- Every bounded graph component admits a description with uniformly many
slots. An occupied slot represents exactly one history of the component.
Its label can be any finite automaton state or tuple of finite annotations. -/
theorem bounded_components_finite_rows {Q : Type*}
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (label : List Graph → Q) :
    ∃ K, ∀ h, P h → ∃ a, ∃ row : GraphRow Q K,
      row.1.val = a%2 ∧
      (∀ k, Connected P h k → ∃ i : Fin K,
        pathIndex k = a+i.val ∧ row.2 i = some (label k)) ∧
      (∀ i q, row.2 i = some q → ∃ k,
        Connected P h k ∧ pathIndex k = a+i.val ∧ label k = q) := by
  obtain ⟨D,near⟩ := bounded_rows_bound_connected_distance P
    (bounded_components_imply_bounded_rows P bounded)
  refine ⟨2*D+1,?_⟩
  intro h live
  let a := pathIndex h-D
  refine ⟨a,encodeGraphRow P label h a (2*D+1),rfl,?_,?_⟩
  · intro k conn
    have distance := near h k live conn
    have lower : a ≤ pathIndex k := by dsimp [a]; omega
    have upper : pathIndex k-a < 2*D+1 := by dsimp [a]; omega
    let i : Fin (2*D+1) := ⟨pathIndex k-a,upper⟩
    have index : pathIndex k = a+i.val := by dsimp [i]; omega
    exact ⟨i,index,(encodeGraphRow_slot P label h a _ i _).mpr ⟨k,conn,index,rfl⟩⟩
  · intro i q eq
    exact (encodeGraphRow_slot P label h a _ i q).mp eq

/-- Slot updates agree with the actual recognizer transition. -/
theorem childSlotState_eval {Q : Type*} {K : Nat} (M : Recognizer Graph Q)
    (row : GraphRow Q K) (i : Fin K) (h : List Graph)
    (stored : row.2 i = some (M.eval h)) (g : Graph) :
    childSlotState M.step row i g = some (M.eval (h++[g])) := by
  simp [childSlotState, stored, Recognizer.eval, Recognizer.evalFrom]

end Characterisation
