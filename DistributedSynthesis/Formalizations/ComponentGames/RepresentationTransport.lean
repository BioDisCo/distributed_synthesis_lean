/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.HistoryGames

namespace Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {H J I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}

theorem mapLayer_id (n : Nat) (s : ClosingLayer H I₁ I₂ n) : mapClosingLayer id n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih s.1) rfl

def layerEquiv (e : H ≃ J) (n : Nat) : ClosingLayer H I₁ I₂ n ≃ ClosingLayer J I₁ I₂ n where
  toFun := mapClosingLayer e n
  invFun := mapClosingLayer e.symm n
  left_inv := by
    intro s
    rw [mapClosingLayer_comp]
    have eq : e.symm ∘ e = id := funext e.symm_apply_apply
    rw [eq,mapLayer_id]
  right_inv := by
    intro s
    rw [mapClosingLayer_comp]
    have eq : e ∘ e.symm = id := funext e.apply_symm_apply
    rw [eq,mapLayer_id]

@[simp] theorem mapLayer_inverse (e : H ≃ J) (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    mapClosingLayer e.symm n (mapClosingLayer e n s) = s := (layerEquiv e n).symm_apply_apply s

@[simp] theorem mapLayer_inverse' (e : H ≃ J) (n : Nat) (s : ClosingLayer J I₁ I₂ n) :
    mapClosingLayer e n (mapClosingLayer e.symm n s) = s := (layerEquiv e n).apply_symm_apply s

variable [DecidableEq I₁] [DecidableEq I₂]

/-- Every equality update commutes with renaming the old roots, at every
suffix depth and for all pairs of private-input/graph continuations. -/
theorem layerShape_map (f : H → J) (shape : InputShape H) (other : InputShape J)
    (same : ∀ p h k, other p (f h) (f k) = shape p h k)
    (n : Nat) (p : Proc) (s t : ClosingLayer H I₁ I₂ n) :
    closingLayerShape other n p (mapClosingLayer f n s) (mapClosingLayer f n t) =
      closingLayerShape shape n p s t := by
  induction n generalizing p with
  | zero => exact same p s t
  | succ n ih =>
    rcases s with ⟨s,x,y,g⟩
    rcases t with ⟨t,u,v,k⟩
    cases p <;> cases g <;> cases k <;>
      simp only [closingLayerShape,mapClosingLayer,advanceInputShape,ih]

def policy (e : H ≃ J) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) : ClosingPolicy J I₁ I₂ O₁ O₂ D :=
  restrictClosingPolicy e.symm out

@[simp] theorem policy_apply (e : H ≃ J) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Fin D) (s : ClosingLayer H I₁ I₂ (n.val+1)) :
    policy e out n (mapClosingLayer e (n.val+1) s) = out n s := by
  simp only [policy,restrictClosingPolicy,mapLayer_inverse]

@[simp] theorem policy_inverse (e : H ≃ J) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) :
    policy e.symm (policy e out) = out := by
  funext n s
  exact policy_apply e out n s

def policyEquiv (e : H ≃ J) : ClosingPolicy H I₁ I₂ O₁ O₂ D ≃ ClosingPolicy J I₁ I₂ O₁ O₂ D where
  toFun := policy e
  invFun := policy e.symm
  left_inv := policy_inverse e
  right_inv := policy_inverse e.symm

theorem coherent_iff (e : H ≃ J) (shape : InputShape H) (other : InputShape J)
    (same : ∀ p h k, other p (e h) (e k) = shape p h k)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) :
    ClosingPolicyCoherent other (policy e out) ↔ ClosingPolicyCoherent shape out := by
  constructor
  · intro coherent n
    constructor
    · intro s t eq
      simpa only [policy_apply] using (coherent n).1
        (mapClosingLayer e _ s) (mapClosingLayer e _ t)
        (by rw [layerShape_map e shape other same]; exact eq)
    · intro s t eq
      simpa only [policy_apply] using (coherent n).2
        (mapClosingLayer e _ s) (mapClosingLayer e _ t)
        (by rw [layerShape_map e shape other same]; exact eq)
  · intro coherent n
    constructor
    all_goals intro s t eq
    all_goals obtain ⟨a,rfl⟩ := (layerEquiv (I₁:=I₁) (I₂:=I₂) e (n.val+1)).surjective s
    all_goals obtain ⟨b,rfl⟩ := (layerEquiv (I₁:=I₁) (I₂:=I₂) e (n.val+1)).surjective t
    all_goals change closingLayerShape other _ _ (mapClosingLayer e _ a) (mapClosingLayer e _ b) = true at eq
    all_goals rw [layerShape_map e shape other same] at eq
    · exact (by simpa only [layerEquiv,Equiv.coe_fn_mk,policy_apply] using (coherent n).1 a b eq)
    · exact (by simpa only [layerEquiv,Equiv.coe_fn_mk,policy_apply] using (coherent n).2 a b eq)

theorem labels_map (e : H ≃ J)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (q : H → Q) (other : J → Q) (same : ∀ h, other (e h) = q h)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (n : Nat) (bound : n ≤ D)
    (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step other (policy e out) n bound (mapClosingLayer e n s) =
      closingLayerLabels step q out n bound s := by
  have start : other = q ∘ e.symm := by
    funext j
    simpa only [Function.comp_apply,e.apply_symm_apply] using same (e.symm j)
  rw [start]
  exact (closingLayerLabels_restrict e.symm step q out n bound (mapClosingLayer e n s)).trans
    (congrArg (closingLayerLabels step q out n bound) (mapLayer_inverse e n s))

def replacement (e : H ≃ J) (r : H → H) : J → J := fun j => e (r (e.symm j))

@[simp] theorem replacement_apply (e : H ≃ J) (r : H → H) (h : H) : replacement e r (e h) = e (r h) := by
  simp only [replacement,e.symm_apply_apply]

@[simp] theorem replacement_inverse (e : H ≃ J) (r : H → H) : replacement e.symm (replacement e r) = r := by
  funext h
  simp only [replacement,Equiv.symm_symm,e.symm_apply_apply]

def replacementEquiv (e : H ≃ J) : (H → H) ≃ (J → J) where
  toFun := replacement e
  invFun := replacement e.symm
  left_inv := replacement_inverse e
  right_inv := replacement_inverse e.symm

theorem replacement_layer (e : H ≃ J) (r : H → H) (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    mapClosingLayer (replacement e r) n (mapClosingLayer e n s) =
      mapClosingLayer e n (mapClosingLayer r n s) := by
  rw [mapClosingLayer_comp,mapClosingLayer_comp]
  have eq : replacement e r ∘ e = e ∘ r := funext (replacement_apply e r)
  rw [eq]

theorem replacementChecks_iff (e : H ≃ J) (shape : InputShape H) (other : InputShape J)
    (same : ∀ p h k, other p (e h) (e k) = shape p h k)
    (M : Recognizer Graph G) (graph : H → G) (otherGraph : J → G)
    (graphSame : ∀ h, otherGraph (e h) = graph h)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q) (otherQ : J → Q)
    (qSame : ∀ h, otherQ (e h) = q h)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) :
    ReplacementChecks other M otherGraph step otherQ (policy e out) (replacement e r) ↔
      ReplacementChecks shape M graph step q out r := by
  have views (p : Proc) (s t : ClosingLayer H I₁ I₂ D) := layerShape_map e shape other same D p s t
  have graphLabels := labels_map e (fun g a (_ : O₁ × O₂) => M.step g a.2.2) graph otherGraph graphSame out
  have labels := labels_map e step q otherQ qSame out
  constructor
  · rintro ⟨preserves,states⟩
    constructor
    · intro p s t eq
      have mapped := preserves p (mapClosingLayer e D s) (mapClosingLayer e D t) (by rwa [views])
      simpa only [replacement_layer,views] using mapped
    · intro n s
      have mapped := states n (mapClosingLayer e n.val s)
      simpa only [replacement_layer,graphLabels,labels] using mapped
  · rintro ⟨preserves,states⟩
    constructor
    · intro p s t eq
      obtain ⟨a,rfl⟩ := (layerEquiv (I₁:=I₁) (I₂:=I₂) e D).surjective s
      obtain ⟨b,rfl⟩ := (layerEquiv (I₁:=I₁) (I₂:=I₂) e D).surjective t
      change closingLayerShape other D p (mapClosingLayer e D a) (mapClosingLayer e D b) = true at eq
      change closingLayerShape other D p (mapClosingLayer (replacement e r) D (mapClosingLayer e D a))
        (mapClosingLayer (replacement e r) D (mapClosingLayer e D b)) = true
      rw [replacement_layer,replacement_layer,views]
      apply preserves p a b
      rwa [views] at eq
    · intro n s
      obtain ⟨a,rfl⟩ := (layerEquiv (I₁:=I₁) (I₂:=I₂) e n.val).surjective s
      simpa only [layerEquiv,Equiv.coe_fn_mk,replacement_layer,graphLabels,labels] using states n a

theorem replacement_image_card [Fintype H] [Fintype J] [DecidableEq H] [DecidableEq J]
    (e : H ≃ J) (r : H → H) :
    (Finset.univ.image (replacement e r)).card = (Finset.univ.image r).card := by
  have eq : Finset.univ.image (replacement e r) = (Finset.univ.image r).image e := by
    ext j
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨r (e.symm k),⟨e.symm k,rfl⟩,rfl⟩
    · rintro ⟨_,⟨h,rfl⟩,rfl⟩
      exact ⟨e h,replacement_apply e r h⟩
  rw [eq,Finset.card_image_of_injective _ e.injective]

variable [Fintype H] [Fintype J] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq H] [DecidableEq J] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]

/-- Exactly the same width W is retained, and both directions of legal
move membership are checked, including every intermediate automaton state. -/
theorem legalMoves_transport (e : H ≃ J) (shape : InputShape H) (other : InputShape J)
    (same : ∀ p h k, other p (e h) (e k) = shape p h k)
    (M : Recognizer Graph G) (graph : H → G) (otherGraph : J → G)
    (graphSame : ∀ h, otherGraph (e h) = graph h)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q : H → Q) (otherQ : J → Q)
    (qSame : ∀ h, otherQ (e h) = q h) (W : Nat)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) :
    (policy e out,replacement e r) ∈ legalMoves other M otherGraph step otherQ D W ↔
      (out,r) ∈ legalMoves shape M graph step q D W := by
  rw [legalMoves_exact,legalMoves_exact,coherent_iff e shape other same,
    replacementChecks_iff e shape other same M graph otherGraph graphSame step q otherQ qSame,
    replacement_image_card]

end Characterisation.ComponentGames.Representation
