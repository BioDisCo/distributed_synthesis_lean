/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedMove
import DistributedSynthesis.Formalizations.Lemma.LemFinitePolicyAllowedTargetBlockMonitor

/-!
# Row-exact finite target tables

An `IndexedTargetReceiverOutput` stores a homogeneous target at every finite
row.  If a target itself remembers the row that selected it, a unary allowed
predicate is not enough to prevent a narrowed table from placing a target
tagged by one row in another row's cell.

This file removes that ambiguity at the type boundary.  A row-exact output
stores at row `i` a target together with the equation `targetIndex target =
i`.  The proof is erased before the old monitor reads the output.  Hence the
monitor state and objective are unchanged, while every finite table obtained
after narrowing is row-correct by construction.  The equality proof is not a
runtime observation or controller state.
-/

namespace DistributedSynthesis

universe x i t

/-- A finite receiver table whose target at each index carries the literal
index equation. -/
structure RowExactIndexedTargetReceiverOutput
    (ROut : Type x) (Index : Type i) (Target : Type t)
    (targetIndex : Target → Index) where
  physical : ROut
  target : (index : Index) → { target : Target // targetIndex target = index }

noncomputable instance rowExactIndexedTargetReceiverOutputFintype
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    [Fintype ROut] [Fintype Index] [Fintype Target] [DecidableEq Index] :
    Fintype
      (RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex) := by
  classical
  let Rep := ROut ×
    ((index : Index) → { target : Target // targetIndex target = index })
  let equivalence :
      RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex ≃
        Rep := {
    toFun := fun output ↦ (output.physical, output.target)
    invFun := fun output ↦ ⟨output.1, output.2⟩
    left_inv := by intro output; cases output; rfl
    right_inv := by intro output; cases output; rfl
  }
  exact Fintype.ofEquiv Rep equivalence.symm

/-- Erase only the index-equality proofs. -/
def RowExactIndexedTargetReceiverOutput.forgetRowProof
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    (output :
      RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex) :
    IndexedTargetReceiverOutput ROut Index Target where
  physical := output.physical
  target := fun index ↦ (output.target index).1

@[simp] theorem RowExactIndexedTargetReceiverOutput.forgetRowProof_physical
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    (output :
      RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex) :
    output.forgetRowProof.physical = output.physical :=
  rfl

@[simp] theorem RowExactIndexedTargetReceiverOutput.forgetRowProof_target
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    (output :
      RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex)
    (index : Index) :
    output.forgetRowProof.target index = (output.target index).1 :=
  rfl

/-- The selected target literally carries its table row. -/
theorem RowExactIndexedTargetReceiverOutput.target_index
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    (output :
      RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex)
    (index : Index) :
    targetIndex (output.forgetRowProof.target index) = index :=
  (output.target index).2

/-- Package an ordinary finite target table once its pointwise row equation
has been proved. -/
def RowExactIndexedTargetReceiverOutput.ofTarget
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    (physical : ROut) (target : Index → Target)
    (target_index : ∀ index, targetIndex (target index) = index) :
    RowExactIndexedTargetReceiverOutput ROut Index Target targetIndex where
  physical := physical
  target := fun index ↦ ⟨target index, target_index index⟩

@[simp] theorem RowExactIndexedTargetReceiverOutput.forgetRowProof_ofTarget
    {ROut : Type x} {Index : Type i} {Target : Type t}
    {targetIndex : Target → Index}
    (physical : ROut) (target : Index → Target)
    (target_index : ∀ index, targetIndex (target index) = index) :
    (RowExactIndexedTargetReceiverOutput.ofTarget physical target
      target_index).forgetRowProof =
        { physical := physical, target := target } := by
  rfl

end DistributedSynthesis
