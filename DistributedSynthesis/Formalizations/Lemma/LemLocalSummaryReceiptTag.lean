/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Recording the locally visible receipt tag in a finite summary

A process need not know whether the current graph is strict or simultaneous,
and in particular it cannot know whether it is the strict leader.  It does,
however, know whether its own current view was obtained by `recv` or
`noRecv`.  This file packages that one locally visible bit around any finite
local-summary automaton.

The wrapper is useful at an alternating activation boundary: the receiver row
of a freshly delivered block controller depends on the receiver's *previous*
receipt tag.  Remembering that tag is local perfect-recall information and
does not reveal the graph or an orientation.
-/

namespace DistributedSynthesis

universe u v o

namespace LocalSummaryAutomaton

variable {In₁ : Type u} {In₂ : Type v}

/-- Add the outer receipt tag of the represented local view to every summary.
The first component evolves exactly as in `M`; the second component is set by
the locally selected `recv`/`noRecv` transition. -/
def withReceiptTag
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) :
    LocalSummaryAutomaton In₁ In₂ where
  Summary d := M.Summary d × ReceiptTag
  finite d := inferInstance
  initial d := (M.initial d, .noRecv)
  stepNoRecv d self input := (M.stepNoRecv d self.1 input, .noRecv)
  stepRecv d self inputSelf other inputOther :=
    (M.stepRecv d self.1 inputSelf other.1 inputOther, .recv)

@[simp] theorem withReceiptTag_initial_fst
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc) :
    (M.withReceiptTag.initial d).1 = M.initial d :=
  rfl

@[simp] theorem withReceiptTag_initial_snd
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc) :
    (M.withReceiptTag.initial d).2 = ReceiptTag.noRecv :=
  rfl

@[simp] theorem withReceiptTag_stepNoRecv_fst
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (self : M.withReceiptTag.Summary d) (input : PSum In₁ In₂) :
    (M.withReceiptTag.stepNoRecv d self input).1 =
      M.stepNoRecv d self.1 input :=
  rfl

@[simp] theorem withReceiptTag_stepNoRecv_snd
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (self : M.withReceiptTag.Summary d) (input : PSum In₁ In₂) :
    (M.withReceiptTag.stepNoRecv d self input).2 = ReceiptTag.noRecv :=
  rfl

@[simp] theorem withReceiptTag_stepRecv_fst
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (self : M.withReceiptTag.Summary d) (inputSelf : PSum In₁ In₂)
    (other : M.withReceiptTag.Summary d.other)
    (inputOther : PSum In₁ In₂) :
    (M.withReceiptTag.stepRecv d self inputSelf other inputOther).1 =
      M.stepRecv d self.1 inputSelf other.1 inputOther :=
  rfl

@[simp] theorem withReceiptTag_stepRecv_snd
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (d : Proc)
    (self : M.withReceiptTag.Summary d) (inputSelf : PSum In₁ In₂)
    (other : M.withReceiptTag.Summary d.other)
    (inputOther : PSum In₁ In₂) :
    (M.withReceiptTag.stepRecv d self inputSelf other inputOther).2 =
      ReceiptTag.recv :=
  rfl

/-- The payload component of the tagged read is the original summary read. -/
@[simp] theorem withReceiptTag_read_fst
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) :
    {d : Proc} → (view : View In₁ In₂ d) →
      (M.withReceiptTag.read view).1 = M.read view
  | _, .empty _ => rfl
  | _, .noRecv previous input => by
      simp only [read_noRecv, withReceiptTag_stepNoRecv_fst]
      rw [withReceiptTag_read_fst M previous]
  | _, .recv previous inputSelf other inputOther => by
      simp only [read_recv, withReceiptTag_stepRecv_fst]
      rw [withReceiptTag_read_fst M previous,
        withReceiptTag_read_fst M other]

/-- The tag component is exactly the outer constructor visible in the local
view. -/
@[simp] theorem withReceiptTag_read_snd
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) :
    {d : Proc} → (view : View In₁ In₂ d) →
      (M.withReceiptTag.read view).2 = view.receiptTag
  | _, .empty _ => rfl
  | _, .noRecv _ _ => rfl
  | _, .recv _ _ _ _ => rfl

/-- Exact readback equation for the tagged wrapper. -/
@[simp] theorem withReceiptTag_read
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {d : Proc} (view : View In₁ In₂ d) :
    M.withReceiptTag.read view = (M.read view, view.receiptTag) := by
  apply Prod.ext
  · exact withReceiptTag_read_fst M view
  · exact withReceiptTag_read_snd M view

end LocalSummaryAutomaton

end DistributedSynthesis
