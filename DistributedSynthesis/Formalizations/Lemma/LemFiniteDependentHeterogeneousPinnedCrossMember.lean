/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPinnedPreselection

/-!
# Cross-member readback from dependent root-pinned preselection

An orientation switch compares two receiver-side predictions: a closing
coordinate of one hidden block interpretation and an informed coordinate of
another.  `root_sender_eq_receiver` handles blind/receiver seams.  The theorem
below is its receiver/receiver companion.

Because all dependent receiver roots are pinned before one finite-family
narrowing, any semantic equality between arbitrary projections of two
possibly differently typed receiver outputs survives literally in the two
narrowed member records.  The keys remain proof-side receiver choices; no key
or hierarchy side is exposed to the shared sender.
-/

namespace DistributedSynthesis

universe k u v x y w z

noncomputable section

variable {Key : Type k} {RIn : Type u} {SIn : Type v}
variable {ROut : Key → Type x} {SOut : Type y}
variable [Inhabited Key] [Fintype Key] [DecidableEq Key]
variable [Inhabited RIn] [Inhabited SIn] [Fintype RIn] [Fintype SIn]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [(key : Key) → Inhabited (ROut key)]
variable [(key : Key) → Fintype (ROut key)] [Fintype SOut]

omit [Inhabited Key] in
/-- A semantic equality between projections of two receiver candidates is
preserved at their two narrowed roots.  The result type `Projected` need not
be finite: it is used only in this proof-side readback statement. -/
theorem
    FiniteDependentHeterogeneousPinnedTable.root_receiver_eq_receiver
    {Projected : Type z}
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (left right : Key) (input : RIn × SIn)
    (projectLeft : ROut left → Projected)
    (projectRight : ROut right → Projected)
    (hsemantic :
      projectLeft (receiver left [] input) =
        projectRight (receiver right [] input)) :
    projectLeft
        ((narrowedRecord
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender left)
          ((table.memberController left).labeledTree [])
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender left).initial input).2.1 left) =
      projectRight
        ((narrowedRecord
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender right)
          ((table.memberController right).labeledTree [])
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender right).initial input).2.1 right) := by
  rw [table.member_root_receiver left input,
    table.member_root_receiver right input]
  exact hsemantic

omit [Inhabited Key] in
/-- Same statement with the semantic equality oriented in the opposite
direction, useful when the two tail projections are presented in
closing/informed order. -/
theorem
    FiniteDependentHeterogeneousPinnedTable.root_receiver_eq_receiver_of_eq
    {Projected : Type z}
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (left right : Key) (input : RIn × SIn)
    (projectLeft : ROut left → Projected)
    (projectRight : ROut right → Projected)
    (hsemantic :
      projectRight (receiver right [] input) =
        projectLeft (receiver left [] input)) :
    projectLeft
        ((narrowedRecord
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender left)
          ((table.memberController left).labeledTree [])
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender left).initial input).2.1 left) =
      projectRight
        ((narrowedRecord
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender right)
          ((table.memberController right).labeledTree [])
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender right).initial input).2.1 right) :=
  table.root_receiver_eq_receiver left right input projectLeft projectRight
    hsemantic.symm

end

end DistributedSynthesis
