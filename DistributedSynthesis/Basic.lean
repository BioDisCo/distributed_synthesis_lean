/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-! Shared basic types for the real_model formalization. -/

namespace DistributedSynthesis

/-- The two processes of the paper. -/
inductive Proc where
  | one
  | two
  deriving DecidableEq, Repr

instance : Fintype Proc where
  elems := {Proc.one, Proc.two}
  complete := by
    intro p
    cases p <;> simp

namespace Proc

/-- The other process. -/
def other : Proc -> Proc
  | one => two
  | two => one

@[simp]
theorem other_other (p : Proc) : p.other.other = p := by
  cases p <;> rfl

end Proc

/-- The three possible communication graphs in a synchronous round. Each
process retains its own information; the constructors specify which messages
between distinct processes are delivered. -/
inductive Graph where
  /-- Only the message from process two to process one is delivered. -/
  | left
  /-- Only the message from process one to process two is delivered. -/
  | right
  /-- Both messages between the processes are delivered. -/
  | both
  deriving DecidableEq, Repr

instance : Fintype Graph where
  elems := {Graph.left, Graph.right, Graph.both}
  complete := by
    intro g
    cases g <;> simp

/-- The local receipt bit recorded in a full view. -/
inductive ReceiptTag where
  | recv
  | noRecv
  deriving DecidableEq, Repr

instance : Fintype ReceiptTag where
  elems := {ReceiptTag.recv, ReceiptTag.noRecv}
  complete := by
    intro r
    cases r <;> simp

end DistributedSynthesis
