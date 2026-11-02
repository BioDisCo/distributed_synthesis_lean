/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSymmetricDelayedCarrier
import DistributedSynthesis.Formalizations.Lemma.LemFiniteThreeColorFreshId

/-!
# Fresh three-color installation for the symmetric delayed carrier

At a simultaneous receive, both endpoints can inspect their own finite
carrier and the delivered finite carrier.  They install new forks using one
common `Fin 3` identifier, chosen fresh from the at most two old identifiers.
The choice is symmetric, so the endpoints compute the same identifier even
though their local argument order is reversed.
-/

namespace DistributedSynthesis

namespace FiniteSymmetricDelayedCarrier

universe u v

variable {Control : Type u} {Delivered : Type v}

/-- The new simultaneous-receive ID computed from the two old carriers. -/
def freshId
    (one : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (two : FiniteSymmetricDelayedCarrier (Fin 3) Delivered) : Fin 3 :=
  freshDelayedForkColor one.forkId? two.forkId?

/-- Swapping the endpoint order does not change the installed ID. -/
theorem freshId_comm
    (one : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (two : FiniteSymmetricDelayedCarrier (Fin 3) Delivered) :
    freshId one two = freshId two one :=
  freshDelayedForkColor_comm one.forkId? two.forkId?

/-- A new simultaneous fork cannot alias an old unresolved fork on the first
endpoint. -/
theorem freshId_ne_left_fork
    (id : Fin 3) (old : FiniteDelayedFork Control)
    (two : FiniteSymmetricDelayedCarrier (Fin 3) Delivered) :
    freshId (.fork id old) two ≠ id := by
  exact freshDelayedForkColor_some_left_ne id two.forkId?

/-- A new simultaneous fork cannot alias an old unresolved fork on the
second endpoint. -/
theorem freshId_ne_right_fork
    (one : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (id : Fin 3) (old : FiniteDelayedFork Delivered) :
    freshId one (.fork id old) ≠ id := by
  exact freshDelayedForkColor_some_right_ne one.forkId? id

/-- Install the endpoint-local half of a fresh simultaneous fork. -/
def installBothLocal
    (own : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (delivered : FiniteSymmetricDelayedCarrier (Fin 3) Delivered)
    (next : FiniteDelayedFork Control) :
    FiniteSymmetricDelayedCarrier (Fin 3) Control :=
  .fork (freshId own delivered) next

@[simp] theorem forkId?_installBothLocal
    (own : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (delivered : FiniteSymmetricDelayedCarrier (Fin 3) Delivered)
    (next : FiniteDelayedFork Control) :
    (installBothLocal own delivered next).forkId? =
      some (freshId own delivered) :=
  rfl

/-- The two locally installed halves carry the same identifier. -/
theorem installBothLocal_ids_agree
    (one : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (two : FiniteSymmetricDelayedCarrier (Fin 3) Delivered)
    (nextOne : FiniteDelayedFork Control)
    (nextTwo : FiniteDelayedFork Delivered) :
    (installBothLocal one two nextOne).forkId? =
      (installBothLocal two one nextTwo).forkId? := by
  simp only [forkId?_installBothLocal, Option.some.injEq]
  exact freshId_comm one two

/-- If the first endpoint already carried an old fork, the freshly installed
ID differs from it. -/
theorem installBothLocal_id_ne_left_old
    (id : Fin 3) (old : FiniteDelayedFork Control)
    (two : FiniteSymmetricDelayedCarrier (Fin 3) Delivered)
    (next : FiniteDelayedFork Control) :
    (installBothLocal (.fork id old) two next).forkId? ≠ some id := by
  intro heq
  exact freshId_ne_left_fork id old two (Option.some.inj heq)

/-- If the delivered endpoint carried an old fork, the freshly installed ID
differs from that old ID as well. -/
theorem installBothLocal_id_ne_right_old
    (one : FiniteSymmetricDelayedCarrier (Fin 3) Control)
    (id : Fin 3) (old : FiniteDelayedFork Delivered)
    (next : FiniteDelayedFork Control) :
    (installBothLocal one (.fork id old) next).forkId? ≠ some id := by
  intro heq
  exact freshId_ne_right_fork one id old (Option.some.inj heq)

end FiniteSymmetricDelayedCarrier

end DistributedSynthesis
