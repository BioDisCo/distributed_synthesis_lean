/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalPostInvariant

/-!
# Fail-fast alternating-diamond audit

The exact-pair operational carrier passes reconstruction at a receive, but a
complete execution invariant would also have to identify the states obtained
along `both; right; left` (and its mirror).  This file names that stronger
law and proves that it is false for the exceptional-to-recurrent seam: the
double reversal is already an ordinary bank phase, whereas ordinary
continuation remains in the exceptional first phase.

Consequently the operational files remain useful verified decoder machinery,
but they are not an unconditional `ReadbackUpgrade`.  A successful narrowing
must preserve local continuation equivalence (or retain a finite set of such
continuations), rather than only the one-round output profile.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- The state equality that the tempting exact-pair invariant would need on
the left-anchored alternating diamond. -/
def ProfiledAlternatingLeftDiamond : Prop :=
  ∀ (phase right : ProfiledMatchedPhase A firstBank), phase.IsLeft →
    ∀ (move nextMove : In₁ × In₂),
      (phase.reverseLeftToRight A firstBank (move.2, move.1) false).2 =
          some right →
      (right.reverseRightToLeft A firstBank nextMove false).2 =
        some (((phase.continue A firstBank move).2.continue A firstBank
          nextMove).2)

/-- A successful double reversal from an exceptional first-left phase cannot
equal its twice-continued phase: the former is `bankLeft`, while the latter
is still `firstLeft`.  This is the kernel-checked failure certificate for the
exact-state alternating diamond. -/
theorem firstLeft_doubleReversal_ne_continue
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (sameKey : receiver.1 = owner.1)
    (move nextMove : In₁ × In₂)
    (right left : ProfiledMatchedPhase A firstBank)
    (hright :
      ((ProfiledMatchedPhase.firstLeft receiver owner sameKey).reverseLeftToRight
        A firstBank (move.2, move.1) false).2 = some right)
    (hleft : (right.reverseRightToLeft A firstBank nextMove false).2 =
      some left) :
    left ≠
      ((((ProfiledMatchedPhase.firstLeft receiver owner sameKey).continue
        A firstBank move).2.continue A firstBank nextMove).2) := by
  simp only [ProfiledMatchedPhase.reverseLeftToRight] at hright
  split at hright
  next hOne hTwo =>
    cases Option.some.inj hright
    simp only [ProfiledMatchedPhase.reverseRightToLeft] at hleft
    split at hleft
    next hOne' hTwo' =>
      cases Option.some.inj hleft
      simp [ProfiledMatchedPhase.continue]
    all_goals simp at hleft
  all_goals simp at hright

end


end


end DetParityAutomaton

end DistributedSynthesis
