/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.List.Induction
import DistributedSynthesis.Formalizations.Lemma.LemHistoryembedding

/-!
# Past receipt bits

This file starts the formalization of Lemma `lem:pastreceipt` from `paper.tex`.
It proves the immediate one-step recovery statement used in the paper proof.
-/

namespace DistributedSynthesis

universe u v x y

/-- Rewind a non-fringe view by repeatedly deleting the newest round. -/
def rewindNonFringe {In₁ : Type u} {In₂ : Type v} {p : Proc} :
    Nat -> NonFringeView In₁ In₂ p -> NonFringeView In₁ In₂ p
  | 0, nf => nf
  | n + 1, nf => rewindNonFringe n nf.previousNonFringe

/--
After one additional round, the previous full view is recoverable from the new
non-fringe view.
-/
theorem previousView_embeds_in_next_nonFringe
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentNonFringe p (History.append h r)).previousView = currentView p h :=
  previousView_from_nonFringe_append p h r

/--
After one additional round, the previous receipt tag is computable from the new
non-fringe view alone.
-/
theorem previousReceiptTag_computable_from_next_nonFringe
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    (currentNonFringe p (History.append h r)).previousView.receiptTag =
      (currentView p h).receiptTag :=
  previousReceiptTag_from_nonFringe_append p h r

/-- Rewinding across a suffix recovers the earlier non-fringe view. -/
theorem rewindNonFringe_append_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂) :
    rewindNonFringe suffix.length (currentNonFringe p (h ++ suffix)) = currentNonFringe p h := by
  induction suffix using List.reverseRecOn generalizing h with
  | nil =>
      simp [rewindNonFringe, History.length]
  | append_singleton suffix r ih =>
      calc
        rewindNonFringe (List.length (suffix ++ [r])) (currentNonFringe p (h ++ (suffix ++ [r])))
            = rewindNonFringe suffix.length
                ((currentNonFringe p (History.append (h ++ suffix) r)).previousNonFringe) := by
                  simp [rewindNonFringe, History.append, List.length_append]
        _ = rewindNonFringe suffix.length (currentNonFringe p (h ++ suffix)) := by
              rw [previousNonFringe_from_nonFringe_append p (h ++ suffix) r]
        _ = currentNonFringe p h := ih h

/--
After any nonempty suffix, rewinding the final non-fringe view back to the
first new round recovers the older full view.
-/
theorem previousView_computable_from_later_nonFringe
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂) :
    (rewindNonFringe suffix.length (currentNonFringe p (History.append h r ++ suffix))).previousView =
      currentView p h := by
  rw [rewindNonFringe_append_suffix]
  exact previousView_from_nonFringe_append p h r

/--
After any nonempty suffix, the older receipt tag is computable from the final
non-fringe view by rewinding finitely many rounds.
-/
theorem previousReceiptTag_computable_from_later_nonFringe
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂) :
    (rewindNonFringe suffix.length (currentNonFringe p (History.append h r ++ suffix))).previousView.receiptTag =
      (currentView p h).receiptTag := by
  rw [previousView_computable_from_later_nonFringe]

/--
Paper-facing packaged form of `lem:pastreceipt`: after one later round and any
additional suffix, rewinding the final non-fringe view recovers both the older
full view and its receipt tag.
-/
theorem past_receipt_bits_embed
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂) :
    (rewindNonFringe suffix.length (currentNonFringe p (History.append h r ++ suffix))).previousView =
      currentView p h ∧
    (rewindNonFringe suffix.length (currentNonFringe p (History.append h r ++ suffix))).previousView.receiptTag =
      (currentView p h).receiptTag := by
  exact ⟨
    previousView_computable_from_later_nonFringe p h r suffix,
    previousReceiptTag_computable_from_later_nonFringe p h r suffix
  ⟩

end DistributedSynthesis
