/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanTransition
import DistributedSynthesis.Library.Automata.EncodedPitermanCreation
import DistributedSynthesis.Library.Automata.EncodedPitermanGreen

/-! # Composition of the six numeric Piterman stages

The nodes removed by stage 4 are saved before stage 5. The union with the
stage-5 empty nodes is computed from the stage-4 tree and reused for stage 6.
All intermediate stages preserve the canonical code representation exactly.
-/

namespace DistributedSynthesis.EncodedPitermanStep
open EncodedPitermanStates
abbrev Input := Nat × EncodedPitermanTransition.Edges × List Nat × Code

def afterStage2 (x : Input) : Code :=
  EncodedPitermanCreation.stage2
    (x.1, x.2.2.1, EncodedPitermanTransition.stage1 x.1 x.2.1 x.2.2.2)
def beforeGreen (x : Input) : Code := EncodedPitermanPruning.stage3 (x.1, afterStage2 x)
def afterGreen (x : Input) : Code := EncodedPitermanGreen.stage4 (x.1, beforeGreen x)
def greenRemoved (x : Input) : List Nat := EncodedPitermanGreen.removedNodes (x.1, beforeGreen x)
def afterEmpty (x : Input) : Code := EncodedPitermanDeletion.stage5 (x.1, afterGreen x) (greenRemoved x)
def allRemoved (x : Input) : List Nat := EncodedPitermanDeletion.removed (x.1, afterGreen x) (greenRemoved x)
def transition (x : Input) : Code := EncodedPitermanDeletion.stage6 (x.1, afterEmpty x) (allRemoved x)
def step (x : Input) : Option Code :=
  if FiniteSubsets.normalize x.1 (readLabel (afterGreen x) 0) = [] then none else some (transition x)

private theorem n_primrec : Primrec (fun x : Input => x.1) := Primrec.fst
theorem afterStage2_primrec : Primrec afterStage2 :=
  EncodedPitermanCreation.stage2_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (EncodedPitermanTransition.stage1_primrec.comp (Primrec.fst.pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))
theorem beforeGreen_primrec : Primrec beforeGreen :=
  EncodedPitermanPruning.stage3_primrec.comp (n_primrec.pair afterStage2_primrec)
theorem afterGreen_primrec : Primrec afterGreen :=
  EncodedPitermanGreen.stage4_primrec.comp (n_primrec.pair beforeGreen_primrec)
theorem greenRemoved_primrec : Primrec greenRemoved :=
  EncodedPitermanGreen.removedNodes_primrec.comp (n_primrec.pair beforeGreen_primrec)
theorem afterEmpty_primrec : Primrec afterEmpty :=
  EncodedPitermanDeletion.stage5_primrec.comp (n_primrec.pair afterGreen_primrec) greenRemoved_primrec
theorem allRemoved_primrec : Primrec allRemoved :=
  EncodedPitermanDeletion.removed_primrec.comp (n_primrec.pair afterGreen_primrec) greenRemoved_primrec
theorem transition_primrec : Primrec transition :=
  EncodedPitermanDeletion.stage6_primrec.comp (n_primrec.pair afterEmpty_primrec) allRemoved_primrec
theorem step_primrec : Primrec step :=
  Primrec.ite (Primrec.eq.comp (FiniteSubsets.normalize_primrec.comp n_primrec
    (readLabel_primrec.comp afterGreen_primrec (Primrec.const 0))) (Primrec.const []))
    (Primrec.const none) (Primrec.option_some.comp transition_primrec)

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State))
  (decStep : ∀ q a r, Decidable (A.step q a r)) (decAccept : DecidablePred A.accepting)
  (edges : EncodedPitermanTransition.Edges) (acc : List Nat) (letter : L)
  (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
  (ha : ∀ q, (number q).val ∈ acc ↔ A.accepting q)
  (tree : CompactTreeData A) (htree : tree.WellFormed A)

@[reducible] def input : Input := (Fintype.card A.State, edges, acc, encode A number tree)
local notation "x" => input A number edges acc tree
local notation "P" => Computable.transitionPlan A decStep decAccept tree htree letter

private theorem transport_cancel {α : Sort*} {β : α → Sort*} {a b : α}
    (h : a = b) (p : β a) : (h.symm ▸ (h ▸ p)) = p := by
  cases h
  rfl

include he ha in
set_option maxHeartbeats 800000 in
theorem afterStage2_encode :
    afterStage2 x = encode A number (Computable.afterStage2 A decStep decAccept tree letter P) := by
  obtain ⟨_, _, _, _, _, hb, hi, hc, _, _, _⟩ := htree
  change EncodedPitermanCreation.stage2 (Fintype.card A.State, acc,
    EncodedPitermanTransition.stage1 (Fintype.card A.State) edges (encode A number tree)) = _
  rw [EncodedPitermanTransition.stage1_encode A number edges letter he decStep tree]
  rw [EncodedPitermanCreation.stage2_encode A number acc decAccept ha
    (Computable.stage1 A decStep tree letter) hb hi hc]
  apply congrArg (encode A number)
  simp only [Computable.afterStage2, Computable.transitionPlan, transport_cancel]

include he ha in
theorem beforeGreen_encode :
    beforeGreen x = encode A number
      (Computable.stage3 A (Computable.afterStage2 A decStep decAccept tree letter P)) := by
  unfold beforeGreen
  rw [afterStage2_encode A number decStep decAccept edges acc letter he ha tree htree]
  exact EncodedPitermanPruning.stage3_encode A number _

include he ha in
theorem afterGreen_encode :
    afterGreen x = encode A number (Computable.afterStage4 A decStep decAccept tree letter P) := by
  unfold afterGreen
  rw [beforeGreen_encode A number decStep decAccept edges acc letter he ha tree htree]
  exact EncodedPitermanGreen.stage4_encode A number _

include he ha in
theorem transition_encode :
    transition x = encode A number (Computable.transitionWithPlan A decStep decAccept tree letter P) := by
  have h3 := beforeGreen_encode A number decStep decAccept edges acc letter he ha tree htree
  have h4 := afterGreen_encode A number decStep decAccept edges acc letter he ha tree htree
  unfold transition afterEmpty allRemoved greenRemoved
  rw [h3, h4]
  rw [EncodedPitermanGreen.removedNodes_correct A number]
  rw [EncodedPitermanDeletion.stage5_encode A number, EncodedPitermanDeletion.removed_correct A number]
  rw [EncodedPitermanDeletion.stage6_encode A number]
  rfl

include he ha in
theorem root_empty_iff :
    FiniteSubsets.normalize x.1 (readLabel (afterGreen x) 0) = [] ↔
      (Computable.afterStage4 A decStep decAccept tree letter P).label (root A) = ∅ := by
  rw [afterGreen_encode A number decStep decAccept edges acc letter he ha tree htree]
  have hzero : (root A).val = 0 := rfl
  rw [← hzero, readLabel_encode]
  change FiniteSubsets.normalize (Fintype.card A.State) (encodeLabel A number _) = [] ↔ _
  simpa only [encodeLabel, FiniteSubsets.normalize_encode] using encodeLabel_eq_nil A number
    ((Computable.afterStage4 A decStep decAccept tree letter P).label (root A))

include he ha in
/-- Complete live-step agreement, including the rejecting sink test. -/
theorem step_correct :
    step x = (Computable.liveTransition A decStep decAccept ⟨tree, htree⟩ letter).map
      (fun live => encode A number live.val) := by
  have hroot := root_empty_iff A number decStep decAccept edges acc letter he ha tree htree
  by_cases h : (Computable.afterStage4 A decStep decAccept tree letter P).label (root A) = ∅
  · have hn := hroot.mpr h
    simp [step, hn, Computable.liveTransition, h]
  · have hn := mt hroot.mp h
    simp only [step, if_neg hn, Computable.liveTransition, dif_pos h, Option.map_some]
    exact congrArg some (transition_encode A number decStep decAccept edges acc letter he ha tree htree)

end DistributedSynthesis.EncodedPitermanStep
