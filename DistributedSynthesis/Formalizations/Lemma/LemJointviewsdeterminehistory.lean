/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.List.Induction
import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# Joint views determine the input/graph history

The literal paper statement says that the pair of current full views determines
the entire history. Under the present model, outputs are not encoded in the
views, so the exact recoverable content is the graph sequence together with the
two input sequences. This is the part used downstream in the main proof chain.
-/

namespace DistributedSynthesis

universe u v x y

/-- Extend a decoded prefix by one round of graph and inputs. -/
def extendDecodedHistory
    {In₁ : Type u} {In₂ : Type v}
    (decoded : List Graph × List In₁ × List In₂)
    (g : Graph) (xOne : In₁) (xTwo : In₂) :
    List Graph × List In₁ × List In₂ :=
  (decoded.1 ++ [g], decoded.2.1 ++ [xOne], decoded.2.2 ++ [xTwo])

/--
Decode the graph and input history carried by a pair of full views. Invalid
view pairs return `none`; valid pairs return the unique recoverable data.
-/
def decodeJointViews
    {In₁ : Type u} {In₂ : Type v} :
    View In₁ In₂ Proc.one -> View In₁ In₂ Proc.two ->
      Option (List Graph × List In₁ × List In₂)
  | .empty _, .empty _ => some ([], [], [])
  | .recv prevOne (.inl xOne) prevTwo (.inr xTwo), .noRecv _ (.inr _) =>
      Option.map (fun decoded => extendDecodedHistory decoded .left xOne xTwo)
        (decodeJointViews prevOne prevTwo)
  | .noRecv prevOne (.inl xOne), .recv prevTwo (.inr xTwo) _ (.inl _) =>
      Option.map (fun decoded => extendDecodedHistory decoded .right xOne xTwo)
        (decodeJointViews prevOne prevTwo)
  | .recv prevOne (.inl xOne) prevTwo (.inr xTwo),
      .recv _ (.inr _) _ (.inl _) =>
      Option.map (fun decoded => extendDecodedHistory decoded .both xOne xTwo)
        (decodeJointViews prevOne prevTwo)
  | _, _ => none

/-- Decoding the actual current views of a history recovers its graphs and inputs. -/
theorem decodeJointViews_current
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    decodeJointViews (currentView Proc.one h) (currentView Proc.two h) =
      some (History.graphSequence h, h.map RoundRecord.inputOne, h.map RoundRecord.inputTwo) := by
  induction h using List.reverseRecOn with
  | nil =>
      simp [decodeJointViews, History.graphSequence, currentView, viewPair]
  | append_singleton h r ih =>
      change decodeJointViews (currentView Proc.one (History.append h r))
          (currentView Proc.two (History.append h r)) =
        some
          (History.graphSequence (History.append h r),
            List.map RoundRecord.inputOne (History.append h r),
            List.map RoundRecord.inputTwo (History.append h r))
      rw [currentView_one_append, currentView_two_append]
      cases hGraph : r.graph <;>
        simp [decodeJointViews, extendDecodedHistory, History.append,
          History.graphSequence, hGraph, ih]

/--
Corrected form of `lem:jointviewsdeterminehistory`: equality of both current
views forces equality of the graph sequence and both input sequences.
-/
theorem jointViews_determine_inputGraphHistory
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hviewOne : currentView Proc.one h = currentView Proc.one h')
    (hviewTwo : currentView Proc.two h = currentView Proc.two h') :
    History.graphSequence h = History.graphSequence h' ∧
      h.map RoundRecord.inputOne = h'.map RoundRecord.inputOne ∧
      h.map RoundRecord.inputTwo = h'.map RoundRecord.inputTwo := by
  have hdecode := decodeJointViews_current h
  rw [hviewOne, hviewTwo] at hdecode
  have hdecode' := decodeJointViews_current h'
  rw [hdecode'] at hdecode
  have hdecoded :
      (h'.graphSequence, List.map RoundRecord.inputOne h', List.map RoundRecord.inputTwo h') =
        (h.graphSequence, List.map RoundRecord.inputOne h, List.map RoundRecord.inputTwo h) :=
    Option.some.inj hdecode
  have hgraphs := congrArg Prod.fst hdecoded
  have hinputs := congrArg Prod.snd hdecoded
  have hinputsOne := congrArg Prod.fst hinputs
  have hinputsTwo := congrArg Prod.snd hinputs
  exact ⟨hgraphs.symm, hinputsOne.symm, hinputsTwo.symm⟩

/-- The same corrected determinacy result phrased with the existing input-sequence helpers. -/
theorem jointViews_determine_inputSequences
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hviewOne : currentView Proc.one h = currentView Proc.one h')
    (hviewTwo : currentView Proc.two h = currentView Proc.two h') :
    History.graphSequence h = History.graphSequence h' ∧
      History.inputSequence Proc.one h = History.inputSequence Proc.one h' ∧
      History.inputSequence Proc.two h = History.inputSequence Proc.two h' := by
  obtain ⟨hgraphs, hinputsOne, hinputsTwo⟩ :=
    jointViews_determine_inputGraphHistory h h' hviewOne hviewTwo
  refine ⟨hgraphs, ?_, ?_⟩
  · simp [History.inputSequence, hinputsOne]
  · simp [History.inputSequence, hinputsTwo]

/--
Paper-facing packaged form of `lem:jointviewsdeterminehistory` under the
present model: joint views determine the graph sequence and both input
sequences. Outputs are not encoded in views, so they are intentionally not part
of this recovered history data.
-/
theorem jointViews_determine_history
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hviewOne : currentView Proc.one h = currentView Proc.one h')
    (hviewTwo : currentView Proc.two h = currentView Proc.two h') :
    History.graphSequence h = History.graphSequence h' ∧
      History.inputSequence Proc.one h = History.inputSequence Proc.one h' ∧
      History.inputSequence Proc.two h = History.inputSequence Proc.two h' :=
  jointViews_determine_inputSequences h h' hviewOne hviewTwo

/--
Joint views alone cannot determine process 1's output trace: outputs are not
stored in the view constructors.
-/
theorem jointViews_do_not_determine_outputSequence_one
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₂]
    {output output' : Out₁}
    (houtput : output ≠ output') :
    ∃ h h' : History In₁ In₂ Graph Out₁ Out₂,
      currentView Proc.one h = currentView Proc.one h' ∧
        currentView Proc.two h = currentView Proc.two h' ∧
        History.outputSequence Proc.one h ≠
          History.outputSequence Proc.one h' := by
  let round : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
    { inputOne := default
      inputTwo := default
      graph := Graph.both
      outputOne := output
      outputTwo := default }
  let round' : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
    { inputOne := default
      inputTwo := default
      graph := Graph.both
      outputOne := output'
      outputTwo := default }
  refine ⟨[round], [round'], ?_, ?_, ?_⟩
  · simp [currentView, viewPair, advanceViews, round, round']
  · simp [currentView, viewPair, advanceViews, round, round']
  · intro hseq
    simp [History.outputSequence, round, round'] at hseq
    exact houtput hseq

/--
Joint views alone cannot determine process 2's output trace: outputs are not
stored in the view constructors.
-/
theorem jointViews_do_not_determine_outputSequence_two
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    {output output' : Out₂}
    (houtput : output ≠ output') :
    ∃ h h' : History In₁ In₂ Graph Out₁ Out₂,
      currentView Proc.one h = currentView Proc.one h' ∧
        currentView Proc.two h = currentView Proc.two h' ∧
        History.outputSequence Proc.two h ≠
          History.outputSequence Proc.two h' := by
  let round : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
    { inputOne := default
      inputTwo := default
      graph := Graph.both
      outputOne := default
      outputTwo := output }
  let round' : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
    { inputOne := default
      inputTwo := default
      graph := Graph.both
      outputOne := default
      outputTwo := output' }
  refine ⟨[round], [round'], ?_, ?_, ?_⟩
  · simp [currentView, viewPair, advanceViews, round, round']
  · simp [currentView, viewPair, advanceViews, round, round']
  · intro hseq
    simp [History.outputSequence, round, round'] at hseq
    exact houtput hseq

end DistributedSynthesis
