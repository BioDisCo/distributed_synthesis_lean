/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderProgressRealization

/-! The persistent progress monitor rejects the postponement pattern that
passes a guard checking only winning-successor membership. -/
namespace Characterisation
open DistributedSynthesis

def postponingHandover : LeaderHandover Unit 1 1 :=
  ⟨⟨⟨1,by omega⟩,(fun _ _ _ => true),(fun _ => ())⟩,
    (fun _ => ⟨0,by omega⟩),(fun _ => ⟨1,by omega⟩)⟩

def postponingInitial : HandoverCode 1 1 := (⟨0,by omega⟩,⟨0,by omega⟩)

def postponingThread : HiddenCodeContinuityThread postponingInitial HandoverEdge
    (fun _ => (postponingHandover,())) where
  code := fun n => match n with
    | 0 => postponingInitial
    | _+1 => (⟨0,by omega⟩,⟨1,by omega⟩)
  initial := rfl
  edge := by
    intro n
    refine ⟨⟨0,by decide⟩,?_,?_⟩ <;> cases n <;> rfl

theorem handoverProgress_rejects_postponement :
    ¬ (handoverProgressSystem postponingInitial).universalRunDPA.Accepts
      (fun _ => (postponingHandover,())) := by
  intro accepted
  have winning := (handoverProgress_accepts_iff postponingInitial _).mp accepted postponingThread
  exact not_natSeqMinEvenParity_of_eventually_one
    (fun n => (postponingThread.code (n+1)).2.val) 0 (fun _ _ => rfl) winning

end Characterisation
