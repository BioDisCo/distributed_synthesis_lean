/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.WinningClosingCertificates
import DistributedSynthesis.Formalizations.Lemma.LemHiddenCodeContinuityBundle

/-! Global parity follows compatible histories across successive agreed
leaders. A handover describes one whole successor family, its predecessor
slots, and its phase minima. The hidden actual slot is never a public move. -/
namespace Characterisation
open DistributedSynthesis

/-- One joint handover outcome. The minima must include the entire ending
phase; closing certificates can carry them in their replayed annotations. -/
abbrev LeaderHandover (Q : Type) (B C : Nat) :=
  Σ target : SwitchInterface Q B,
    (Fin target.1.val → Fin (B+1)) × (Fin target.1.val → Fin (C+1))

instance leaderHandover_fintype {Q : Type} [Fintype Q] (B C : Nat) :
    Fintype (LeaderHandover Q B C) := by
  unfold LeaderHandover SwitchInterface InputShape
  infer_instance

abbrev HandoverCode (B C : Nat) := Fin (B+1) × Fin (C+1)

def handoverSlot {Q : Type} {B C : Nat} (handover : LeaderHandover Q B C)
    (i : Fin handover.1.1.val) : Fin (B+1) :=
  ⟨i.val,lt_trans i.isLt handover.1.1.isLt⟩

/-- A hidden history may continue only through its recorded predecessor.
Keeping just the set of winning target summaries would lose this constraint. -/
def HandoverEdge {Q : Type} {B C : Nat}
    (old : HandoverCode B C) (handover : LeaderHandover Q B C)
    (_ : Unit) (next : HandoverCode B C) : Prop :=
  ∃ i, handover.2.1 i = old.1 ∧ next = (handoverSlot handover i,handover.2.2 i)

/-- Read the minimum of each completed phase. This automaton and the
universal hidden-thread determinization are independent of the strategy. -/
def handoverPriorityDPA (B C : Nat) : DetParityAutomaton.{0,0} (HandoverCode B C) where
  State := Fin (C+1)
  stateFinite := inferInstance
  initial := ⟨0,by omega⟩
  step := fun _ code => code.2
  priority := Fin.val

theorem handoverPriorityDPA_accepts_iff {B C : Nat}
    (word : Nat → HandoverCode B C) :
    (handoverPriorityDPA B C).Accepts word ↔
      NatSeqMinEvenParity (fun n => (word n).2.val) := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  have tail : (fun n => (handoverPriorityDPA B C).priority
      ((handoverPriorityDPA B C).run word (1+n))) = fun n => (word n).2.val := by
    funext n
    rw [Nat.add_comm 1 n]
    rfl
  rw [← natSeqMinEvenParity_shift _ 1,tail]

noncomputable def handoverProgressSystem {Q : Type} {B C : Nat}
    (initial : HandoverCode B C) : FiniteThreadSystem.{0,0,0} (LeaderHandover Q B C × Unit) :=
  hiddenCodeContinuitySystem (handoverPriorityDPA B C) initial HandoverEdge

/-- One finite DPA checks parity across every compatible hidden history,
through arbitrarily many leader changes. It is never reset at a handover. -/
theorem handoverProgress_accepts_iff {Q : Type} {B C : Nat}
    (initial : HandoverCode B C) (word : Nat → LeaderHandover Q B C × Unit) :
    (handoverProgressSystem initial).universalRunDPA.Accepts word ↔
      ∀ thread : HiddenCodeContinuityThread initial HandoverEdge word,
        NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  rw [handoverProgressSystem,hiddenCodeContinuitySystem_universalRunDPA_accepts_iff]
  simp only [handoverPriorityDPA_accepts_iff,HiddenCodeContinuityThread.childCodeWord]

/-- Extract the parent/minimum data from the existing certificate. Root
numbering is explicit; the retained priority is part of the checked label. -/
def certificateHandover {H I₁ I₂ O₁ O₂ Q : Type} {B C D n : Nat}
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n) : LeaderHandover Q B C :=
  ⟨⟨move.1,move.2.2.2⟩,
    (fun i => slot (closingLayerRoot n (move.2.2.1 i))),
    (fun i => minimum (move.2.2.2.2 i))⟩

theorem certificateHandover_edge {H I₁ I₂ O₁ O₂ Q : Type} {B C D n : Nat}
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (old next : HandoverCode B C) :
    HandoverEdge old (certificateHandover slot minimum move) () next ↔
      ∃ i : Fin move.1.val,
        slot (closingLayerRoot n (move.2.2.1 i)) = old.1 ∧
        next = (handoverSlot (certificateHandover slot minimum move) i,
          minimum (move.2.2.2.2 i)) := Iff.rfl

end Characterisation
