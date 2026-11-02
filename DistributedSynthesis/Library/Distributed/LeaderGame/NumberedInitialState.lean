/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedGameRealization

/-! The initial public family has one slot, containing the empty physical
history. Its graph representation exists from the graph component bound. -/
namespace Characterisation
open DistributedSynthesis

noncomputable def numberedInitialChoice {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (positive : 0 < B) (graph : GraphRootState GQ d K) :
    NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective :=
  ⟨⟨⟨⟨1, by omega⟩, (fun _ _ _ => true),
      (fun _ => ((graph,objective.initial),fun _ => Fin.last C))⟩,
      (fun _ => 0), (fun _ => Fin.last C)⟩, fun _ => []⟩

theorem numberedInitialChoice_rep {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
    (M : Recognizer Graph GQ)
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (P : List Graph → Prop) (positive : 0 < B)
    (graph : GraphRootState GQ d K) (represented : GraphRootRep P M [] graph) :
    let initial := numberedInitialChoice (I₁:=I₁) (I₂:=I₂) (C:=C) objective positive graph
    NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)) := by
  dsimp only [numberedInitialChoice]
  refine ⟨fun _ _ _ => Subsingleton.elim _ _,?_,fun _ => rfl,?_,fun _ => represented,fun _ => rfl⟩
  · intro k
    constructor
    · intro connected
      have empty : k = [] := List.eq_nil_of_length_eq_zero (inputConnected_length P connected).symm
      exact ⟨0,empty.symm⟩
    · rintro ⟨i,equal⟩
      rw [← equal]
      exact Relation.ReflTransGen.refl
  · intro p i j
    exact iff_of_true rfl rfl

theorem numberedInitialChoice_exists {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
    (M : Recognizer Graph GQ)
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (P : List Graph → Prop) (positive : 0 < B)
    (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K) :
    ∃ initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
        (boundaryOrigin P ([] : EnvHistory I₁ I₂)) := by
  obtain ⟨graph,represented⟩ := graphRootRep_exists M P d K bounded []
  exact ⟨numberedInitialChoice objective positive graph,
    numberedInitialChoice_rep M objective P positive graph represented⟩

end Characterisation
