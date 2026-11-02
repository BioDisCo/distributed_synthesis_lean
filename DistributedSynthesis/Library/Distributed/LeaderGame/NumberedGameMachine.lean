/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedBoundaryInterpretation
import DistributedSynthesis.Library.Distributed.LeaderGame.CarriedPublicGame

/-! The concrete numbered game's common-state controller. Its successor
selection retains one advertised family together with its literal numbering. -/
namespace Characterisation
open DistributedSynthesis

theorem leaderBoundary_empty {I₁ I₂ : Type} (P : List Graph → Prop) (d : Nat) :
    leaderBoundary P d ([] : EnvHistory I₁ I₂) = true := by
  have views : ∀ p, currentView p ([] : EnvHistory I₁ I₂) = View.empty p := by
    intro p
    cases p <;> rfl
  have checkpoint : leaderCheckpoint P d ([] : EnvHistory I₁ I₂) = true := by
    unfold leaderCheckpoint
    rw [views,lagView_empty]
    rfl
  rw [leaderBoundary,checkpoint,Bool.true_or]

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (P : List Graph → Prop)

abbrev NumberedGameState := CarriedLeaderState
  (List (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) ×
    NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
  objective.State I₁ I₂

variable (tree : LabeledTree
  (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
  (NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))

noncomputable def numberedGameDecode (_origin : LeaderPhaseOrigin I₁ I₂)
    (state : NumberedGameState (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) :
    StrategyPair I₁ I₂ O₁ O₂ :=
  chooseNumberedController M objective rank state.data.2.1.1 state.data.2.2
    (tree state.data.1).2 (tree state.data.1).1

noncomputable def numberedGameSelect
    (state : NumberedGameState (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (old target : LeaderPhaseOrigin I₁ I₂)
    (_labels : EnvHistory I₁ I₂ → objective.State) (_minima : EnvHistory I₁ I₂ → Nat) :=
  match chooseNumberedSuccessor M objective rank P state.data.2.1.1 state.data.2.2
    (numberedGameDecode M objective rank tree old state) (tree state.data.1).2 target with
  | some choice => (choice.1,choice)
  | none => (state.data.2.1,state.data.2)

noncomputable abbrev numberedGameAdvance := carriedLeaderAdvance
  (fun s input output => objective.step s (input,output)) (fun q => (rank q).val)
  (numberedGameDecode M objective rank tree) (carriedPublicUpdate (numberedGameSelect M objective rank P tree))

def NumberedGameValid
    (initial : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (state : NumberedGameState (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (origin : LeaderPhaseOrigin I₁ I₂) : Prop :=
  publicSupport (numberedLeaderOffers objective) tree state.data.1 = true ∧
  state.data.2.1 = observableAt initial state.data.1 ∧
  NumberedBoundaryRep M objective P state.label state.data.2.1.1 state.data.2.2 origin

noncomputable def numberedGameSlot
    (state : NumberedGameState (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (h : EnvHistory I₁ I₂) : Fin (B+1) :=
  numberedHistorySlot objective state.data.2.1.1 state.data.2.2 h

variable (initial : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

noncomputable abbrev numberedGameMachine := carriedLeaderMachine P d
  (fun s input output => objective.step s (input,output)) (fun q => (rank q).val) objective.initial
  ([],initial) (numberedGameDecode M objective rank tree)
  (carriedPublicUpdate (numberedGameSelect M objective rank P tree))

variable (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)
variable (validTree : SupportedMovesValid (numberedLeaderOffers objective) initial.1
  (fun family move => numberedLeaderLegal M objective rank family.1 move = true) tree)

include closed recognizes recent bounded small validTree in
theorem numberedGameAdvance_valid
    (state : NumberedGameState (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (valid : NumberedGameValid M objective P tree initial.1 state (boundaryOrigin P (h.take a))) :
    let old := boundaryOrigin P (h.take a)
    let target := boundaryOrigin P h
    let next := numberedGameAdvance M objective rank P tree state old target
    ∃ choice : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      choice.1 ∈ (tree state.data.1).2 ∧
      NumberedSuccessorRep M objective rank P state.data.2.1.1 state.data.2.2
        (numberedGameDecode M objective rank tree old state) target choice.1 choice.2 ∧
      next.data = (state.data.1 ++ [choice.1],choice) ∧
      NumberedGameValid M objective P tree initial.1 next target := by
  let old := boundaryOrigin P (h.take a)
  let target := boundaryOrigin P h
  let next := numberedGameAdvance M objective rank P tree state old target
  have legal := validTree state.data.1 valid.1
  rw [← valid.2.1] at legal
  obtain ⟨choice,selected,member,rep⟩ := numberedLegal_actual_choice M objective P state.label
    state.data.2.1.1 state.data.2.2 rank (tree state.data.1)
    closed recognizes recent bounded small h live a phase valid.2.2 legal
  have data : next.data = (state.data.1 ++ [choice.1],choice) := by
    change (carriedLeaderAdvance _ _ _ _ state old target).data = _
    simp only [carriedLeaderAdvance,carriedPublicUpdate,numberedGameSelect,numberedGameDecode,target,selected]
  have representation := numberedSuccessor_preserves_representation M objective rank P
    (numberedGameDecode M objective rank tree) (carriedPublicUpdate (numberedGameSelect M objective rank P tree))
    state old target state.data.2.1.1 state.data.2.2 valid.2.2 choice.1 choice.2 rep
  refine ⟨choice,member,rep,data,?_,?_,?_⟩
  · rw [data,publicSupport_append,valid.1]
    simpa only [Bool.true_and,numberedLeaderOffers,decide_eq_true_eq] using member
  · rw [data]
    simp only [observableAt,List.getLast?_concat,Option.getD_some]
  · rw [data]
    exact representation.1

include closed recognizes recent bounded small validTree in
theorem numberedGameMachine_valid
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)))
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (boundary : leaderBoundary P d h = true) :
    NumberedGameValid M objective P tree initial.1
      (numberedGameMachine M objective rank P tree initial h) (boundaryOrigin P h) := by
  have claim : ∀ n (h : EnvHistory I₁ I₂), List.length h = n → P (History.graphSequence h) →
      leaderBoundary P d h = true →
      NumberedGameValid M objective P tree initial.1
        (numberedGameMachine M objective rank P tree initial h) (boundaryOrigin P h) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h length live boundary
      by_cases empty : h = []
      · subst h
        change NumberedGameValid M objective P tree initial.1
          (boundaryMachine P d (initialCarriedLeaderState (fun q => (rank q).val) objective.initial ([],initial))
            (numberedGameAdvance M objective rank P tree) []) _
        rw [boundaryMachine_empty]
        exact ⟨publicSupport_nil _ _,rfl,initialRep⟩
      · have positive := List.length_pos_iff.mpr empty
        let a := previousLeaderBoundary P d h
        have interval := previousLeaderBoundary_interval P d h positive
        have less : a < List.length h := interval.start_lt
        have start : leaderBoundary P d (h.take a) = true := by
          rcases interval.start with zero | boundary
          · simpa only [a,zero,List.take_zero] using leaderBoundary_empty (I₁:=I₁) (I₂:=I₂) P d
          · exact boundary
        have phase : ConsecutiveLeaderBoundaries P d h a :=
          ⟨interval.start_lt,start,boundary,interval.no_boundary⟩
        have rootLength : List.length (h.take a) = a := by
          simp only [List.length_take,min_eq_left (Nat.le_of_lt less)]
        have oldValid := ih a (by omega) (h.take a) rootLength (live_history_take P closed h live a) start
        obtain ⟨_,_,_,_,nextValid⟩ := numberedGameAdvance_valid M objective rank P tree initial
          closed recognizes recent bounded small validTree
          (numberedGameMachine M objective rank P tree initial (h.take a)) h live a phase oldValid
        change NumberedGameValid M objective P tree initial.1
          (boundaryMachine P d (initialCarriedLeaderState (fun q => (rank q).val) objective.initial ([],initial))
            (numberedGameAdvance M objective rank P tree) h) _
        rw [boundaryMachine_nonempty P d _ _ h empty]
        exact nextValid
  exact claim _ h rfl live boundary

include closed recognizes recent bounded small validTree in
theorem numberedGameMachine_actual_edge
    (initialRep : NumberedBoundaryRep M objective P (fun _ => objective.initial) initial.1.1 initial.2
      (boundaryOrigin P ([] : EnvHistory I₁ I₂)))
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (interval : LeaderPhaseInterval P d h a) (boundary : leaderBoundary P d h = true) :
    let machine := numberedGameMachine M objective rank P tree initial
    OfferedHandoverEdge (numberedLeaderOffers objective)
      (carriedHandoverCode (numberedGameSlot objective) (machine (h.take a)) (h.take a))
      (tree (machine (h.take a)).data.1)
      (carriedPublicObservation (fun s input output => objective.step s (input,output))
        (fun q => (rank q).val) (numberedGameDecode M objective rank tree)
        (numberedGameSelect M objective rank P tree) initial.1
        (machine (h.take a)) (boundaryOrigin P (h.take a)) (boundaryOrigin P h))
      (carriedHandoverCode (numberedGameSlot objective) (machine h) h) := by
  let machine := numberedGameMachine M objective rank P tree initial
  let state := machine (h.take a)
  let old := boundaryOrigin P (h.take a)
  let target := boundaryOrigin P h
  let next := numberedGameAdvance M objective rank P tree state old target
  have start : leaderBoundary P d (h.take a) = true := by
    rcases interval.start with zero | boundary
    · simpa only [zero,List.take_zero] using leaderBoundary_empty (I₁:=I₁) (I₂:=I₂) P d
    · exact boundary
  have phase : ConsecutiveLeaderBoundaries P d h a :=
    ⟨interval.start_lt,start,boundary,interval.no_boundary⟩
  have valid := numberedGameMachine_valid M objective rank P tree initial closed recognizes recent bounded small
    validTree initialRep (h.take a) (live_history_take P closed h live a) start
  obtain ⟨choice,member,rep,data,_⟩ := numberedGameAdvance_valid M objective rank P tree initial closed recognizes
    recent bounded small validTree state h live a phase valid
  have current : machine h = next := by
    have empty : h ≠ [] := List.ne_nil_of_length_pos (by have := interval.start_lt; omega)
    change boundaryMachine P d (initialCarriedLeaderState (fun q => (rank q).val) objective.initial ([],initial))
      (numberedGameAdvance M objective rank P tree) h = _
    rw [boundaryMachine_nonempty P d _ _ h empty,previousLeaderBoundary_eq P d h a interval]
  have observation : carriedPublicObservation (fun s input output => objective.step s (input,output))
      (fun q => (rank q).val) (numberedGameDecode M objective rank tree)
      (numberedGameSelect M objective rank P tree) initial.1 state old target = choice.1 := by
    change (next.data.1.getLast?).getD initial.1 = _
    rw [data]
    simp only [List.getLast?_concat,Option.getD_some]
  change OfferedHandoverEdge _ _ _ _ (carriedHandoverCode (numberedGameSlot objective) (machine h) h)
  rw [current,observation]
  refine ⟨?_,?_⟩
  · change decide (choice.1 ∈ (tree state.data.1).2) = true
    exact decide_eq_true member
  · have edge := numberedSuccessor_actual_edge M objective rank P
      (numberedGameDecode M objective rank tree) (carriedPublicUpdate (numberedGameSelect M objective rank P tree))
      state old target state.data.2.1.1 state.data.2.2 valid.2.2 choice.1 choice.2 rep h
      (show InputConnected P h h from Relation.ReflTransGen.refl)
      (carriedHandoverCode (numberedGameSlot objective) state (h.take a)).2
    have depth : old.1 = a := by
      simp only [old,boundaryOrigin,List.length_take,min_eq_left (Nat.le_of_lt interval.start_lt)]
    rw [depth] at edge
    change HandoverEdge _ _ () (numberedHistorySlot objective next.data.2.1.1 next.data.2.2 h,
      ⟨next.minimum h % (C+1),Nat.mod_lt _ (by omega)⟩)
    rw [data]
    exact edge

end
end Characterisation
