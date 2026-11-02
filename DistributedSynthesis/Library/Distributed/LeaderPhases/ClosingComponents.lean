/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingMoveGuard
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Complete component selection among bounded closing descendants. We use
Mathlib's finite graph reachability procedure rather than implementing a new
reachability algorithm. -/
namespace Characterisation
open DistributedSynthesis

/-- If the root family contains every member of each root's component, then
all descendants of any closing scenario's component occur in its layer. -/
theorem closingLayer_component_coverage {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (past : H → EnvHistory I₁ I₂)
    (covers : ∀ s k, InputConnected P (past s) k → ∃ t, past t = k)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) (k : EnvHistory I₁ I₂)
    (conn : InputConnected P (closingLayerHistory past n s) k) :
    ∃ t : ClosingLayer H I₁ I₂ n, closingLayerHistory past n t = k := by
  induction n generalizing k with
  | zero => exact covers s k conn
  | succ n ih =>
    have parent := inputConnected_parent P closed conn
    have par : InputConnected P (closingLayerHistory past n s.1) k.dropLast := by
      simpa [closingLayerHistory,scenarioHistory,List.dropLast_concat] using parent
    obtain ⟨t,ht⟩ := ih s.1 k.dropLast par
    have lengths := connected_same_depth P (inputConnected_projects P conn)
    have nonempty : k ≠ [] := by
      intro empty
      simp [empty,closingLayerHistory,scenarioHistory,History.graphSequence] at lengths
    obtain ⟨old,r,eq⟩ := (List.eq_nil_or_concat' k).resolve_left nonempty
    have oldEq : old = closingLayerHistory past n t := by
      simpa [eq,List.dropLast_concat] using ht.symm
    refine ⟨(t,r.inputOne,r.inputTwo,r.graph),?_⟩
    rcases r with ⟨x,y,g,⟨⟩,⟨⟩⟩
    simpa [closingLayerHistory,scenarioHistory,← oldEq] using eq.symm

/-- The full boundary component satisfies the coverage hypothesis. A single
leader-view subfamily need not satisfy it and must not be substituted here. -/
theorem input_component_covers {I₁ I₂ : Type}
    (P : List Graph → Prop) (h : EnvHistory I₁ I₂)
    (s : InputHistoryComponent P h) (k : EnvHistory I₁ I₂)
    (conn : InputConnected P s.val k) :
    ∃ t : InputHistoryComponent P h, t.val = k :=
  ⟨⟨k,s.property.trans conn⟩,rfl⟩

theorem closingLayerHistory_injective {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past) (n : Nat) :
    Function.Injective (closingLayerHistory past n) := by
  induction n with
  | zero => exact injective
  | succ n ih =>
    intro s t eq
    rcases s with ⟨s,x,y,g⟩
    rcases t with ⟨t,u,v,j⟩
    have parents := congrArg List.dropLast eq
    simp only [closingLayerHistory,scenarioHistory,List.dropLast_concat] at parents
    obtain rfl := ih parents
    have records : (⟨x,y,g,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit) = ⟨u,v,j,(),()⟩ := by
      simpa only [closingLayerHistory,scenarioHistory,List.append_cancel_left_eq,List.singleton_inj] using eq
    cases records
    rfl

def closingObservationGraph {S : Type} (shape : InputShape S) (live : S → Bool) : SimpleGraph S where
  Adj s t := s ≠ t ∧ live s = true ∧ live t = true ∧
    ∃ p : Proc, shape p s t = true ∨ shape p t s = true
  symm := by
    intro s t edge
    exact ⟨Ne.symm edge.1,edge.2.2.1,edge.2.1,
      edge.2.2.2.imp (fun _ eq => eq.symm)⟩
  loopless := ⟨fun _ edge => edge.1 rfl⟩

instance closingObservationGraph_decidable {S : Type} [DecidableEq S]
    (shape : InputShape S) (live : S → Bool) : DecidableRel (closingObservationGraph shape live).Adj := by
  intro s t
  unfold closingObservationGraph
  infer_instance

/-- The executable component mask includes exactly the live reachable slots. -/
def closingComponentMask {S : Type} [Fintype S] [DecidableEq S]
    (shape : InputShape S) (live : S → Bool) (root : S) (s : S) : Bool :=
  live s && decide ((closingObservationGraph shape live).Reachable root s)

theorem closing_graph_reachable_of_adjacent {S I₁ I₂ : Type}
    (P : List Graph → Prop) (past : S → EnvHistory I₁ I₂)
    (shape : InputShape S) (rep : RepresentsInputShape past shape)
    (live : S → Bool) (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (past s)))
    (s t : S) (ls : P (History.graphSequence (past s))) (lt : P (History.graphSequence (past t)))
    (adj : InputAdjacent (past s) (past t)) :
    (closingObservationGraph shape live).Reachable s t := by
  by_cases eq : s = t
  · subst t
    exact SimpleGraph.Reachable.refl s
  · apply SimpleGraph.Adj.reachable
    refine ⟨eq,(liveExact s).mpr ls,(liveExact t).mpr lt,?_⟩
    rcases adj with one | two
    · exact ⟨.one,Or.inl ((rep .one s t).mpr one)⟩
    · exact ⟨.two,Or.inl ((rep .two s t).mpr two)⟩

theorem closing_graph_adjacent_sound {S I₁ I₂ : Type}
    (P : List Graph → Prop) (past : S → EnvHistory I₁ I₂)
    (shape : InputShape S) (rep : RepresentsInputShape past shape)
    (live : S → Bool) (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (past s)))
    {s t : S} (edge : (closingObservationGraph shape live).Adj s t) :
    P (History.graphSequence (past s)) ∧ P (History.graphSequence (past t)) ∧
      InputAdjacent (past s) (past t) := by
  refine ⟨(liveExact s).mp edge.2.1,(liveExact t).mp edge.2.2.1,?_⟩
  obtain ⟨p,eq | eq⟩ := edge.2.2.2
  · cases p
    · exact Or.inl ((rep .one s t).mp eq)
    · exact Or.inr ((rep .two s t).mp eq)
  · cases p
    · exact Or.inl ((rep .one t s).mp eq).symm
    · exact Or.inr ((rep .two t s).mp eq).symm

/-- Exactness requires coverage of the entire actual component, not merely
an arbitrary finite set of representatives. -/
theorem closingComponentMask_exact {S I₁ I₂ : Type} [Fintype S] [DecidableEq S]
    (P : List Graph → Prop) (past : S → EnvHistory I₁ I₂)
    (shape : InputShape S) (rep : RepresentsInputShape past shape)
    (live : S → Bool) (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (past s)))
    (root : S) (rootLive : P (History.graphSequence (past root)))
    (covers : ∀ k, InputConnected P (past root) k → ∃ s, past s = k)
    (s : S) : closingComponentMask shape live root s = true ↔
      InputConnected P (past root) (past s) := by
  constructor
  · intro mask
    have decoded : live s = true ∧ (closingObservationGraph shape live).Reachable root s := by
      simpa only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq] using mask
    have reach := decoded.2
    have path := ((closingObservationGraph shape live).reachable_iff_reflTransGen root s).mp reach
    exact Relation.ReflTransGen.lift past (fun _ _ edge => closing_graph_adjacent_sound P past shape rep live liveExact edge) path
  · intro conn
    have lift : ∀ k, InputConnected P (past root) k → ∀ t, past t = k →
        P (History.graphSequence k) ∧ (closingObservationGraph shape live).Reachable root t := by
      intro k connected
      induction connected with
      | refl =>
        intro t eq
        refine ⟨rootLive,closing_graph_reachable_of_adjacent P past shape rep live liveExact root t rootLive ?_ ?_⟩
        · simpa [eq] using rootLive
        · exact Or.inl (congrArg (currentView .one) eq.symm)
      | @tail b c connected edge ih =>
        intro t eq
        obtain ⟨u,hu⟩ := covers b connected
        obtain ⟨_,reach⟩ := ih u hu
        refine ⟨edge.2.1,reach.trans (closing_graph_reachable_of_adjacent P past shape rep live liveExact u t ?_ ?_ ?_)⟩
        · simpa [hu] using edge.1
        · simpa [eq] using edge.2.1
        · simpa [hu,eq] using edge.2.2
    obtain ⟨ls,reach⟩ := lift _ conn s rfl
    simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨(liveExact s).mpr ls,reach⟩

/-- The computed live mask selects exactly the full actual descendant
component when the source family covers its components. -/
theorem closingLayerComponentMask_exact {H I₁ I₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (covers : ∀ s k, InputConnected P (past s) k → ∃ t, past t = k)
    (n : Nat) (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root)))
    (s : ClosingLayer H I₁ I₂ n) :
    closingComponentMask (closingLayerShape shape n) live root s = true ↔
      InputConnected P (closingLayerHistory past n root) (closingLayerHistory past n s) :=
  closingComponentMask_exact P _ _ (closingLayerShape_exact past shape rep n) live liveExact root rootLive
    (fun k conn => closingLayer_component_coverage P closed past covers n root k conn) s

/-- Including every compatible history is part of the result, not a premise
about a guessed list of next-boundary histories. -/
theorem closingLayerComponent_complete {H I₁ I₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (covers : ∀ s k, InputConnected P (past s) k → ∃ t, past t = k)
    (n : Nat) (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root)))
    (k : EnvHistory I₁ I₂) :
    InputConnected P (closingLayerHistory past n root) k ↔
      ∃ s, closingComponentMask (closingLayerShape shape n) live root s = true ∧
        closingLayerHistory past n s = k := by
  constructor
  · intro conn
    obtain ⟨s,eq⟩ := closingLayer_component_coverage P closed past covers n root k conn
    exact ⟨s,(closingLayerComponentMask_exact P closed past shape rep covers n live liveExact root rootLive s).mpr
      (by simpa only [eq] using conn),eq⟩
  · rintro ⟨s,mask,rfl⟩
    exact (closingLayerComponentMask_exact P closed past shape rep covers n live liveExact root rootLive s).mp mask

/-- No duplicates are introduced when the source histories have unique
slots. Hence cardinality bounds on actual components transfer to the
computed component's slots. -/
theorem closingComponentMask_equiv {S I₁ I₂ : Type} [Fintype S] [DecidableEq S]
    (P : List Graph → Prop) (past : S → EnvHistory I₁ I₂)
    (injective : Function.Injective past)
    (shape : InputShape S) (rep : RepresentsInputShape past shape)
    (live : S → Bool) (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (past s)))
    (root : S) (rootLive : P (History.graphSequence (past root)))
    (covers : ∀ k, InputConnected P (past root) k → ∃ s, past s = k) :
    Nonempty ({s // closingComponentMask shape live root s = true} ≃ InputHistoryComponent P (past root)) := by
  classical
  let f : {s // closingComponentMask shape live root s = true} → InputHistoryComponent P (past root) :=
    fun s => ⟨past s.val,(closingComponentMask_exact P past shape rep live liveExact root rootLive covers s.val).mp s.property⟩
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩⟩
  · intro s t eq
    exact Subtype.ext (injective (congrArg Subtype.val eq))
  · intro k
    obtain ⟨s,eq⟩ := covers k.val k.property
    have mask : closingComponentMask shape live root s = true :=
      (closingComponentMask_exact P past shape rep live liveExact root rootLive covers s).mpr
        (by simpa only [eq] using k.property)
    exact ⟨⟨s,mask⟩,Subtype.ext eq⟩

abbrev ClosingComponentSlots {H I₁ I₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H) (n : Nat) (live : ClosingLayer H I₁ I₂ n → Bool)
    (root : ClosingLayer H I₁ I₂ n) :=
  {s // closingComponentMask (closingLayerShape shape n) live root s = true}

/-- Compute the entire chosen component and its monitor labels. There is no
caller-supplied list of retained slots in this construction. -/
def computedClosingComponent {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n) :
    InputShape (ClosingComponentSlots shape n live root) ×
      (ClosingComponentSlots shape n live root → Q) :=
  computedClosingTarget shape step initial out bound Subtype.val

theorem computedClosingComponent_correct {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (covers : ∀ s k, InputConnected P (past s) k → ∃ t, past t = k)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root))) :
    (RepresentsInputShape (fun s : ClosingComponentSlots shape n live root => closingLayerHistory past n s.val)
      (computedClosingComponent shape step initial out bound live root).1 ∧
      ∀ s : ClosingComponentSlots shape n live root,
        (computedClosingComponent shape step initial out bound live root).2 s =
          (closingLayerTrace out n bound s.val).foldl (fun q letter => step q letter.1 letter.2)
            (initial (closingLayerRoot n s.val))) ∧
    (∀ k, InputConnected P (closingLayerHistory past n root) k ↔
      ∃ s : ClosingComponentSlots shape n live root, closingLayerHistory past n s.val = k) := by
  refine ⟨computedClosingTarget_exact past shape rep step initial out bound Subtype.val,?_⟩
  intro k
  rw [closingLayerComponent_complete P closed past shape rep covers n live liveExact root rootLive k]
  constructor
  · rintro ⟨s,mask,eq⟩
    exact ⟨⟨s,mask⟩,eq⟩
  · rintro ⟨s,eq⟩
    exact ⟨s.val,s.property,eq⟩

end Characterisation
