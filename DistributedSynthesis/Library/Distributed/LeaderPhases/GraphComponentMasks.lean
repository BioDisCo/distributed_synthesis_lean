/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CarriedScheduledBundles

/-! Reuse the existing observation update and finite component mask on
singleton-input histories. These masks represent complete graph components,
independently of the actual private-input histories carried by a leader. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

def graphHistory (g : List Graph) : EnvHistory Unit Unit :=
  g.map (fun r => ⟨(),(),r,(),()⟩)

theorem graphHistory_graphSequence (g : List Graph) : History.graphSequence (graphHistory g) = g := by
  simp [graphHistory,History.graphSequence,List.map_map,Function.comp_def]

theorem graphHistory_of_unit (h : EnvHistory Unit Unit) : graphHistory (History.graphSequence h) = h := by
  induction h with
  | nil => rfl
  | cons r h ih =>
    rcases r with ⟨⟨⟩,⟨⟩,g,⟨⟩,⟨⟩⟩
    simpa only [History.graphSequence,graphHistory,List.map_cons] using congrArg (List.cons _) ih

theorem graphHistory_view (g : List Graph) (p : Proc) : currentView p (graphHistory g) = graphView p g := by
  cases p
  · exact (congrArg Prod.fst (at_views g)).symm
  · exact (congrArg Prod.snd (at_views g)).symm

theorem graphHistory_append (g : List Graph) (r : Graph) :
    graphHistory (g++[r]) = graphHistory g ++ [⟨(),(),r,(),()⟩] := by
  simp only [graphHistory,List.map_append,List.map_cons,List.map_nil]

theorem graphConnected_iff_unit (P : List Graph → Prop) (g h : List Graph) :
    Connected P g h ↔ InputConnected P (graphHistory g) (graphHistory h) := by
  constructor
  · intro conn
    apply Relation.ReflTransGen.lift graphHistory ?_ conn
    intro a b edge
    refine ⟨by simpa only [graphHistory_graphSequence] using edge.1,
      by simpa only [graphHistory_graphSequence] using edge.2.1,?_⟩
    rcases edge.2.2 with one | two
    · exact Or.inl (by simpa only [graphHistory_view,graphView] using one)
    · exact Or.inr (by simpa only [graphHistory_view,graphView] using two)
  · intro conn
    simpa only [graphHistory_graphSequence] using inputConnected_projects P conn

/-- Exact graph-component reachability is the existing input-component
checker at singleton inputs. Its coverage hypothesis concerns graph histories. -/
theorem graphComponentMask_exact {S : Type} [Fintype S] [DecidableEq S]
    (P : List Graph → Prop) (past : S → List Graph)
    (shape : InputShape S) (rep : RepresentsInputShape (graphHistory ∘ past) shape)
    (live : S → Bool) (liveExact : ∀ s, live s = true ↔ P (past s))
    (root : S) (rootLive : P (past root))
    (covers : ∀ k, Connected P (past root) k → ∃ s, past s = k) (s : S) :
    closingComponentMask shape live root s = true ↔ Connected P (past root) (past s) := by
  rw [graphConnected_iff_unit]
  apply closingComponentMask_exact P (graphHistory ∘ past) shape rep live
    (fun s => by simpa only [Function.comp_apply,graphHistory_graphSequence] using liveExact s) root
    (by simpa only [Function.comp_apply,graphHistory_graphSequence] using rootLive)
  intro k conn
  have graphs := inputConnected_projects P conn
  simp only [Function.comp_apply,graphHistory_graphSequence] at graphs
  obtain ⟨t,eq⟩ := covers (History.graphSequence k) graphs
  exact ⟨t,by simp only [Function.comp_apply,eq,graphHistory_of_unit]⟩

abbrev GraphChild (S : Type) := S × Graph

def graphChildHistory {S : Type} (past : S → List Graph) (s : GraphChild S) : List Graph :=
  past s.1 ++ [s.2]

def graphChildShape {S : Type} (shape : InputShape S) : InputShape (GraphChild S) :=
  restrictInputShape (advanceInputShape (I₁:=Unit) (I₂:=Unit) shape) (fun s => (s.1,(),(),s.2))

theorem graphChildShape_exact {S : Type} (past : S → List Graph) (shape : InputShape S)
    (rep : RepresentsInputShape (graphHistory ∘ past) shape) :
    RepresentsInputShape (graphHistory ∘ graphChildHistory past) (graphChildShape shape) := by
  have exactShape := restrictInputShape_exact _ _
    (advanceInputShape_exact (graphHistory ∘ past) shape rep) (fun s : GraphChild S => (s.1,(),(),s.2))
  simpa only [graphChildShape,Function.comp_def,graphChildHistory,graphHistory_append,scenarioHistory] using exactShape

/-- Prefix closure guarantees coverage after expansion of the full source
component. No missing graph histories may be inferred from private inputs. -/
theorem graphChild_component_coverage {S : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (past : S → List Graph)
    (covers : ∀ s k, Connected P (past s) k → ∃ t, past t = k)
    (s : GraphChild S) (k : List Graph) (conn : Connected P (graphChildHistory past s) k) :
    ∃ t, graphChildHistory past t = k := by
  have parent := connected_parent P closed conn
  simp only [graphChildHistory,List.dropLast_concat] at parent
  obtain ⟨t,eq⟩ := covers s.1 k.dropLast parent
  have len := connected_same_depth P conn
  have ne : k ≠ [] := by
    intro empty
    simp [graphChildHistory,empty] at len
  obtain ⟨old,g,hk⟩ := (List.eq_nil_or_concat' k).resolve_left ne
  refine ⟨(t,g),?_⟩
  simp only [hk,List.dropLast_concat] at eq
  simp only [graphChildHistory,eq,hk]

end Characterisation
