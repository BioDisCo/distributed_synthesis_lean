/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphBoundaryUpdates

/-! After one-round expansion, retain exactly the computed live component
and renumber it within the original uniform bound. The existing enumeration
checker is reused; observation matrices and annotations are computed. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

abbrev GraphComponentReindex (S : Type) (K : Nat) := Σ n : Fin (K+1), Fin n.val → GraphChild S

instance graphComponentReindex_fintype {S : Type} [Fintype S] (K : Nat) :
    Fintype (GraphComponentReindex S K) := by
  unfold GraphComponentReindex GraphChild
  infer_instance

def checkGraphReindex {S Q : Type} [Fintype S] [DecidableEq S] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (shape : InputShape S) (label : S → GraphReceptionLabel Q d) (root : GraphChild S)
    (keep : GraphComponentReindex S K) : Bool :=
  checkClosingEnumeration (closingComponentMask (graphChildShape shape) (graphChildLive M label) root) keep.2

def graphReindexTarget {S Q : Type} {d K : Nat} (M : Recognizer Graph Q)
    (shape : InputShape S) (label : S → GraphReceptionLabel Q d) (keep : GraphComponentReindex S K) :
    SwitchInterface (GraphReceptionLabel Q d) K :=
  ⟨keep.1,restrictInputShape (graphChildShape shape) keep.2,graphChildLabels M.step label ∘ keep.2⟩

def RepresentsGraphComponentUsing {Q : Type} {d K : Nat} (P : List Graph → Prop)
    (M : Recognizer Graph Q) (g : List Graph) (summary : SwitchInterface (GraphReceptionLabel Q d) K)
    (past : Fin summary.1.val → List Graph) : Prop :=
  Function.Injective past ∧
    (∀ k, Connected P g k ↔ ∃ s, past s = k) ∧
    RepresentsInputShape (graphHistory ∘ past) summary.2.1 ∧
    ∀ s, summary.2.2 s = graphReceptionLabel M d (past s)

def RepresentsGraphComponent {Q : Type} {d K : Nat} (P : List Graph → Prop)
    (M : Recognizer Graph Q) (g : List Graph) (summary : SwitchInterface (GraphReceptionLabel Q d) K) : Prop :=
  ∃ past, RepresentsGraphComponentUsing P M g summary past

theorem graphChildHistory_injective {S : Type} (past : S → List Graph) (injective : Function.Injective past) :
    Function.Injective (graphChildHistory past) := by
  rintro ⟨s,g⟩ ⟨t,r⟩ eq
  have old := congrArg List.dropLast eq
  simp only [graphChildHistory,List.dropLast_concat] at old
  obtain rfl := injective old
  have last : g = r := by simpa only [graphChildHistory,List.append_cancel_left_eq,List.singleton_inj] using eq
  subst r
  rfl

section Transition
variable {S Q : Type} [Fintype S] [DecidableEq S]
variable (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (past : S → List Graph) (injective : Function.Injective past)
variable (shape : InputShape S) (rep : RepresentsInputShape (graphHistory ∘ past) shape)
variable (covers : ∀ s k, Connected P (past s) k → ∃ t, past t = k)
variable (label : S → GraphReceptionLabel Q d)
variable (exactLabels : ∀ s, label s = graphReceptionLabel M d (past s))
variable (root : GraphChild S) (live : P (graphChildHistory past root))

include closed rep covers exactLabels live recognizes in
theorem graphStepMask_exact (s : GraphChild S) :
    closingComponentMask (graphChildShape shape) (graphChildLive M label) root s = true ↔
      Connected P (graphChildHistory past root) (graphChildHistory past s) :=
  graphComponentMask_exact P (graphChildHistory past) (graphChildShape shape)
    (graphChildShape_exact past shape rep) (graphChildLive M label)
    (graphChildLive_exact M d P recognizes past label exactLabels) root live
    (graphChild_component_coverage P closed past covers root) s

include closed injective rep covers exactLabels live recognizes in
/-- Every passing renumbering preserves a complete graph component with
exact observations and exact finite reception/recognizer annotations. -/
theorem graphReindexTarget_using {K : Nat} (keep : GraphComponentReindex S K)
    (valid : checkGraphReindex M shape label root keep = true) :
    RepresentsGraphComponentUsing P M (graphChildHistory past root) (graphReindexTarget M shape label keep)
      (graphChildHistory past ∘ keep.2) := by
  have selected : Function.Injective keep.2 ∧ ∀ t,
      closingComponentMask (graphChildShape shape) (graphChildLive M label) root t = true ↔ ∃ s, keep.2 s = t := by
    simpa only [checkGraphReindex,checkClosingEnumeration,decide_eq_true_eq] using valid
  have mask := graphStepMask_exact M P closed recognizes d past shape rep covers label exactLabels root live
  refine ⟨(graphChildHistory_injective past injective).comp selected.1,?_,?_,?_⟩
  · intro k
    constructor
    · intro conn
      obtain ⟨t,eq⟩ := graphChild_component_coverage P closed past covers root k conn
      obtain ⟨s,hs⟩ := (selected.2 t).mp ((mask t).mpr (by rwa [eq]))
      exact ⟨s,by simpa only [Function.comp_apply,hs] using eq⟩
    · rintro ⟨s,rfl⟩
      exact (mask _).mp ((selected.2 _).mpr ⟨s,rfl⟩)
  · exact restrictInputShape_exact _ _ (graphChildShape_exact past shape rep) keep.2
  · intro s
    exact graphChildLabels_exact M d past label exactLabels (keep.2 s)

include closed injective rep covers exactLabels live recognizes in
theorem graphReindexTarget_correct {K : Nat} (keep : GraphComponentReindex S K)
    (valid : checkGraphReindex M shape label root keep = true) :
    RepresentsGraphComponent P M (graphChildHistory past root) (graphReindexTarget M shape label keep) :=
  ⟨_,graphReindexTarget_using M P closed recognizes d past injective shape rep covers label exactLabels root live keep valid⟩

include closed injective rep covers exactLabels live recognizes in
/-- The old uniform graph-component bound suffices for an accepted target
renumbering at every live step. No new bound grows with the phase length. -/
theorem exists_checked_graph_reindex (K : Nat)
    [Finite (HistoryComponent P (graphChildHistory past root))]
    (small : Nat.card (HistoryComponent P (graphChildHistory past root)) ≤ K) :
    ∃ keep : GraphComponentReindex S K, checkGraphReindex M shape label root keep = true := by
  classical
  let mask := closingComponentMask (graphChildShape shape) (graphChildLive M label) root
  let T := {s : GraphChild S // mask s = true}
  have exactMask := graphStepMask_exact M P closed recognizes d past shape rep covers label exactLabels root live
  let f : T → HistoryComponent P (graphChildHistory past root) :=
    fun s => ⟨graphChildHistory past s.val,(exactMask s.val).mp s.property⟩
  have inj : Function.Injective f := by
    intro s t eq
    apply Subtype.ext
    exact graphChildHistory_injective past injective (congrArg Subtype.val eq)
  have card : Nat.card T ≤ K := (Nat.card_le_card_of_injective f inj).trans small
  obtain ⟨summary,e,_,_⟩ := finite_switch_interface K card
    (fun s : T => graphHistory (graphChildHistory past s.val))
    (fun s : T => graphChildLabels M.step label s.val)
  let keep : GraphComponentReindex S K := ⟨summary.1,fun i => (e i).val⟩
  refine ⟨keep,?_⟩
  simp only [checkGraphReindex,checkClosingEnumeration,decide_eq_true_eq]
  change Function.Injective keep.2 ∧ ∀ t, mask t = true ↔ ∃ s, keep.2 s = t
  refine ⟨Subtype.val_injective.comp e.injective,fun t => ⟨?_,?_⟩⟩
  · intro yes
    obtain ⟨i,eq⟩ := e.surjective (⟨t,yes⟩ : T)
    exact ⟨i,congrArg Subtype.val eq⟩
  · rintro ⟨i,rfl⟩
    exact (e i).property


include closed injective rep covers exactLabels live recognizes in
/-- An accepted renumbering also retains the actual child slot. Remembering
its new index lets the monitor follow the physical graph history exactly. -/
theorem exists_checked_pointed_graph_reindex (K : Nat)
    [Finite (HistoryComponent P (graphChildHistory past root))]
    (small : Nat.card (HistoryComponent P (graphChildHistory past root)) ≤ K) :
    ∃ keep : GraphComponentReindex S K, ∃ point : Fin keep.1.val,
      checkGraphReindex M shape label root keep = true ∧ keep.2 point = root := by
  obtain ⟨keep,valid⟩ := exists_checked_graph_reindex M P closed recognizes d past injective
    shape rep covers label exactLabels root live K small
  have selected : Function.Injective keep.2 ∧ ∀ t,
      closingComponentMask (graphChildShape shape) (graphChildLive M label) root t = true ↔ ∃ s, keep.2 s = t := by
    simpa only [checkGraphReindex,checkClosingEnumeration,decide_eq_true_eq] using valid
  have rootIn := (graphStepMask_exact M P closed recognizes d past shape rep covers label exactLabels root live root).mpr
    Relation.ReflTransGen.refl
  obtain ⟨point,eq⟩ := (selected.2 root).mp rootIn
  exact ⟨keep,point,valid,eq⟩

end Transition
end Characterisation
