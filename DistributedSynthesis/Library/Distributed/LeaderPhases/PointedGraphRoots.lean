/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphComponentReindexing

/-! Each private-input root carries its own bounded graph component and
actual slot. An explicit dead state represents forbidden graph prefixes.
Different input roots may occupy different graph components. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

abbrev PointedGraphInterface (Q : Type) (d K : Nat) :=
  Σ summary : SwitchInterface (GraphReceptionLabel Q d) K, Fin summary.1.val

instance pointedGraphInterface_fintype {Q : Type} [Fintype Q] (d K : Nat) :
    Fintype (PointedGraphInterface Q d K) := by
  letI : Fintype (SwitchInterface (GraphReceptionLabel Q d) K) := by
    unfold SwitchInterface InputShape
    infer_instance
  unfold PointedGraphInterface
  infer_instance

instance pointedGraphInterface_decidableEq {Q : Type} [DecidableEq Q] (d K : Nat) :
    DecidableEq (PointedGraphInterface Q d K) := by
  unfold PointedGraphInterface SwitchInterface InputShape
  infer_instance

abbrev GraphRootState (Q : Type) (d K : Nat) := Option (PointedGraphInterface Q d K)

def GraphRootRep {Q : Type} {d K : Nat} (P : List Graph → Prop) (M : Recognizer Graph Q)
    (g : List Graph) : GraphRootState Q d K → Prop
  | none => ¬ P g
  | some st => P g ∧ ∃ past, RepresentsGraphComponentUsing P M g st.1 past ∧ past st.2 = g

def graphRootLive {Q : Type} {d K : Nat} (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (state : GraphRootState Q d K) (g : Graph) : Bool :=
  match state with
  | none => false
  | some st => graphChildLive M st.1.2.2 (st.2,g)

def graphRootBoundary {Q : Type} {d K : Nat} (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (state : GraphRootState Q d K) (g : Graph) : Bool :=
  match state with
  | none => false
  | some st => graphStepBoundary M st.1.2.1 st.1.2.2 (st.2,g)

/-- A proposed next state must be the checked complete successor component,
with its actual child slot preserved. Forbidden prefixes enter the dead state. -/
def checkGraphRootStep {Q : Type} [Fintype Q] [DecidableEq Q] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (state : GraphRootState Q d K) (g : Graph) (next : GraphRootState Q d K) : Bool :=
  match state with
  | none => decide (next = none)
  | some st =>
    if graphChildLive M st.1.2.2 (st.2,g) then
      decide (∃ keep : GraphComponentReindex (Fin st.1.1.val) K,
        checkGraphReindex M st.1.2.1 st.1.2.2 (st.2,g) keep = true ∧
        ∃ point : Fin keep.1.val, keep.2 point = (st.2,g) ∧
          next = some ⟨graphReindexTarget M st.1.2.1 st.1.2.2 keep,point⟩)
    else decide (next = none)

theorem graphComponentUsing_same {Q : Type} {d K : Nat} (P : List Graph → Prop)
    (M : Recognizer Graph Q) (g : List Graph) (summary : SwitchInterface (GraphReceptionLabel Q d) K)
    (past : Fin summary.1.val → List Graph) (rep : RepresentsGraphComponentUsing P M g summary past)
    (s t : Fin summary.1.val) : Connected P (past s) (past t) :=
  (connected_symm P ((rep.2.1 _).mpr ⟨s,rfl⟩)).trans ((rep.2.1 _).mpr ⟨t,rfl⟩)

theorem graphComponentUsing_covers {Q : Type} {d K : Nat} (P : List Graph → Prop)
    (M : Recognizer Graph Q) (g : List Graph) (summary : SwitchInterface (GraphReceptionLabel Q d) K)
    (past : Fin summary.1.val → List Graph) (rep : RepresentsGraphComponentUsing P M g summary past)
    (s : Fin summary.1.val) (k : List Graph) (conn : Connected P (past s) k) : ∃ t, past t = k :=
  (rep.2.1 k).mp (((rep.2.1 _).mpr ⟨s,rfl⟩).trans conn)

theorem graphRootLive_exact {Q : Type} {d K : Nat} (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (g : List Graph) (state : GraphRootState Q d K) (rep : GraphRootRep P M g state) (r : Graph) :
    graphRootLive M state r = true ↔ P (g++[r]) := by
  cases state with
  | none =>
    change false = true ↔ P (g++[r])
    exact ⟨Bool.noConfusion,fun live => False.elim (rep (closed g [r] live))⟩
  | some st =>
    obtain ⟨_,past,data,point⟩ := rep
    have exactLive := graphChildLive_exact M d P recognizes past st.1.2.2 data.2.2.2 (st.2,r)
    simpa only [graphRootLive,graphChildHistory,point] using exactLive

/-- Boundary correctness is asserted on live extensions. Dead prefixes
have no hypothetical boundary obligation. Private inputs remain arbitrary. -/
theorem graphRootBoundary_exact {Q I₁ I₂ : Type} {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (h : EnvHistory I₁ I₂) (state : GraphRootState Q d K)
    (rep : GraphRootRep P M (History.graphSequence h) state)
    (r : RoundRecord I₁ I₂ Graph Unit Unit) (live : P (History.graphSequence (h++[r]))) :
    graphRootBoundary M state r.graph = leaderBoundary P d (h++[r]) := by
  cases state with
  | none =>
    exact False.elim (rep (by
      apply closed _ [r.graph]
      simpa only [History.graphSequence,List.map_append,List.map_cons,List.map_nil] using live))
  | some st =>
    obtain ⟨_,past,data,point⟩ := rep
    exact graphStepBoundary_exact M P closed recognizes d past st.1.2.1 data.2.2.1
      (graphComponentUsing_same P M _ st.1 past data) (graphComponentUsing_covers P M _ st.1 past data)
      st.1.2.2 data.2.2.2 (st.2,r.graph) (h++[r])
      (by simp only [History.graphSequence,List.map_append,List.map_cons,List.map_nil,graphChildHistory,point]) live

end Characterisation
