/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.SwitchComponents

/-! A common coordinator selects prescriptions, not actual outputs depending
on hidden inputs. One-round prescriptions at bounded components are finite
and exactly implementable by the original local strategies. -/
namespace Characterisation
open DistributedSynthesis

theorem factor_local_response {X V O : Type*} [Nonempty O]
    (view : X → V) (out : X → O)
    (coherent : ∀ x y, view x = view y → out x = out y) :
    ∃ f : V → O, ∀ x, f (view x) = out x := by
  classical
  let f v := if hv : ∃ x, view x = v then out hv.choose else Classical.choice inferInstance
  refine ⟨f, ?_⟩
  intro x
  have hx : ∃ y, view y = view x := ⟨x,rfl⟩
  simp only [f, dif_pos hx]
  exact coherent _ _ hx.choose_spec

/-- A scenario consists of a history slot, two fresh private inputs, and a
communication graph. The coordinator's table covers all scenarios at once. -/
abbrev NextScenario (H I₁ I₂ : Type*) := H × I₁ × I₂ × Graph

def scenarioHistory {H I₁ I₂ : Type*} (past : H → EnvHistory I₁ I₂)
    (s : NextScenario H I₁ I₂) : EnvHistory I₁ I₂ :=
  past s.1 ++ [⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩]

def ResponseCoherent {H I₁ I₂ O₁ O₂ : Type*} (past : H → EnvHistory I₁ I₂)
    (out : NextScenario H I₁ I₂ → O₁ × O₂) : Prop :=
  (∀ s t, currentView .one (scenarioHistory past s) = currentView .one (scenarioHistory past t) →
    (out s).1 = (out t).1) ∧
  (∀ s t, currentView .two (scenarioHistory past s) = currentView .two (scenarioHistory past t) →
    (out s).2 = (out t).2)

/-- Tables that prescribe the same output at equal local views. Graph slots,
private inputs, and receipt alternatives are not revealed to the processes. -/
def CoordinatorTable {H I₁ I₂ : Type*} (O₁ O₂ : Type*) (past : H → EnvHistory I₁ I₂) :=
  {out : NextScenario H I₁ I₂ → O₁ × O₂ // ResponseCoherent past out}

/-- Exact local implementation of one-round coordinator tables, with no
additional communication or observation available to either process. -/
theorem coordinator_table_iff_local {H I₁ I₂ O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (out : NextScenario H I₁ I₂ → O₁ × O₂) :
    ResponseCoherent past out ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ s,
      σ.one (currentView .one (scenarioHistory past s)) = (out s).1 ∧
      σ.two (currentView .two (scenarioHistory past s)) = (out s).2 := by
  constructor
  · intro coherent
    obtain ⟨one,hone⟩ := factor_local_response (fun s => currentView .one (scenarioHistory past s))
      (fun s => (out s).1) coherent.1
    obtain ⟨two,htwo⟩ := factor_local_response (fun s => currentView .two (scenarioHistory past s))
      (fun s => (out s).2) coherent.2
    exact ⟨⟨one,two⟩, fun s => ⟨hone s,htwo s⟩⟩
  · rintro ⟨σ, hs⟩
    constructor
    · intro s t eq
      rw [← (hs s).1, ← (hs t).1, eq]
    · intro s t eq
      rw [← (hs s).2, ← (hs t).2, eq]

instance coordinatorTable_finite {H I₁ I₂ O₁ O₂ : Type*}
    [Finite H] [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂]
    (past : H → EnvHistory I₁ I₂) : Finite (CoordinatorTable O₁ O₂ past) := by
  unfold CoordinatorTable
  infer_instance

/-- The current receiver cannot distinguish one-way from bidirectional
communication. A coordinator must therefore share that receiver's response. -/
theorem coordinator_receiver_shared {H I₁ I₂ O₁ O₂ : Type*}
    (past : H → EnvHistory I₁ I₂) (out : NextScenario H I₁ I₂ → O₁ × O₂)
    (coherent : ResponseCoherent past out) (h : H) (x : I₁) (y : I₂) :
    (out (h,x,y,Graph.right)).2 = (out (h,x,y,Graph.both)).2 ∧
    (out (h,x,y,Graph.left)).1 = (out (h,x,y,Graph.both)).1 := by
  constructor
  · apply coherent.2
    change currentView .two (History.append _ _) = currentView .two (History.append _ _)
    rw [currentView_two_append, currentView_two_append]
  · apply coherent.1
    change currentView .one (History.append _ _) = currentView .one (History.append _ _)
    rw [currentView_one_append, currentView_one_append]

/-- At every owner switch, the common node has a finite menu of locally
implementable one-round prescriptions. A global finite summary is still needed
to compose these menus across unboundedly many rounds. -/
theorem finite_coordinator_tables_at_switch {I₁ I₂ O₁ O₂ : Type*}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (bounded : BoundedViewComponents P)
    (d : Nat) (old new : Proc) (h : EnvHistory I₁ I₂) (hh : P (History.graphSequence h))
    (changed : old ≠ new)
    (oldRecent : RecentOther P d (History.graphSequence h.dropLast) old)
    (newRecent : RecentOther P d (History.graphSequence h) new) :
    Finite (CoordinatorTable O₁ O₂ (fun k : InputHistoryComponent P h => k.val)) := by
  letI : Finite (InputHistoryComponent P h) :=
    finite_component_at_switch P closed bounded d old new h hh changed oldRecent newRecent
  infer_instance

/-- All observation prefixes of lengths 1 through d following a history
slot. A table is selected before any of these future input values are known. -/
abbrev WindowScenario (H I₁ I₂ : Type*) (d : Nat) :=
  H × (Σ n : Fin d, Fin (n.val+1) → I₁ × I₂ × Graph)

def windowHistory {H I₁ I₂ : Type*} (past : H → EnvHistory I₁ I₂)
    (d : Nat) (s : WindowScenario H I₁ I₂ d) : EnvHistory I₁ I₂ :=
  past s.1 ++ List.ofFn (fun i =>
    let r := s.2.2 i
    (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit))

def WindowCoherent {H I₁ I₂ O₁ O₂ : Type*} (past : H → EnvHistory I₁ I₂)
    (d : Nat) (out : WindowScenario H I₁ I₂ d → O₁ × O₂) : Prop :=
  (∀ s t, currentView .one (windowHistory past d s) = currentView .one (windowHistory past d t) →
    (out s).1 = (out t).1) ∧
  (∀ s t, currentView .two (windowHistory past d s) = currentView .two (windowHistory past d t) →
    (out s).2 = (out t).2)

def WindowTable {H I₁ I₂ : Type*} (O₁ O₂ : Type*) (past : H → EnvHistory I₁ I₂) (d : Nat) :=
  {out : WindowScenario H I₁ I₂ d → O₁ × O₂ // WindowCoherent past d out}

/-- Finite contingent instructions cover an entire bounded delay window. -/
instance windowTable_finite {H I₁ I₂ O₁ O₂ : Type*}
    [Finite H] [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂]
    (past : H → EnvHistory I₁ I₂) (d : Nat) : Finite (WindowTable O₁ O₂ past d) := by
  unfold WindowTable WindowScenario
  infer_instance

/-- Exact preservation of all local output choices throughout the window.
The prescription cannot depend on a graph or input not visible in that view. -/
theorem window_table_iff_local {H I₁ I₂ O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (d : Nat)
    (out : WindowScenario H I₁ I₂ d → O₁ × O₂) :
    WindowCoherent past d out ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ s,
      σ.one (currentView .one (windowHistory past d s)) = (out s).1 ∧
      σ.two (currentView .two (windowHistory past d s)) = (out s).2 := by
  constructor
  · intro coherent
    obtain ⟨one,hone⟩ := factor_local_response (fun s => currentView .one (windowHistory past d s))
      (fun s => (out s).1) coherent.1
    obtain ⟨two,htwo⟩ := factor_local_response (fun s => currentView .two (windowHistory past d s))
      (fun s => (out s).2) coherent.2
    exact ⟨⟨one,two⟩, fun s => ⟨hone s,htwo s⟩⟩
  · rintro ⟨σ, hs⟩
    constructor
    · intro s t eq
      rw [← (hs s).1, ← (hs t).1, eq]
    · intro s t eq
      rw [← (hs s).2, ← (hs t).2, eq]

/-- One can choose finite delay-window tables at every bounded switch
component. This does not yet assert compatibility of successive tables. -/
theorem finite_window_tables_at_switch {I₁ I₂ O₁ O₂ : Type*}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (bounded : BoundedViewComponents P)
    (d window : Nat) (old new : Proc) (h : EnvHistory I₁ I₂) (hh : P (History.graphSequence h))
    (changed : old ≠ new)
    (oldRecent : RecentOther P d (History.graphSequence h.dropLast) old)
    (newRecent : RecentOther P d (History.graphSequence h) new) :
    Finite (WindowTable O₁ O₂ (fun k : InputHistoryComponent P h => k.val) window) := by
  letI : Finite (InputHistoryComponent P h) :=
    finite_component_at_switch P closed bounded d old new h hh changed oldRecent newRecent
  infer_instance

end Characterisation
