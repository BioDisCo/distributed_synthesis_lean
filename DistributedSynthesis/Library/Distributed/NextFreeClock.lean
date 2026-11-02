/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Library.Distributed.GraphExecutions
import DistributedSynthesis.Library.Distributed.BinaryAgreement
import DistributedSynthesis.Library.Logic.NextFree

/-! # A next-free clock for unrestricted full-view communication

Each process outputs a data bit and a clock bit. Agreement on every history
makes the clock constant across each positive-depth view path. Requiring the
graph to stay fixed until the clock changes then forces a change every round:
the environment can choose different graphs at any two consecutive rounds.
There is no restriction on the environment and no additional observation.
-/
namespace DistributedSynthesis.NextFreeClock
open FullViewPath GraphExecutions

abbrev Output := Bool × Bool
abbrev Atom := BinaryAgreement.Atom ⊕ Proc
abbrev Letter := RoundRecord Unit Unit Graph Output Output
abbrev Strategies := StrategyPair Unit Unit Output Output

def interp : Atom → Letter → Prop
  | .inl (.inl g), r => r.graph = g
  | .inl (.inr .one), r => r.outputOne.1 = true
  | .inl (.inr .two), r => r.outputTwo.1 = true
  | .inr .one, r => r.outputOne.2 = true
  | .inr .two, r => r.outputTwo.2 = true

def phase (b : Bool) : LTL Atom :=
  if b then .atom (.inr .one) else .neg (.atom (.inr .one))

def agreement : LTL Atom :=
  .conj (.disj (.neg (.atom (.inr .one))) (.atom (.inr .two)))
    (.disj (.neg (.atom (.inr .two))) (.atom (.inr .one)))

def rule (g : Graph) (b : Bool) : LTL Atom :=
  let p := LTL.conj (.atom (.inl (.inl g))) (phase b)
  .disj (.neg p) (.until p (.neg (phase b)))

def rules (g : Graph) : LTL Atom := .conj (rule g false) (rule g true)

def protocol : LTL Atom :=
  (LTL.conj agreement (.conj (rules .left) (.conj (rules .right) (rules .both)))).always

theorem protocol_nextFree : LTL.NextFree protocol := by
  simp [protocol, agreement, rules, rule, phase, LTL.always, LTL.NextFree]

theorem phase_iff (w : OmegaWord Letter) (t : Nat) (b : Bool) :
    LTL.Satisfies interp (w.drop t) (phase b) ↔ (w t).outputOne.2 = b := by
  cases b <;> cases h : (w t).outputOne.2 <;>
    simp [phase, LTL.Satisfies, interp, OmegaWord.drop, h]

theorem agreement_iff (w : OmegaWord Letter) (t : Nat) :
    LTL.Satisfies interp (w.drop t) agreement ↔
      (w t).outputOne.2 = (w t).outputTwo.2 := by
  cases h : (w t).outputOne.2 <;> cases k : (w t).outputTwo.2 <;>
    simp [agreement, LTL.Satisfies, interp, OmegaWord.drop, h, k]

def Conditions (w : OmegaWord Letter) : Prop :=
  (∀ t, (w t).outputOne.2 = (w t).outputTwo.2) ∧
  ∀ t g b, (w t).graph = g → (w t).outputOne.2 = b →
    ∃ n, (w (t+n)).outputOne.2 ≠ b ∧
      ∀ k, k < n → (w (t+k)).graph = g ∧ (w (t+k)).outputOne.2 = b

theorem rule_iff (w : OmegaWord Letter) (t : Nat) (g : Graph) (b : Bool) :
    LTL.Satisfies interp (w.drop t) (rule g b) ↔
      ((w t).graph = g → (w t).outputOne.2 = b →
        ∃ n, (w (t+n)).outputOne.2 ≠ b ∧
          ∀ k, k < n → (w (t+k)).graph = g ∧ (w (t+k)).outputOne.2 = b) := by
  simp only [rule, LTL.Satisfies, OmegaWord.drop_drop, phase_iff]
  simp only [interp, OmegaWord.drop_apply, Nat.add_zero]
  tauto

theorem protocol_iff (w : OmegaWord Letter) :
    LTL.Satisfies interp w protocol ↔ Conditions w := by
  simp only [protocol, LTL.satisfies_always, LTL.Satisfies, rules, agreement_iff, rule_iff]
  constructor
  · intro h
    refine ⟨fun t ↦ (h t).1, ?_⟩
    intro t g b
    cases g <;> cases b
    all_goals first | exact (h t).2.1.1 | exact (h t).2.1.2 |
      exact (h t).2.2.1.1 | exact (h t).2.2.1.2 |
      exact (h t).2.2.2.1 | exact (h t).2.2.2.2
  · rintro ⟨ha, hr⟩ t
    exact ⟨ha t, ⟨hr t .left false, hr t .left true⟩,
      ⟨hr t .right false, hr t .right true⟩,
      hr t .both false, hr t .both true⟩

theorem graph_change (w : OmegaWord Letter) (h : Conditions w) (t : Nat)
    (hg : (w (t+1)).graph ≠ (w t).graph) :
    (w (t+1)).outputOne.2 ≠ (w t).outputOne.2 := by
  intro hc
  obtain ⟨n, hn, hall⟩ := h.2 t (w t).graph (w t).outputOne.2 rfl rfl
  have h₀ : n ≠ 0 := by intro he; subst n; simp at hn
  have h₁ : n ≠ 1 := by intro he; subst n; exact hn hc
  exact hg (hall 1 (by omega)).1

/-- Equality on every history edge propagates to all process-one views at
the same depth. The label type need not be Boolean. -/
theorem history_uniform {O : Type*} (f₁ : View Unit Unit .one → O)
    (f₂ : View Unit Unit .two → O) (t : Nat)
    (he : ∀ h : List Graph, h.length = t → f₁ (evaluate h).one = f₂ (evaluate h).two)
    (h k : List Graph) (hh : h.length = t) (hk : k.length = t) :
    f₁ (evaluate h).one = f₁ (evaluate k).one := by
  let label : Vertex → O := Sum.elim f₁ f₂
  have visited (s : Cell) (hs : s ∈ row t) :
      ScalingRow.Path.Visits right (blind^[t] (left root)) (row t) (.inl s.one) := by
    have hv := endpoints_visited hs
    cases ho : s.oneLeft
    · simpa [left, right, ho] using hv.2
    · simpa [left, right, ho] using hv.1
  apply (row_path t).fiber_uniform (fun _ ↦ 0) label (by simp) _
    (visited _ ((mem_row_iff _ _).mpr ⟨h, hh, rfl⟩))
    (visited _ ((mem_row_iff _ _).mpr ⟨k, hk, rfl⟩)) rfl
  intro s hs _
  obtain ⟨h, hh, rfl⟩ := (mem_row_iff _ _).mp hs
  have he := he h hh
  cases ho : (evaluate h).oneLeft <;> simp [label, left, right, ho, he]

theorem execution_uniform (σ : Strategies)
    (win : ∀ env, LTL.Satisfies interp (execution σ env) protocol)
    (env env' : EnvironmentSequence Unit Unit) (t : Nat) :
    (execution σ env t).outputOne.2 = (execution σ env' t).outputOne.2 := by
  have finite (h : List Graph) (hh : h.length = t+1) :
      (σ.one (evaluate h).one).2 = (σ.two (evaluate h).two).2 := by
    have ha := ((protocol_iff _).mp (win (extend h))).1 (h.length-1)
    have ho := extend_outputs σ h (by omega)
    rwa [ho.1, ho.2] at ha
  rw [(execution_outputs σ env t).1, (execution_outputs σ env' t).1]
  exact history_uniform (fun v ↦ (σ.one v).2) (fun v ↦ (σ.two v).2) (t+1) finite
    _ _ (BlockEmbedding.prefix_length _ _) (BlockEmbedding.prefix_length _ _)

/-- Universal winning, not a restriction on a single word, forces the clock
to change in every physical round. -/
theorem winning_alternates (σ : Strategies)
    (win : ∀ env, LTL.Satisfies interp (execution σ env) protocol)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    (execution σ env (t+1)).outputOne.2 ≠ (execution σ env t).outputOne.2 := by
  let other := ofGraphs (fun k ↦ if k = t then Graph.left else Graph.right)
  have hc := graph_change (execution σ other) ((protocol_iff _).mp (win other)) t (by
    rw [execution_graph, execution_graph]
    simp [other, ofGraphs])
  rwa [execution_uniform σ win other env (t+1), execution_uniform σ win other env t] at hc

theorem of_alternating (w : OmegaWord Letter)
    (ha : ∀ t, (w t).outputOne.2 = (w t).outputTwo.2)
    (hc : ∀ t, (w (t+1)).outputOne.2 ≠ (w t).outputOne.2) :
    LTL.Satisfies interp w protocol := by
  apply (protocol_iff _).mpr
  refine ⟨ha, ?_⟩
  intro t g b hg hb
  refine ⟨1, by simpa [← hb] using hc t, ?_⟩
  intro k hk
  have : k = 0 := by omega
  simpa [this] using And.intro hg hb

end DistributedSynthesis.NextFreeClock
