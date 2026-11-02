/- Extracted from consensusLTL/lean/ConsensusLTL/Cone.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Konig
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

/-- **The in-regime bit is the silence of the suffix.**  Inside the cone spawned at a reception
child of the base, being a first return of that base says exactly that no reception has occurred
since, which is a bit the automaton can carry down and which never turns back on. -/
theorem firstReturn_cone {p : Bool} {h t : List Letter} {g : Letter} (hg : g.hears p = true) :
    FirstReturn p (some h) (h ++ g :: t) ↔ ∀ a ∈ t, a.hears p = false := by
  constructor
  · rintro ⟨g', t', hg', ht', heq⟩
    have hcan := List.append_cancel_left heq.symm
    obtain ⟨rfl, rfl⟩ : g' = g ∧ t' = t :=
      ⟨(List.cons.inj hcan).1, (List.cons.inj hcan).2⟩
    exact ht'
  · intro ht
    exact ⟨g, t, hg, ht, rfl⟩

/-- **The sealed condition.**  Having no bad node above `x` is the safety condition: every node
above `x` that is still in regime is good. -/
theorem noBelow_iff_regime_good {K : Type*} {p : Bool} {C : Bool → Base → K} {b : Base} {c : K}
    {x : List Letter} :
    NoBelow (Bad p C b c) x ↔ ∀ j, x <+: j → FirstReturn p b j → Good p C j c := by
  constructor
  · intro h j hj hfr
    by_contra hg
    exact h j hj ⟨hfr, hg⟩
  · rintro h j hj ⟨hfr, hg⟩
    exact hg (h j hj hfr)

/-- **Staying in regime means silence.**  If a history and an extension of it are both first
returns of the same base, the letters in between are not receptions.  This is what lets the
automaton carry the regime as one bit. -/
theorem firstReturn_suffix_silent {p : Bool} {b : Base} {x s : List Letter}
    (hx : FirstReturn p b x) (hxs : FirstReturn p b (x ++ s)) :
    ∀ a ∈ s, a.hears p = false := by
  rcases b with _ | h
  · intro a ha
    exact hxs a (List.mem_append_right _ ha)
  · obtain ⟨g, t, hg, ht, hxe⟩ := hx
    obtain ⟨g', t', hg', ht', hxse⟩ := hxs
    rw [hxe, List.append_assoc, List.cons_append] at hxse
    have hcan := List.append_cancel_left hxse
    obtain ⟨-, hts⟩ : g = g' ∧ t ++ s = t' :=
      ⟨(List.cons.inj hcan).1, (List.cons.inj hcan).2⟩
    intro a ha
    exact ht' a (hts ▸ List.mem_append_right _ ha)

/-- **A reception discharges the check without sealing it.**  Inside the cone of a received base,
once a reception has occurred since the base no node above is a first return of it, so nothing
above is bad.  This is why a branch that hears again need not seal the old check. -/
theorem noBelow_of_not_silent {K : Type*} {p : Bool} {C : Bool → Base → K} {h u : List Letter}
    {g : Letter} {c : K} (hg : g.hears p = true) (hu : ∃ a ∈ u, a.hears p = true) :
    NoBelow (Bad p C (some h) c) (h ++ g :: u) := by
  rintro j hj ⟨hfr, -⟩
  obtain ⟨v, rfl⟩ := hj
  have hassoc : h ++ g :: u ++ v = h ++ g :: (u ++ v) := by
    simp
  rw [hassoc, firstReturn_cone hg] at hfr
  obtain ⟨a, ha, hah⟩ := hu
  rw [hfr a (List.mem_append_left _ ha)] at hah
  exact Bool.false_ne_true hah

/-- **A non-reception child leaves the cone.**  Nothing above a child of the base by a
non-reception letter is a first return of that base. -/
theorem noBelow_of_nonrec {K : Type*} {p : Bool} {C : Bool → Base → K} {h : List Letter}
    {a : Letter} {c : K} (ha : a.hears p = false) :
    NoBelow (Bad p C (some h) c) (h ++ [a]) := by
  rintro j hj ⟨hfr, -⟩
  obtain ⟨v, rfl⟩ := hj
  have hassoc : h ++ [a] ++ v = h ++ a :: v := by simp
  rw [hassoc] at hfr
  obtain ⟨g, u, hg, -, heq⟩ := hfr
  have hcan := List.append_cancel_left heq
  have : a = g := (List.cons.inj hcan).1
  rw [← this, ha] at hg
  exact Bool.false_ne_true hg

/-- **A reception leaves the initial cone.**  The first returns of the initial base are the
histories with no reception, so once one has occurred nothing above is bad. -/
theorem noBelow_none_of_rec {K : Type*} {p : Bool} {C : Bool → Base → K} {c : K}
    {x : List Letter} (hx : ∃ a ∈ x, a.hears p = true) :
    NoBelow (Bad p C none c) x := by
  rintro j hj ⟨hfr, -⟩
  obtain ⟨v, rfl⟩ := hj
  obtain ⟨a, ha, hah⟩ := hx
  rw [hfr a (List.mem_append_left _ ha)] at hah
  exact Bool.false_ne_true hah

theorem bad_subset_cone {K : Type*} {p : Bool} {C : Bool → Base → K} {h : List Letter} {c : K}
    {j : List Letter} (hj : j ∈ Bad p C (some h) c) : h <+: j := by
  obtain ⟨⟨g, t, -, -, rfl⟩, -⟩ := hj
  exact ⟨g :: t, rfl⟩

/-- Outside the cone of a received base there is nothing to check. -/
theorem noBelow_of_not_prefix {K : Type*} {p : Bool} {C : Bool → Base → K} {h : List Letter}
    {c : K} {x : List Letter} (hx : ¬ h <+: x) (hlen : h.length ≤ x.length) :
    NoBelow (Bad p C (some h) c) x := by
  intro j hj hbad
  have hhj : h <+: j := bad_subset_cone hbad
  exact hx (((List.prefix_or_prefix_of_prefix hhj hj).resolve_right
    (fun hxh => hx (by
      have : x = h := hxh.eq_of_length (le_antisymm hxh.length_le hlen)
      exact this ▸ List.prefix_rfl))))

end DistributedSynthesis.DecisionTasks.Source
