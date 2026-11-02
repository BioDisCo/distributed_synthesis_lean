/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedRunTree

/-! # Enumerating finite tree-transition relations -/
namespace DistributedSynthesis.EncodedRunTree

/-- Enumerate a decidable relation over all bounded source states, labels, and
successor vectors, using the existing finite-function tables. -/
def enumerate (b n a : Nat) (p : Nat → Nat → List Nat → Prop)
    [∀ q l v, Decidable (p q l v)] : List Transition :=
  ((List.range n).flatMap fun q => (List.range a).flatMap fun l =>
    (FiniteFunctionCoding.codes b n).map (fun v => (q, l, v))).filter
      (fun t => decide (p t.1 t.2.1 t.2.2))

theorem mem_enumerate (b n a : Nat) (p : Nat → Nat → List Nat → Prop)
    [∀ q l v, Decidable (p q l v)] (q l : Nat) (v : List Nat) :
    (q, l, v) ∈ enumerate b n a p ↔
      q < n ∧ l < a ∧ v ∈ FiniteFunctionCoding.codes b n ∧ p q l v := by
  simp only [enumerate, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨q', hq, l', hl, v', hv, rfl, rfl, rfl⟩, hp⟩
    exact ⟨hq, hl, hv, hp⟩
  · rintro ⟨hq, hl, hv, hp⟩
    exact ⟨⟨q, hq, l, hl, v, hv, rfl, rfl, rfl⟩, hp⟩

variable {X : Type*} [Primcodable X]

/-- Uniform primitive recursiveness of finite transition-table construction. -/
theorem enumerate_primrec {b n a : X → Nat} {p : X → Nat → Nat → List Nat → Prop}
    [∀ x q l v, Decidable (p x q l v)]
    (hb : Primrec b) (hn : Primrec n) (ha : Primrec a)
    (hp : PrimrecPred (fun x : X × Nat × Nat × List Nat => p x.1 x.2.1 x.2.2.1 x.2.2.2)) :
    Primrec (fun x => enumerate (b x) (n x) (a x) (p x)) := by
  have hc : Primrec (fun x => FiniteFunctionCoding.codes (b x) (n x)) :=
    FiniteFunctionCoding.codes_primrec.comp hb hn
  unfold enumerate
  apply PrimrecFunProp.filter
  · apply PrimrecFunProp.flatMap (Primrec.list_range.comp hn)
    apply PrimrecFunProp.flatMap (Primrec.list_range.comp (ha.comp Primrec.fst))
    apply PrimrecFunProp.map (hc.comp (Primrec.fst.comp Primrec.fst))
    exact (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  · exact hp

end DistributedSynthesis.EncodedRunTree
