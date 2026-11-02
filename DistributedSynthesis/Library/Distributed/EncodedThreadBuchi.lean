/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedThreadBuchi
import DistributedSynthesis.Library.Distributed.ThreadComputable

/-! # Bad-thread table correctness for block-record monitors -/

namespace DistributedSynthesis.EncodedThreadBuchi

variable {RIn SIn ROut SOut : Type*} (M : BlockRecordMonitor RIn SIn ROut SOut)
  [Fintype RIn] [DecidableEq M.State]
  (number : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (number q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ ThreadComputable.priorityRange M)

def encode (s : ThreadComputable.GuessState M) : State :=
  ((number s.1).val, s.2.map Subtype.val)

private theorem even_iff (p : Nat) : DetParityAutomaton.NatEven p ↔ p % 2 = 0 := by
  unfold DetParityAutomaton.NatEven
  constructor
  · rintro ⟨k, rfl⟩; omega
  · intro h; exact ⟨p / 2, by omega⟩

include hp hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem step_correct (ed : Edges) (a : BlockRecordMonitor.ThreadLetter M)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ ed ↔
      ∃ i : RIn, r = M.step q (narrowedRecord M a.1 q (i, a.2)))
    (s t : ThreadComputable.GuessState M) :
    step ((ps, ed), encode M number s, encode M number t) ↔
      (ThreadComputable.buchi M).step s a t := by
  have hsome (tag : Option {p : Nat // p ∈ ThreadComputable.priorityRange M})
      (p : {p : Nat // p ∈ ThreadComputable.priorityRange M}) :
      tag.map Subtype.val = some p.val ↔ tag = some p := by
    cases tag with
    | none => simp
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact Subtype.val_injective.eq_iff
  have hex (P : Nat → Prop) : (∃ p ∈ ps, P p) ↔
      ∃ p : {p : Nat // p ∈ ThreadComputable.priorityRange M}, P p.val := by
    constructor
    · rintro ⟨p, h, hp⟩; exact ⟨⟨p, (hr p).mp h⟩, hp⟩
    · rintro ⟨p, h⟩; exact ⟨p.val, (hr p.val).mpr p.property, h⟩
  simp only [step, encode, he, hp, hex, hsome, Option.map_eq_none_iff,
    ThreadComputable.buchi, even_iff]

include hp hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem accepting_correct (s : ThreadComputable.GuessState M) :
    accepting ps (encode M number s) ↔ (ThreadComputable.buchi M).accepting s := by
  unfold accepting encode ThreadComputable.buchi
  simp only [hp]
  constructor
  · rintro ⟨p, hmem, ht, he⟩
    obtain ⟨tag, htag, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨tag, htag, he⟩
  · rintro ⟨tag, htag, he⟩
    exact ⟨tag.val, (hr tag.val).mpr tag.property, by simp [htag], he⟩

include hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem states_complete (s : ThreadComputable.GuessState M) :
    encode M number s ∈ states (Fintype.card M.State) ps := by
  apply List.mem_product.mpr
  refine ⟨List.mem_range.mpr (number s.1).isLt, ?_⟩
  cases h : s.2 with
  | none => simp [encode, h]
  | some p =>
    simp only [encode, h, Option.map_some, List.mem_cons, List.mem_map]
    exact Or.inr ⟨p.val, (hr p.val).mpr p.property, rfl⟩

omit [Fintype RIn] [DecidableEq M.State] in
theorem encode_injective : Function.Injective (encode M number) := by
  intro s t h
  exact Prod.ext (number.injective (Fin.ext (congrArg Prod.fst h)))
    (Option.map_injective Subtype.val_injective (congrArg Prod.snd h))

include hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem states_sound (c : State) (hc : c ∈ states (Fintype.card M.State) ps) :
    ∃ s : ThreadComputable.GuessState M, encode M number s = c := by
  obtain ⟨hq, ht⟩ := List.mem_product.mp hc
  have hq' := List.mem_range.mp hq
  let q := number.symm ⟨c.1,hq'⟩
  cases h : c.2 with
  | none =>
    refine ⟨(q,none), ?_⟩
    simp only [encode, q, Equiv.apply_symm_apply, Option.map_none]
    exact Prod.ext rfl h.symm
  | some p =>
    have hp : p ∈ ps := by simpa only [h, List.mem_cons, Option.some_ne_none,
      List.mem_map, Option.some.injEq, exists_eq_right, false_or] using ht
    refine ⟨(q,some ⟨p,(hr p).mp hp⟩), ?_⟩
    simp only [encode, q, Equiv.apply_symm_apply, Option.map_some]
    exact Prod.ext rfl h.symm

end DistributedSynthesis.EncodedThreadBuchi
