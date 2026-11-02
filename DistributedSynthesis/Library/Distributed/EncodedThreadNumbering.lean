/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedThreadNumbering
import DistributedSynthesis.Library.Distributed.EncodedThreadBuchi

namespace DistributedSynthesis.EncodedThreadNumbering
open EncodedThreadBuchi

section Semantic
variable {RIn SIn ROut SOut : Type*} (M : BlockRecordMonitor RIn SIn ROut SOut)
  [Fintype RIn] [DecidableEq M.State]
  (baseNumber : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (baseNumber q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ ThreadComputable.priorityRange M)

noncomputable def number : ThreadComputable.GuessState M ≃
    Fin (Fintype.card (ThreadComputable.GuessState M)) :=
  FiniteCodeNumbering.number (states (Fintype.card M.State) ps) (encode M baseNumber)
    (encode_injective M baseNumber) (states_complete M baseNumber ps hr)
    (states_sound M baseNumber ps hr)

omit [Fintype RIn] [DecidableEq M.State] in
theorem number_val (s : ThreadComputable.GuessState M) :
    (number M baseNumber ps hr s).val = name (Fintype.card M.State,ps) (encode M baseNumber s) := rfl

include baseNumber hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem card_eq : Fintype.card (ThreadComputable.GuessState M) =
    (codes (Fintype.card M.State,ps)).length :=
  FiniteCodeNumbering.card_eq _ (encode M baseNumber) (encode_injective M baseNumber)
    (states_complete M baseNumber ps hr) (states_sound M baseNumber ps hr)

include hp hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem edges_correct (es : Edges) (a : BlockRecordMonitor.ThreadLetter M)
    (he : ∀ q r, ((baseNumber q).val,(baseNumber r).val) ∈ es ↔
      ∃ i : RIn, r = M.step q (narrowedRecord M a.1 q (i,a.2)))
    (s t : ThreadComputable.GuessState M) :
    ((number M baseNumber ps hr s).val,(number M baseNumber ps hr t).val) ∈
      edges (Fintype.card M.State,ps) es ↔ (ThreadComputable.buchi M).step s a t := by
  simp only [edges,List.mem_map,number_val]
  constructor
  · rintro ⟨⟨u,v⟩,hm,heq⟩
    obtain ⟨hu,hv,hstep⟩ := (EncodedThreadBuchi.mem_edges _ _ u v).mp hm
    obtain ⟨hue,hve⟩ := Prod.mk.inj heq
    obtain rfl := FiniteCodeNumbering.name_injective _ hu (states_complete M baseNumber ps hr s) hue
    obtain rfl := FiniteCodeNumbering.name_injective _ hv (states_complete M baseNumber ps hr t) hve
    exact (step_correct M baseNumber ps hp hr es a he s t).mp hstep
  · intro h
    refine ⟨(encode M baseNumber s,encode M baseNumber t),?_,rfl⟩
    exact (EncodedThreadBuchi.mem_edges _ _ _ _).mpr
      ⟨states_complete M baseNumber ps hr s, states_complete M baseNumber ps hr t,
        (step_correct M baseNumber ps hp hr es a he s t).mpr h⟩

include hp hr in
omit [Fintype RIn] [DecidableEq M.State] in
theorem accepting_correct (s : ThreadComputable.GuessState M) :
    (number M baseNumber ps hr s).val ∈ accepting (Fintype.card M.State,ps) ↔
      (ThreadComputable.buchi M).accepting s := by
  simp only [accepting,List.mem_map,number_val]
  constructor
  · rintro ⟨t,ht,he⟩
    obtain ⟨ht,hacc⟩ := List.mem_filter.mp ht
    obtain rfl := FiniteCodeNumbering.name_injective _ ht (states_complete M baseNumber ps hr s) he
    exact (EncodedThreadBuchi.accepting_correct M baseNumber ps hp hr s).mp (of_decide_eq_true hacc)
  · intro h
    exact ⟨encode M baseNumber s,List.mem_filter.mpr ⟨states_complete M baseNumber ps hr s,
      decide_eq_true ((EncodedThreadBuchi.accepting_correct M baseNumber ps hp hr s).mpr h)⟩,rfl⟩
end Semantic
end DistributedSynthesis.EncodedThreadNumbering
