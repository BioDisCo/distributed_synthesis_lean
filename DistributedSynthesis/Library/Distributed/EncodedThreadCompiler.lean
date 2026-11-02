/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedThreadCompiler
import DistributedSynthesis.Library.Distributed.EncodedThreadNumbering

namespace DistributedSynthesis.EncodedThreadCompiler
open EncodedThreadBuchi

section Semantic
private theorem cast_automaton_congr {k : Nat} (x y : EncodedPitermanCompiler.Input)
    (h : x = y) (hx : x.2.2.2.length = k) (hy : y.2.2.2.length = k) :
    (EncodedPitermanCompiler.automaton x).comap (Fin.cast hx.symm) =
      (EncodedPitermanCompiler.automaton y).comap (Fin.cast hy.symm) := by
  cases h
  rfl

variable {RIn SIn ROut SOut : Type*} (M : BlockRecordMonitor RIn SIn ROut SOut)
  [Fintype RIn] [DecidableEq M.State]
  (baseNumber : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (baseNumber q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ ThreadComputable.priorityRange M)
  (es : List Edges) (letter : Fin es.length → BlockRecordMonitor.ThreadLetter M)
  (he : ∀ q (a : Fin es.length) r,
    ((baseNumber q).val,(baseNumber r).val) ∈ es[a.val]?.getD [] ↔
      ∃ i : RIn, r = M.step q (narrowedRecord M (letter a).1 q (i,(letter a).2)))

def sourceData : Input := (Fintype.card M.State,(baseNumber M.initial).val,ps,es)

def sourceBuchi : NondetBuchiAutomaton (Fin es.length) where
  State := ThreadComputable.GuessState M
  stateFinite := inferInstance
  initial := (M.initial,none)
  step := fun q a r => (ThreadComputable.buchi M).step q (letter a) r
  accepting := (ThreadComputable.buchi M).accepting

local instance : DecidableEq (sourceBuchi M es letter).State :=
  inferInstanceAs (DecidableEq (ThreadComputable.GuessState M))

include hp hr he in
theorem bad_accepts_iff (word : OmegaWord (Fin es.length)) :
    (badAutomaton (sourceData M baseNumber ps es)).Accepts word ↔
      (ThreadComputable.buchi M).Accepts (OmegaWord.map letter word) := by
  let B := sourceBuchi M es letter
  let num := EncodedThreadNumbering.number M baseNumber ps hr
  have hc : EncodedThreadNumbering.compile (sourceData M baseNumber ps es) =
      (Fintype.card B.State, (num B.initial).val,
        EncodedThreadNumbering.accepting (Fintype.card M.State,ps),
        es.map (EncodedThreadNumbering.edges (Fintype.card M.State,ps))) := by
    unfold EncodedThreadNumbering.compile sourceData
    rw [← EncodedThreadNumbering.card_eq M baseNumber ps hr]
    rfl
  have hlen : (es.map (EncodedThreadNumbering.edges (Fintype.card M.State,ps))).length = es.length :=
    List.length_map _
  have hedge (q : B.State) (a : Fin es.length) (r : B.State) :
      ((num q).val,(num r).val) ∈
        (es.map (EncodedThreadNumbering.edges (Fintype.card M.State,ps)))[a.val]?.getD [] ↔ B.step q a r := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem a.isLt, Option.map_some, Option.getD_some]
    apply EncodedThreadNumbering.edges_correct M baseNumber ps hp hr _ (letter a)
    intro q r
    simpa only [List.getElem?_eq_getElem a.isLt, Option.getD_some] using he q a r
  have hacc (q : B.State) : (num q).val ∈
      EncodedThreadNumbering.accepting (Fintype.card M.State,ps) ↔ B.accepting q :=
    EncodedThreadNumbering.accepting_correct M baseNumber ps hp hr q
  have h := EncodedPitermanCompiler.accepts_iff B num
    (fun q a r => ThreadComputable.stepDecidable M q (letter a) r)
    (ThreadComputable.acceptingDecidable M) _ hlen _ hedge hacc word
  have hEq := cast_automaton_congr _ _ hc
    (EncodedThreadNumbering.alphabet_size (sourceData M baseNumber ps es)) hlen
  have hProp := congrArg (fun D : DetParityAutomaton (Fin es.length) => D.Accepts word) hEq
  refine (Iff.of_eq hProp).trans (h.trans ?_)
  constructor <;> rintro ⟨run,hrun⟩ <;>
    exact ⟨⟨run.path,run.initial_state,run.step_valid⟩,hrun⟩

include hp hr he in
theorem accepts_iff_not_bad (word : OmegaWord (Fin es.length)) :
    (automaton (sourceData M baseNumber ps es)).Accepts word ↔
      ¬ (ThreadComputable.buchi M).Accepts (OmegaWord.map letter word) := by
  rw [automaton,DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts]
  exact not_congr (bad_accepts_iff M baseNumber ps hp hr es letter he word)

include hp hr he in
theorem accepts_iff (word : OmegaWord (Fin es.length)) :
    (automaton (sourceData M baseNumber ps es)).Accepts word ↔
      ∀ q : Nat → M.State, M.IsThread (OmegaWord.map letter word) q →
        NatSeqMinEvenParity (fun n => M.priority (q n)) := by
  rw [accepts_iff_not_bad M baseNumber ps hp hr es letter he,
    ThreadComputable.accepts_iff,BlockRecordMonitor.threadBuchi_accepts_iff]
  constructor
  · intro hnot q hthread
    rcases natSeqMinEvenParity_or_minOddParity (fun n => M.priority (q n))
      (BlockRecordMonitor.priority_range_finite M q) with heven | hodd
    · exact heven
    · exact absurd ⟨q,hthread,hodd⟩ hnot
  · rintro hall ⟨q,hthread,hodd⟩
    exact not_natSeqMinEvenParity_and_natSeqMinOddParity _ ⟨hall q hthread,hodd⟩
end Semantic
end DistributedSynthesis.EncodedThreadCompiler
