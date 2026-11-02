/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedThreadCompiler

/-! # Thread checkers with one edge list supplied at each step

The numeric state carrier depends only on the base-state count and priorities.
The initial state may vary with a boundary; edge lists may vary with a handoff
set. No complete letter alphabet needs to be materialized to take a step.
-/
namespace DistributedSynthesis.EncodedThreadStream
abbrev Config := Nat × Nat × List Nat
def base (c : Config) : EncodedThreadNumbering.Context := (c.1,c.2.2)
def buchiSize (c : Config) := (EncodedThreadNumbering.codes (base c)).length
def size (c : Config) := EncodedPitermanAutomaton.size (buchiSize c)
def initial (c : Config) := EncodedPitermanAutomaton.locate (buchiSize c)
  (some (EncodedPitermanAutomaton.initialCode (buchiSize c) (EncodedThreadNumbering.name (base c) (c.2.1,none))))
def next (x : Config × EncodedThreadBuchi.Edges × Nat) :=
  EncodedPitermanAutomaton.next (buchiSize x.1,EncodedThreadNumbering.edges (base x.1) x.2.1,
    EncodedThreadNumbering.accepting (base x.1)) x.2.2
def priority (c : Config) (q : Nat) := EncodedPitermanAutomaton.priority (buchiSize c) q + 1

theorem base_primrec : Primrec base := Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
theorem buchiSize_primrec : Primrec buchiSize :=
  Primrec.list_length.comp (EncodedThreadNumbering.codes_primrec.comp base_primrec)
theorem size_primrec : Primrec size := EncodedPitermanAutomaton.size_primrec.comp buchiSize_primrec
theorem initial_primrec : Primrec initial :=
  EncodedPitermanAutomaton.locate_primrec.comp buchiSize_primrec
    (Primrec.option_some.comp (EncodedPitermanAutomaton.initialCode_primrec.comp buchiSize_primrec
      (EncodedThreadNumbering.name_primrec.comp base_primrec
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.const none)))))
theorem next_primrec : Primrec next :=
  EncodedPitermanAutomaton.next_primrec.comp
    ((buchiSize_primrec.comp Primrec.fst).pair
      ((EncodedThreadNumbering.edges_primrec.comp (base_primrec.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
        (EncodedThreadNumbering.accepting_primrec.comp (base_primrec.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.snd)
theorem priority_primrec : Primrec₂ priority :=
  Primrec.succ.comp (EncodedPitermanAutomaton.priority_primrec.comp (buchiSize_primrec.comp Primrec.fst) Primrec.snd)

def automaton {L : Type*} (c : Config) (edges : L → EncodedThreadBuchi.Edges) : DetParityAutomaton L :=
  (EncodedPitermanAutomaton.automaton (EncodedThreadNumbering.name (base c) (c.2.1,none))
    (fun a => EncodedThreadNumbering.edges (base c) (edges a))
    (EncodedThreadNumbering.accepting (base c)) (buchiSize c)).shiftPriority 1

theorem initial_val {L : Type*} (c : Config) (edges : L → EncodedThreadBuchi.Edges) :
    (automaton c edges).initial.val = initial c := rfl
theorem next_val {L : Type*} (c : Config) (edges : L → EncodedThreadBuchi.Edges)
    (q : (automaton c edges).State) (a : L) :
    ((automaton c edges).step q a).val = next (c,edges a,q.val) := rfl
theorem priority_val {L : Type*} (c : Config) (edges : L → EncodedThreadBuchi.Edges)
    (q : (automaton c edges).State) : (automaton c edges).priority q = priority c q.val := rfl

section Semantic
variable {RIn SIn ROut SOut L : Type*} (M : BlockRecordMonitor RIn SIn ROut SOut)
  [Fintype RIn] [DecidableEq M.State]
  (num : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (num q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ ThreadComputable.priorityRange M)
  (es : L → EncodedThreadBuchi.Edges) (letter : L → BlockRecordMonitor.ThreadLetter M)
  (he : ∀ q a r, ((num q).val,(num r).val) ∈ es a ↔
    ∃ i : RIn, r = M.step q (narrowedRecord M (letter a).1 q (i,(letter a).2)))

include hp hr he in
theorem accepts_iff_not_bad (word : OmegaWord L) :
    (automaton (Fintype.card M.State,(num M.initial).val,ps) es).Accepts word ↔
      ¬ (ThreadComputable.buchi M).Accepts (OmegaWord.map letter word) := by
  let B : NondetBuchiAutomaton L :=
    { State := ThreadComputable.GuessState M
      stateFinite := inferInstance
      initial := (M.initial,none)
      step := fun q a r => (ThreadComputable.buchi M).step q (letter a) r
      accepting := (ThreadComputable.buchi M).accepting }
  letI : DecidableEq B.State := inferInstanceAs (DecidableEq (ThreadComputable.GuessState M))
  let number := EncodedThreadNumbering.number M num ps hr
  have h := EncodedPitermanAutomaton.accepts_iff B number
    (fun q a r => ThreadComputable.stepDecidable M q (letter a) r)
    (ThreadComputable.acceptingDecidable M)
    (fun a => EncodedThreadNumbering.edges (Fintype.card M.State,ps) (es a))
    (EncodedThreadNumbering.accepting (Fintype.card M.State,ps))
    (fun q a r => EncodedThreadNumbering.edges_correct M num ps hp hr (es a) (letter a) (he · a ·) q r)
    (EncodedThreadNumbering.accepting_correct M num ps hp hr) word
  have hb : B.Accepts word ↔ (ThreadComputable.buchi M).Accepts (OmegaWord.map letter word) := by
    constructor <;> rintro ⟨run,hacc⟩ <;> exact ⟨⟨run.path,run.initial_state,run.step_valid⟩,hacc⟩
  rw [automaton,DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts]
  apply not_congr
  dsimp only [base,buchiSize]
  rw [← EncodedThreadNumbering.card_eq M num ps hr]
  exact h.trans hb

include hp hr he in
theorem accepts_iff (word : OmegaWord L) :
    (automaton (Fintype.card M.State,(num M.initial).val,ps) es).Accepts word ↔
      ∀ q : Nat → M.State, M.IsThread (OmegaWord.map letter word) q →
        NatSeqMinEvenParity (fun n => M.priority (q n)) := by
  rw [accepts_iff_not_bad M num ps hp hr es letter he,
    ThreadComputable.accepts_iff,BlockRecordMonitor.threadBuchi_accepts_iff]
  constructor
  · intro hnot q hthread
    rcases natSeqMinEvenParity_or_minOddParity (fun n => M.priority (q n))
      (BlockRecordMonitor.priority_range_finite M q) with hgood | hbad
    · exact hgood
    · exact absurd ⟨q,hthread,hbad⟩ hnot
  · rintro hall ⟨q,hq,hbad⟩
    exact not_natSeqMinEvenParity_and_natSeqMinOddParity _ ⟨hall q hq,hbad⟩
end Semantic
end DistributedSynthesis.EncodedThreadStream
