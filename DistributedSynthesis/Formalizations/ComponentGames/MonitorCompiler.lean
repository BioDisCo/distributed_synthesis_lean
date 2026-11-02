/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.Objective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgressCorrect
import Mathlib.Data.List.Sublists

namespace Characterisation.ComponentGames.MonitorCompiler
open DistributedSynthesis Characterisation
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

def triples (B K : Nat) : List (Fin (B+1) × Fin (K+1) × Fin (B+1)) :=
  (List.finRange (B+1)).product ((List.finRange (K+1)).product (List.finRange (B+1)))

theorem triples_complete (B K : Nat) (t : Fin (B+1) × Fin (K+1) × Fin (B+1)) : t ∈ triples B K := by
  rcases t with ⟨h,c,t⟩
  simp [triples]

/-- Enumerate the full ternary-relation alphabet, retaining differently
colored edges with the same source and target. -/
def letters (B K : Nat) : List (TransitionAlphabet B K) :=
  ((triples B K).sublists).map List.toFinset

theorem letters_complete {B K : Nat} (T : TransitionAlphabet B K) : T ∈ letters B K := by
  apply List.mem_map.mpr
  refine ⟨(triples B K).filter (fun t => t ∈ T),List.mem_sublists.mpr List.filter_sublist,?_⟩
  ext t
  simp [triples_complete]

def rawTriple {B K : Nat} (t : Fin (B+1) × Fin (K+1) × Fin (B+1)) : Nat × Nat × Nat :=
  (t.1.val,t.2.1.val,t.2.2.val)

theorem rawTriple_injective {B K : Nat} : Function.Injective (@rawTriple B K) := by
  intro a b eq
  exact Prod.ext (Fin.ext (congrArg (fun x => x.1) eq))
    (Prod.ext (Fin.ext (congrArg (fun x => x.2.1) eq)) (Fin.ext (congrArg (fun x => x.2.2) eq)))

def rawRelation {B K : Nat} (T : TransitionAlphabet B K) : Finset (Nat × Nat × Nat) := T.image rawTriple

theorem rawRelation_mem {B K : Nat} (T : TransitionAlphabet B K)
    (t : Fin (B+1) × Fin (K+1) × Fin (B+1)) : rawTriple t ∈ rawRelation T ↔ t ∈ T := by
  constructor
  · rintro member
    obtain ⟨s,inside,eq⟩ := Finset.mem_image.mp member
    exact (rawTriple_injective eq) ▸ inside
  · intro member
    exact Finset.mem_image.mpr ⟨t,member,rfl⟩

def step {B K : Nat} (q : EncodedLeaderProgress.State) (T : TransitionAlphabet B K) (r : EncodedLeaderProgress.Resolution) : EncodedLeaderProgress.State :=
  q.bind (fun old => if (old.1,r.2,r.1) ∈ rawRelation T then some (r.1,r.2,r.2) else none)

def row {B K : Nat} (T : TransitionAlphabet B K) : EncodedThreadBuchi.Edges :=
  (EncodedLeaderProgress.states (B,0,K)).flatMap (fun q => (EncodedLeaderProgress.resolutions (B,0,K)).map
    (fun r => (EncodedLeaderProgress.name (B,0,K) q,EncodedLeaderProgress.name (B,0,K) (step q T r))))

def rows (B K : Nat) : List EncodedThreadBuchi.Edges := (letters B K).map row

def data {B K : Nat} (initial : Fin (B+1)) : EncodedThreadBuchi.Input :=
  ((EncodedLeaderProgress.states (B,0,K)).length,EncodedLeaderProgress.name (B,0,K) (some (initial.val,0,0)),
    (EncodedLeaderProgress.states (B,0,K)).map EncodedLeaderProgress.priority,rows B K)

/-- All tables are executable. The established library performs bad-run
Buchi compilation, Piterman determinization, and complementation. -/
def compile {B K : Nat} (initial : Fin (B+1)) : EncodedParityTables.Data :=
  EncodedThreadCompiler.compile (data (K:=K) initial)

variable {B K : Nat} (initial : Fin (B+1))
noncomputable def source : FiniteThreadSystem (TransitionAlphabet B K × Unit) :=
  hiddenCodeContinuitySystem (handoverPriorityDPA B K) (initial,0) relationEdge

theorem step_encode (q : EncodedLeaderProgress.SemanticState B K) (T : TransitionAlphabet B K) (r : HandoverCode B K) :
    step (EncodedLeaderProgress.encode q) T (r.1.val,r.2.val) = EncodedLeaderProgress.encode ((source initial).step q (T,()) r) := by
  cases q with
  | dead => rfl
  | live code control =>
    have membership : (code.1.val,r.2.val,r.1.val) ∈ rawRelation T ↔ relationEdge code T () r :=
      rawRelation_mem T (code.1,r.2,r.1)
    by_cases edge : relationEdge code T () r
    · rw [show (source initial).step (.live code control) (T,()) r =
          .live r ((handoverPriorityDPA B K).step control r) from
        hiddenCodeContinuitySystem_step_live_of _ _ _ _ _ _ _ edge]
      simp only [step,EncodedLeaderProgress.encode,Option.bind_some,if_pos (membership.mpr edge)]
      rfl
    · rw [show (source initial).step (.live code control) (T,()) r = .dead from
        hiddenCodeContinuitySystem_step_live_dead_of _ _ _ _ _ _ _ edge]
      simp only [step,EncodedLeaderProgress.encode,Option.bind_some,if_neg (fun h => edge (membership.mp h))]

theorem row_correct (q r : EncodedLeaderProgress.SemanticState B K) (T : TransitionAlphabet B K) :
    ((EncodedLeaderProgress.stateNumber B 0 K q).val,(EncodedLeaderProgress.stateNumber B 0 K r).val) ∈ row T ↔
      ∃ resolution : HandoverCode B K, r = (source initial).step q (T,()) resolution := by
  simp only [EncodedLeaderProgress.stateNumber_val,row,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨old,hold,res,hres,equal⟩
    have raw : old ∈ EncodedLeaderProgress.rawStates (B,0,K) := by
      apply (FiniteCodeNumbering.mem_unique _ _).mp
      simpa only [EncodedLeaderProgress.states] using hold
    obtain ⟨s,es⟩ := EncodedLeaderProgress.codes_sound B 0 K old raw
    subst old
    have same : s=q := EncodedLeaderProgress.encode_injective (FiniteCodeNumbering.name_injective _ (EncodedLeaderProgress.encode_mem B 0 K s)
      (EncodedLeaderProgress.encode_mem B 0 K q) (congrArg Prod.fst equal))
    subst s
    obtain ⟨hi,hj⟩ := List.mem_product.mp hres
    let resolution : HandoverCode B K := (⟨res.1,List.mem_range.mp hi⟩,⟨res.2,List.mem_range.mp hj⟩)
    have target := congrArg Prod.snd equal
    change EncodedLeaderProgress.name (B,0,K) (step (EncodedLeaderProgress.encode q) T (resolution.1.val,resolution.2.val)) = EncodedLeaderProgress.name (B,0,K) (EncodedLeaderProgress.encode r) at target
    rw [step_encode initial] at target
    exact ⟨resolution,(EncodedLeaderProgress.encode_injective (FiniteCodeNumbering.name_injective _
      (EncodedLeaderProgress.encode_mem B 0 K _) (EncodedLeaderProgress.encode_mem B 0 K r) target)).symm⟩
  · rintro ⟨resolution,rfl⟩
    refine ⟨EncodedLeaderProgress.encode q,?_,(resolution.1.val,resolution.2.val),?_,?_⟩
    · rw [EncodedLeaderProgress.states,FiniteCodeNumbering.mem_unique]
      exact EncodedLeaderProgress.encode_mem B 0 K q
    · exact List.mem_product.mpr ⟨List.mem_range.mpr resolution.1.isLt,List.mem_range.mpr resolution.2.isLt⟩
    · exact Prod.ext rfl (congrArg (EncodedLeaderProgress.name (B,0,K)) (step_encode initial q T resolution))

def decode (i : Fin (rows B K).length) : TransitionAlphabet B K :=
  (letters B K)[i.val]'(by simpa only [rows,List.length_map] using i.isLt)

def index (T : TransitionAlphabet B K) : Fin (rows B K).length :=
  ⟨(letters B K).idxOf T,by simpa only [rows,List.length_map] using List.idxOf_lt_length_iff.mpr (letters_complete T)⟩

theorem decode_index (T : TransitionAlphabet B K) : decode (index T) = T :=
  List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (letters_complete T))

theorem rows_correct (q r : EncodedLeaderProgress.SemanticState B K) (a : Fin (rows B K).length) :
    ((EncodedLeaderProgress.stateNumber B 0 K q).val,(EncodedLeaderProgress.stateNumber B 0 K r).val) ∈ (rows B K)[a.val]?.getD [] ↔
      ∃ resolution : HandoverCode B K, r = (source initial).step q (decode a,()) resolution := by
  rw [List.getElem?_eq_getElem a.isLt]
  change _ ∈ (rows B K)[a.val] ↔ _
  simp only [rows,List.getElem_map]
  exact row_correct initial q r (decode a)

def automaton : DetParityAutomaton (TransitionAlphabet B K) :=
  (EncodedThreadCompiler.automaton (data (K:=K) initial)).comap index

theorem accepts_iff_paper (word : OmegaWord (TransitionAlphabet B K)) :
    (automaton initial).Accepts word ↔ (paperMonitor initial).Accepts word := by
  classical
  letI : Fintype (source (K:=K) initial).Resolution := inferInstanceAs (Fintype (HandoverCode B K))
  letI : DecidableEq (source (K:=K) initial).State := Classical.typeDecidableEq _
  let ps := (EncodedLeaderProgress.states (B,0,K)).map EncodedLeaderProgress.priority
  let es := rows B K
  let numericWord : OmegaWord (Fin es.length) := OmegaWord.map index word
  have priority : ∀ q, ps.getD (EncodedLeaderProgress.stateNumber B 0 K q).val 0 = (source (K:=K) initial).priority q :=
    EncodedLeaderProgress.priority_lookup (Q:=Unit) (N:=0) (initial,0)
  have range : ∀ p, p ∈ ps ↔ p ∈ (source (K:=K) initial).priorityRange :=
    EncodedLeaderProgress.priority_range (Q:=Unit) (N:=0) (initial,0)
  have correct := EncodedFiniteThreads.accepts_iff (source (K:=K) initial) (EncodedLeaderProgress.stateNumber B 0 K) ps
    priority range es (fun a => (decode a,())) (fun q a r => rows_correct initial q r a) numericWord
  have decoded : OmegaWord.map (fun a => (decode a,())) numericWord = OmegaWord.map (fun T => (T,())) word := by
    funext n
    exact Prod.ext (decode_index (word n)) rfl
  rw [decoded] at correct
  have initialName : EncodedLeaderProgress.name (B,0,K) (some (initial.val,0,0)) =
      (EncodedLeaderProgress.stateNumber B 0 K (source (K:=K) initial).initial).val := by
    rw [EncodedLeaderProgress.stateNumber_val]
    rfl
  have same := EncodedThreadCompiler.config_accepts_congr ps es (EncodedLeaderProgress.card_eq B 0 K).symm
    initialName numericWord
  rw [automaton,DetParityAutomaton.comap_accepts_iff,paperMonitor,DetParityAutomaton.comap_accepts_iff]
  exact same.trans correct

/-- Full effective version of the paper's monitor lemma, for all relation
words and all compatible histories/priorities. -/
theorem bounded_parity_monitor_effective (word : OmegaWord (TransitionAlphabet B K)) :
    (automaton initial).Accepts word ↔
      ∀ (h : Nat → Fin (B+1)) (c : Nat → Fin (K+1)), h 0 = initial →
        (∀ n, (h n,c n,h (n+1)) ∈ word n) →
        NatSeqMinEvenParity (fun n => (c n).val) :=
  (accepts_iff_paper initial word).trans (bounded_parity_monitor initial word)

/-- The effective semantic automaton is exactly the generated numeric
parity table, with the computable relation-letter index map. -/
theorem automaton_eq_numeric : automaton (K:=K) initial =
    (EncodedParityTables.automaton (compile (K:=K) initial)).comap
      (fun T => Fin.cast (EncodedThreadCompiler.alphabet_size (data (K:=K) initial)).symm (index T)) := by
  rw [automaton,EncodedThreadCompiler.automaton_eq]
  rfl

end Characterisation.ComponentGames.MonitorCompiler
