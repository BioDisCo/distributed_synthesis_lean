/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLNumbering

/-! # Complete primitive-recursive LTL-to-parity tables

The input is a postfix formula and a finite list of valuations. Each position
in that list is a letter, even when valuations repeat. The output consists
only of natural numbers and finite lists; its language is exactly the decoded
formula under those valuations.
-/

namespace DistributedSynthesis.EncodedLTLParity
variable {A : Type*} [DecidableEq A]
abbrev Input (A : Type*) := EncodedFiniteLTL.Code A × List (List A)

def compile (x : Input A) : EncodedParityTables.Data :=
  EncodedPitermanCompiler.compile (EncodedLTLNumbering.compile x)
theorem compile_primrec [Primcodable A] : Primrec (compile (A := A)) :=
  EncodedPitermanCompiler.compile_primrec.comp EncodedLTLNumbering.compile_primrec

def symbolic (c : EncodedFiniteLTL.Code A) : DetParityAutomaton (List A) :=
  EncodedPitermanAutomaton.automaton
    (EncodedLTLNumbering.name c EncodedLTLBreakpoints.initial)
    (fun a => EncodedLTLNumbering.edges (c, a)) (EncodedLTLNumbering.accepting c)
    (EncodedLTLBreakpoints.stateCodes c).length

theorem symbolic_accepts_iff (c : EncodedFiniteLTL.Code A) (word : OmegaWord (List A)) :
    (symbolic c).Accepts word ↔
      LTL.Satisfies EncodedLTLAutomaton.interp word (EncodedFiniteLTL.decode c) := by
  let B := EncodedLTLBreakpoints.buchi c
  letI := EncodedLTLNumbering.stateDecidableEq c
  let ds : ∀ q a r, Decidable (B.step q a r) := fun q a r =>
    inferInstanceAs (Decidable (EncodedLTLBreakpoints.transition ((c, a), q.val, r.val)))
  let da : DecidablePred B.accepting := fun q =>
    inferInstanceAs (Decidable (EncodedLTLBreakpoints.accepting c q.val))
  have h := EncodedPitermanAutomaton.accepts_iff B (EncodedLTLNumbering.number c) ds da
    (fun a => EncodedLTLNumbering.edges (c, a)) (EncodedLTLNumbering.accepting c)
    (fun q a r => EncodedLTLNumbering.edges_correct c a q r)
    (EncodedLTLNumbering.accepting_correct c) word
  rw [EncodedLTLNumbering.number_val, EncodedLTLNumbering.card_eq] at h
  exact h.trans (EncodedLTLBreakpoints.accepts_iff c word)

theorem alphabet_size (x : Input A) : (EncodedParityTables.rows (compile x)).length = x.2.length := by
  rw [compile, EncodedPitermanCompiler.alphabet_size]
  simp [EncodedLTLNumbering.compile]

def automaton (x : Input A) : DetParityAutomaton (Fin x.2.length) :=
  (EncodedParityTables.automaton (compile x)).comap (Fin.cast (alphabet_size x).symm)

private theorem cast_comap {n m k : Nat} (D : DetParityAutomaton (Fin n))
    (h : n = m) (h' : m = k) :
    (D.comap (Fin.cast h.symm)).comap (Fin.cast h'.symm) =
      D.comap (Fin.cast (h.trans h').symm) := by
  cases h
  cases h'
  rfl

private theorem raw_comap {L K : Type*} (n initial : Nat)
    (edges : L → EncodedPitermanTransition.Edges) (acc : List Nat) (f : K → L) :
    (EncodedPitermanAutomaton.automaton initial edges acc n).comap f =
      EncodedPitermanAutomaton.automaton initial (fun a => edges (f a)) acc n := rfl

set_option maxHeartbeats 800000 in
theorem automaton_eq (x : Input A) :
    automaton x = (symbolic x.1).comap (fun a : Fin x.2.length => x.2[a]) := by
  have h := EncodedPitermanCompiler.automaton_eq (EncodedLTLNumbering.compile x)
  have hlen : (EncodedLTLNumbering.compile x).2.2.2.length = x.2.length := by
    simp [EncodedLTLNumbering.compile]
  have hl : automaton x = (EncodedPitermanCompiler.automaton (EncodedLTLNumbering.compile x)).comap
      (Fin.cast hlen.symm) := by
    unfold automaton compile EncodedPitermanCompiler.automaton
    exact (cast_comap _ (EncodedPitermanCompiler.alphabet_size (EncodedLTLNumbering.compile x)) hlen).symm
  rw [hl, h]
  unfold symbolic
  rw [raw_comap, raw_comap]
  dsimp only [EncodedLTLNumbering.compile]
  apply congrArg (fun edges => EncodedPitermanAutomaton.automaton
    (EncodedLTLNumbering.name x.1 EncodedLTLBreakpoints.initial) edges
    (EncodedLTLNumbering.accepting x.1) (EncodedLTLBreakpoints.stateCodes x.1).length)
  funext a
  change (x.2.map (fun a => EncodedLTLNumbering.edges (x.1, a)))[a.val] = _
  exact List.getElem_map _

theorem accepts_iff (x : Input A) (word : OmegaWord (Fin x.2.length)) :
    (automaton x).Accepts word ↔
      LTL.Satisfies EncodedLTLAutomaton.interp (fun t => x.2[word t])
        (EncodedFiniteLTL.decode x.1) := by
  rw [automaton_eq, DetParityAutomaton.comap_accepts_iff]
  exact symbolic_accepts_iff x.1 _

end DistributedSynthesis.EncodedLTLParity
