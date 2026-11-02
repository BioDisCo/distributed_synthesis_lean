/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedThreadBuchi
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Automata.EncodedPitermanCompiler

/-! # Duplicate-safe numbering of the bad-thread Büchi tables -/
namespace DistributedSynthesis.EncodedThreadNumbering
open EncodedThreadBuchi
abbrev Context := Nat × List Nat

def codes (x : Context) := FiniteCodeNumbering.unique (states x.1 x.2)
def name (x : Context) (s : State) := FiniteCodeNumbering.name (states x.1 x.2) s
def accepting (x : Context) := (acceptingStates x.1 x.2).map (name x)
def edges (x : Context) (es : Edges) :=
  (EncodedThreadBuchi.edges x.1 (x.2,es)).map (fun e => (name x e.1,name x e.2))
def compile (x : Input) : EncodedPitermanCompiler.Input :=
  ((codes (x.1,x.2.2.1)).length, name (x.1,x.2.2.1) (x.2.1,none),
    accepting (x.1,x.2.2.1), x.2.2.2.map (edges (x.1,x.2.2.1)))

theorem codes_primrec : Primrec codes := FiniteCodeNumbering.unique_primrec.comp states_primrec
theorem name_primrec : Primrec₂ name := by
  have hs : Primrec (fun x : Context × State => states x.1.1 x.1.2) :=
    states_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact FiniteCodeNumbering.name_primrec.comp hs Primrec.snd
theorem accepting_primrec : Primrec accepting :=
  Primrec.list_map acceptingStates_primrec name_primrec
theorem edges_primrec : Primrec₂ edges :=
  Primrec.list_map (EncodedThreadBuchi.edges_primrec.comp (Primrec.fst.comp Primrec.fst)
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    ((name_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (name_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
theorem compile_primrec : Primrec compile := by
  have hc : Primrec (fun x : Input => (x.1,x.2.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_length.comp (codes_primrec.comp hc)).pair
    ((name_primrec.comp hc ((Primrec.fst.comp Primrec.snd).pair (Primrec.const none))).pair
      ((accepting_primrec.comp hc).pair
        (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (edges_primrec.comp (hc.comp Primrec.fst) Primrec.snd).to₂)))

theorem alphabet_size (x : Input) : (compile x).2.2.2.length = x.2.2.2.length := by
  simp only [compile,List.length_map]

end DistributedSynthesis.EncodedThreadNumbering
