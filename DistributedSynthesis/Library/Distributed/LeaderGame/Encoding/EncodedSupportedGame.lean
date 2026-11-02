/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Automata.EncodedParityTables
import DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness

/-! Numeric compilation of supported public games to the existing parity-tree
solver format. Data contain finite offer and legality tables and a numeric
progress objective. Legality is checked before support can be lost. -/
namespace Characterisation.EncodedSupportedGame
open DistributedSynthesis

/-- Maximum observation index, move count, progress automaton, initial
observation, move-major offers, and observation-major legality. -/
abbrev Data := Nat × Nat × EncodedParityTables.Data × Nat × List Bool × List Bool
abbrev State := Nat × Nat × Bool × Bool

def observations (d : Data) := d.1+1
def moves (d : Data) := d.2.1
def progress (d : Data) := d.2.2.1
def first (d : Data) := d.2.2.2.1
def offers (d : Data) := d.2.2.2.2.1
def legal (d : Data) := d.2.2.2.2.2

def offered (d : Data) (l b : Nat) := (offers d).getD (l*observations d+b) false
def allowed (d : Data) (b l : Nat) := (legal d).getD (b*moves d+l) false

def rawStates (d : Data) : List State :=
  (List.range (observations d)).product
    ((List.range (EncodedParityTables.size (progress d))).product
      ([false,true].product [false,true]))
@[irreducible] def states (d : Data) := FiniteCodeNumbering.unique (rawStates d)
def name (d : Data) (s : State) := FiniteCodeNumbering.name (rawStates d) s

def step (d : Data) (s : State) (l b : Nat) : State :=
  (b,EncodedParityTables.next (progress d) s.2.1 (l*observations d+b),
    s.2.2.1 && offered d l b, s.2.2.2 && (!s.2.2.1 || allowed d s.1 l))
def priority (d : Data) (s : State) :=
  if s.2.2.2 then (if s.2.2.1 then EncodedParityTables.priority (progress d) s.2.1+2 else 0) else 1
def initial (d : Data) : State :=
  (first d % observations d,EncodedParityTables.initial (progress d) % EncodedParityTables.size (progress d),true,true)

def transitions (d : Data) := (states d).flatMap (fun s => (List.range (moves d)).flatMap
  (fun l => (List.range (observations d)).map (fun b => name d (step d s l b))))
def compile (d : Data) : EncodedTreeNonemptiness.Data :=
  ((states d).length-1,moves d,observations d,transitions d,(states d).map (priority d),name d (initial d))

theorem observations_primrec : Primrec observations := Primrec.succ.comp Primrec.fst
theorem moves_primrec : Primrec moves := Primrec.fst.comp Primrec.snd
theorem progress_primrec : Primrec progress := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem first_primrec : Primrec first := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem offers_primrec : Primrec offers := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem legal_primrec : Primrec legal := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem rawStates_primrec : Primrec rawStates := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp observations_primrec)
  (FiniteSearch.product_primrec.comp (Primrec.list_range.comp (EncodedParityTables.size_primrec.comp progress_primrec))
    (Primrec.const ([false,true].product [false,true])))
theorem states_primrec : Primrec states := by
  unfold states
  exact FiniteCodeNumbering.unique_primrec.comp rawStates_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp (rawStates_primrec.comp Primrec.fst) Primrec.snd

section Composition
variable {X : Type*} [Primcodable X] {d : X → Data} {s : X → State} {l b : X → Nat}
theorem offered_comp (hd : Primrec d) (hl : Primrec l) (hb : Primrec b) :
    Primrec (fun x => offered (d x) (l x) (b x)) :=
  (Primrec.list_getD false).comp (offers_primrec.comp hd)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hl (observations_primrec.comp hd)) hb)
theorem allowed_comp (hd : Primrec d) (hb : Primrec b) (hl : Primrec l) :
    Primrec (fun x => allowed (d x) (b x) (l x)) :=
  (Primrec.list_getD false).comp (legal_primrec.comp hd)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hb (moves_primrec.comp hd)) hl)
theorem step_comp (hd : Primrec d) (hs : Primrec s) (hl : Primrec l) (hb : Primrec b) :
    Primrec (fun x => step (d x) (s x) (l x) (b x)) := by
  have hq := Primrec.fst.comp (Primrec.snd.comp hs)
  have support := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have valid := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  exact hb.pair ((EncodedParityTables.next_primrec.comp
    ((progress_primrec.comp hd).pair (hq.pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hl (observations_primrec.comp hd)) hb)))).pair
    (((Primrec.dom_bool₂ Bool.and).comp support (offered_comp hd hl hb)).pair
      ((Primrec.dom_bool₂ Bool.and).comp valid ((Primrec.dom_bool₂ Bool.or).comp
        ((Primrec.dom_bool Bool.not).comp support) (allowed_comp hd (Primrec.fst.comp hs) hl)))))
theorem priority_comp (hd : Primrec d) (hs : Primrec s) :
    Primrec (fun x => priority (d x) (s x)) :=
  Primrec.ite (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs))) (Primrec.const true))
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))) (Primrec.const true))
      (Primrec.nat_add.comp (EncodedParityTables.priority_primrec.comp (progress_primrec.comp hd)
        (Primrec.fst.comp (Primrec.snd.comp hs))) (Primrec.const 2)) (Primrec.const 0)) (Primrec.const 1)
end Composition

theorem initial_primrec : Primrec initial :=
  (Primrec.nat_mod.comp first_primrec observations_primrec).pair
    ((Primrec.nat_mod.comp (EncodedParityTables.initial_primrec.comp progress_primrec)
      (EncodedParityTables.size_primrec.comp progress_primrec)).pair ((Primrec.const true).pair (Primrec.const true)))
theorem transitions_primrec : Primrec transitions := by
  apply Primrec.list_flatMap states_primrec
  change Primrec (fun x : Data × State => (List.range (moves x.1)).flatMap
    (fun l => (List.range (observations x.1)).map (fun b => name x.1 (step x.1 x.2 l b))))
  apply Primrec.list_flatMap (Primrec.list_range.comp (moves_primrec.comp Primrec.fst))
  change Primrec (fun x : (Data × State) × Nat => (List.range (observations x.1.1)).map
    (fun b => name x.1.1 (step x.1.1 x.1.2 x.2 b)))
  apply Primrec.list_map (Primrec.list_range.comp (observations_primrec.comp (Primrec.fst.comp Primrec.fst)))
  have hd : Primrec (fun x : ((Data × State) × Nat) × Nat => x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  exact (name_primrec.comp hd (step_comp hd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
theorem compile_primrec : Primrec compile :=
  (Primrec.nat_sub.comp (Primrec.list_length.comp states_primrec) (Primrec.const 1)).pair
    (moves_primrec.pair (observations_primrec.pair (transitions_primrec.pair
      ((Primrec.list_map states_primrec (priority_comp Primrec.fst Primrec.snd).to₂).pair
        (name_primrec.comp Primrec.id initial_primrec)))))

end Characterisation.EncodedSupportedGame
