/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabet
import DistributedSynthesis.Library.Distributed.EncodedThreadCompiler

/-! Numeric generation of the persistent hidden-thread progress objective.
Live states retain a slot, its code minimum, and the literal priority-monitor
control. Invalid resolutions enter the same even sink as the semantic game.
The existing bad-thread compiler handles determinization and complementation. -/
namespace Characterisation.EncodedLeaderProgress
open DistributedSynthesis
open EncodedLeaderAlphabet (Context Outcome Move width maxPriority outcomeName)

abbrev State := Option (Nat × Nat × Nat)
abbrev Resolution := Nat × Nat
abbrev Letter := Move × Outcome
abbrev Input := Context × Resolution

def resolutions (c : Context) := (List.range (width c+1)).product (List.range (maxPriority c+1))
def rawStates (c : Context) : List State := none ::
  ((List.range (width c+1)).product ((List.range (maxPriority c+1)).product (List.range (maxPriority c+1)))).map some
@[irreducible] def states (c : Context) := FiniteCodeNumbering.unique (rawStates c)
def name (c : Context) (q : State) := FiniteCodeNumbering.name (rawStates c) q
def letters (c : Context) := (EncodedLeaderAlphabet.moves c).product (EncodedLeaderAlphabet.outcomes c)

def step (c : Context) (q : State) (a : Letter) (r : Resolution) : State := q.bind fun old =>
  if EncodedLeaderAlphabet.offered a.1 (outcomeName c a.2) &&
      EncodedLeaderAlphabet.edge a.2 (old.1,old.2.1) r then some (r.1,r.2,r.2) else none

def priority (q : State) := (q.map (fun s => s.2.2)).getD 0
def initial (x : Input) : State := some (x.2.1 % (width x.1+1),x.2.2 % (maxPriority x.1+1),0)

def row (c : Context) (a : Letter) : EncodedThreadBuchi.Edges :=
  (states c).flatMap (fun q => (resolutions c).map (fun r => (name c q,name c (step c q a r))))
def edgeRows (c : Context) := (letters c).map (row c)
def data (x : Input) : EncodedThreadBuchi.Input :=
  ((states x.1).length,name x.1 (initial x),(states x.1).map priority,edgeRows x.1)
def compile (x : Input) := EncodedThreadCompiler.compile (data x)

theorem resolutions_primrec : Primrec resolutions := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp (Primrec.succ.comp EncodedLeaderAlphabet.width_primrec))
  (Primrec.list_range.comp (Primrec.succ.comp EncodedLeaderAlphabet.maxPriority_primrec))
theorem rawStates_primrec : Primrec rawStates := Primrec.list_cons.comp (Primrec.const none)
  (Primrec.list_map (FiniteSearch.product_primrec.comp
    (Primrec.list_range.comp (Primrec.succ.comp EncodedLeaderAlphabet.width_primrec))
    (FiniteSearch.product_primrec.comp
      (Primrec.list_range.comp (Primrec.succ.comp EncodedLeaderAlphabet.maxPriority_primrec))
      (Primrec.list_range.comp (Primrec.succ.comp EncodedLeaderAlphabet.maxPriority_primrec))))
    (Primrec.option_some.comp Primrec.snd).to₂)
theorem states_primrec : Primrec states := by
  unfold states
  exact FiniteCodeNumbering.unique_primrec.comp rawStates_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp
  (rawStates_primrec.comp Primrec.fst) Primrec.snd
theorem letters_primrec : Primrec letters := FiniteSearch.product_primrec.comp
  EncodedLeaderAlphabet.moves_primrec EncodedLeaderAlphabet.outcomes_primrec

theorem step_comp {X : Type} [Primcodable X] {c : X → Context} {q : X → State}
    {a : X → Letter} {r : X → Resolution}
    (hc : Primrec c) (hq : Primrec q) (ha : Primrec a) (hr : Primrec r) :
    Primrec (fun x => step (c x) (q x) (a x) (r x)) := by
  apply Primrec.option_bind hq
  have hctx : Primrec (fun x : X × (Nat × Nat × Nat) => c x.1) := hc.comp Primrec.fst
  have hletter : Primrec (fun x : X × (Nat × Nat × Nat) => a x.1) := ha.comp Primrec.fst
  have hres : Primrec (fun x : X × (Nat × Nat × Nat) => r x.1) := hr.comp Primrec.fst
  have hfirst := Primrec.fst.comp hres
  have hsecond := Primrec.snd.comp hres
  have hoffers := EncodedLeaderAlphabet.offered_primrec.comp (Primrec.fst.comp hletter)
    (EncodedLeaderAlphabet.outcomeName_primrec.comp hctx (Primrec.snd.comp hletter))
  have hedge := EncodedLeaderAlphabet.edge_primrec.comp ((Primrec.snd.comp hletter).pair
    (((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair hres))
  exact (Primrec.ite (Primrec.eq.comp ((Primrec.dom_bool₂ Bool.and).comp hoffers hedge) (Primrec.const true))
    (Primrec.option_some.comp (hfirst.pair (hsecond.pair hsecond))) (Primrec.const none)).to₂

theorem priority_primrec : Primrec priority := Primrec.option_getD.comp
  (Primrec.option_map Primrec.id (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂) (Primrec.const 0)
theorem initial_primrec : Primrec initial := Primrec.option_some.comp
  ((Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.succ.comp (EncodedLeaderAlphabet.width_primrec.comp Primrec.fst))).pair
  ((Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd)
    (Primrec.succ.comp (EncodedLeaderAlphabet.maxPriority_primrec.comp Primrec.fst))).pair (Primrec.const 0)))

theorem row_primrec : Primrec₂ row := by
  apply Primrec.list_flatMap (states_primrec.comp Primrec.fst)
  change Primrec (fun x : (Context × Letter) × State => (resolutions x.1.1).map
    (fun r => (name x.1.1 x.2,name x.1.1 (step x.1.1 x.2 x.1.2 r))))
  apply Primrec.list_map (resolutions_primrec.comp (Primrec.fst.comp Primrec.fst))
  have hc : Primrec (fun x : ((Context × Letter) × State) × Resolution => x.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun x : ((Context × Letter) × State) × Resolution => x.1.2) := Primrec.snd.comp Primrec.fst
  exact ((name_primrec.comp hc hq).pair
    (name_primrec.comp hc (step_comp hc hq (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))).to₂

theorem edgeRows_primrec : Primrec edgeRows := Primrec.list_map letters_primrec row_primrec
theorem data_primrec : Primrec data :=
  (Primrec.list_length.comp (states_primrec.comp Primrec.fst)).pair
    ((name_primrec.comp Primrec.fst initial_primrec).pair
      ((Primrec.list_map (states_primrec.comp Primrec.fst) (priority_primrec.comp Primrec.snd).to₂).pair
        (edgeRows_primrec.comp Primrec.fst)))
theorem compile_primrec : Primrec compile := EncodedThreadCompiler.compile_primrec.comp data_primrec

end Characterisation.EncodedLeaderProgress
