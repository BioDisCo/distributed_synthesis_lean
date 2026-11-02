/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolver
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgress
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedSupportedGameCorrect

/-! Generate all public offers, legal moves, and persistent-thread progress
from the original graph context and the checked raw-header local tests. -/
namespace Characterisation.EncodedPublicLeaderGame
open DistributedSynthesis
attribute [local irreducible] Primrec
abbrev Data := EncodedHeaderCompiler.GraphData × List Bool × EncodedRoundObjectives.Data × EncodedLeaderAlphabet.Outcome × (Nat × Nat)
local instance publicGameDataCode : Primcodable Data := inferInstance
local instance publicGameOutcomeEq : DecidableEq EncodedLeaderAlphabet.Outcome := inferInstance
local instance publicGameLetterEq : DecidableEq EncodedLeaderProgress.Letter := inferInstance
local instance publicGameLetterBEq : BEq EncodedLeaderProgress.Letter := instBEqOfDecidableEq

def graphData (d : Data) := d.1
def leaders (d : Data) := d.2.1
def objective (d : Data) := d.2.2.1
def initial (d : Data) := d.2.2.2.1
def initialCode (d : Data) := d.2.2.2.2
def context (d : Data) : EncodedLeaderAlphabet.Context :=
  ((graphData d).2.2.2.2.2,(graphData d).1.1 * EncodedRoundObjectives.stateCount (objective d) *
    (EncodedLeaderObjective.priorityBound (objective d)+1),EncodedLeaderObjective.priorityBound (objective d))
def outcomes (d : Data) := EncodedLeaderAlphabet.outcomes (context d)
def moves (d : Data) := EncodedLeaderAlphabet.moves (context d)
def selected (d : Data) (m : EncodedLeaderAlphabet.Move) :=
  (outcomes d).filter (fun b => EncodedLeaderAlphabet.offered m (EncodedLeaderAlphabet.outcomeName (context d) b))
def graphOf (d : Data) (q : Nat) := q / (EncodedLeaderObjective.priorityBound (objective d)+1) /
  EncodedRoundObjectives.stateCount (objective d)
def agrees (d : Data) (h : EncodedLeaderAlphabet.Header) (m : EncodedLeaderAlphabet.Move) :=
  decide (∀ q ∈ h.2.2.2, (leaders d).getD (graphOf d q) false = m.1)
def legal (d : Data) (h : EncodedLeaderAlphabet.Header) (m : EncodedLeaderAlphabet.Move) :=
  agrees d h m && EncodedHeaderCompiler.test (graphData d,objective d,h,selected d m) (!m.1)
def offerTable (d : Data) := (moves d).flatMap (fun m => (outcomes d).map
  (fun b => EncodedLeaderAlphabet.offered m (EncodedLeaderAlphabet.outcomeName (context d) b)))
def legalTable (d : Data) := (outcomes d).flatMap (fun b => (moves d).map (legal d b.1))
def progressBase (d : Data) := EncodedLeaderProgress.compile (context d,initialCode d)
/-- Reindex explicitly by the shared public-letter codes. -/
def progressRows (d : Data) := (moves d).flatMap (fun m => (outcomes d).map
  (fun b => (EncodedParityTables.rows (progressBase d)).getD
    ((EncodedLeaderProgress.letters (context d)).idxOf (m,b)) []))
def progress (d : Data) : EncodedParityTables.Data :=
  ((progressBase d).1,EncodedParityTables.initial (progressBase d),
    EncodedParityTables.priorities (progressBase d),progressRows d)
def compile (d : Data) : EncodedSupportedGame.Data :=
  ((outcomes d).length-1,(moves d).length,progress d,
    EncodedLeaderAlphabet.outcomeName (context d) (initial d),offerTable d,legalTable d)
def solve (d : Data) := EncodedSupportedGame.solve (compile d)

theorem graphData_primrec : Primrec graphData := Primrec.fst
theorem leaders_primrec : Primrec leaders := Primrec.fst.comp Primrec.snd
theorem objective_primrec : Primrec objective := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem initial_primrec : Primrec initial := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem initialCode_primrec : Primrec initialCode := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem context_primrec : Primrec context :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp graphData_primrec))))).pair
    ((Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.fst.comp graphData_primrec))
        (EncodedRoundObjectives.stateCount_primrec.comp objective_primrec))
      (Primrec.succ.comp (EncodedLeaderObjective.priorityBound_primrec.comp objective_primrec))).pair
      (EncodedLeaderObjective.priorityBound_primrec.comp objective_primrec))
theorem outcomes_primrec : Primrec outcomes := EncodedLeaderAlphabet.outcomes_primrec.comp context_primrec
theorem moves_primrec : Primrec moves := EncodedLeaderAlphabet.moves_primrec.comp context_primrec
theorem selected_primrec : Primrec₂ selected := by
  have p : PrimrecRel (fun (x : Data × EncodedLeaderAlphabet.Move) b =>
      EncodedLeaderAlphabet.offered x.2 (EncodedLeaderAlphabet.outcomeName (context x.1) b) = true) :=
    (Primrec.eq.comp (EncodedLeaderAlphabet.offered_primrec.comp (Primrec.snd.comp Primrec.fst)
      (EncodedLeaderAlphabet.outcomeName_primrec.comp (context_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (Primrec.const true)).primrecRel
  exact (p.swap.listFilter.comp (outcomes_primrec.comp Primrec.fst) Primrec.id).of_eq
    (fun x => by simp [selected,Function.swap])
theorem graphOf_primrec : Primrec₂ graphOf := Primrec.nat_div.comp
  (Primrec.nat_div.comp Primrec.snd
    (Primrec.succ.comp (EncodedLeaderObjective.priorityBound_primrec.comp (objective_primrec.comp Primrec.fst))))
  (EncodedRoundObjectives.stateCount_primrec.comp (objective_primrec.comp Primrec.fst))
theorem agrees_primrec : Primrec (fun x : Data × EncodedLeaderAlphabet.Header × EncodedLeaderAlphabet.Move => agrees x.1 x.2.1 x.2.2) :=
  (FiniteSearch.forall_mem (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
    (Primrec.eq.comp
      ((Primrec.list_getD false).comp (leaders_primrec.comp (Primrec.fst.comp Primrec.fst))
        (graphOf_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).primrecRel).decide

theorem legal_primrec : Primrec (fun x : Data × EncodedLeaderAlphabet.Header × EncodedLeaderAlphabet.Move => legal x.1 x.2.1 x.2.2) :=
  (Primrec.dom_bool₂ Bool.and).comp agrees_primrec
    (EncodedHeaderCompiler.test_primrec.comp
      ((graphData_primrec.comp Primrec.fst).pair ((objective_primrec.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair
          (selected_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))))
      ((Primrec.dom_bool Bool.not).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
theorem offerTable_primrec : Primrec offerTable := Primrec.list_flatMap moves_primrec
  (Primrec.list_map (outcomes_primrec.comp Primrec.fst)
    (EncodedLeaderAlphabet.offered_primrec.comp (Primrec.snd.comp Primrec.fst)
      (EncodedLeaderAlphabet.outcomeName_primrec.comp (context_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂).to₂
theorem legalTable_primrec : Primrec legalTable := Primrec.list_flatMap outcomes_primrec
  (Primrec.list_map (moves_primrec.comp Primrec.fst)
    (legal_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂).to₂
theorem progressBase_primrec : Primrec progressBase := EncodedLeaderProgress.compile_primrec.comp
  (context_primrec.pair initialCode_primrec)
theorem progressRows_primrec : Primrec progressRows := Primrec.list_flatMap moves_primrec
  (Primrec.list_map (outcomes_primrec.comp Primrec.fst)
    ((Primrec.list_getD []).comp
      (EncodedParityTables.rows_primrec.comp (progressBase_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_idxOf.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
        (EncodedLeaderProgress.letters_primrec.comp (context_primrec.comp (Primrec.fst.comp Primrec.fst))))).to₂).to₂
theorem progress_primrec : Primrec progress := (Primrec.fst.comp progressBase_primrec).pair
  ((EncodedParityTables.initial_primrec.comp progressBase_primrec).pair
    ((EncodedParityTables.priorities_primrec.comp progressBase_primrec).pair progressRows_primrec))
theorem compile_primrec : Primrec compile :=
  (Primrec.nat_sub.comp (Primrec.list_length.comp outcomes_primrec) (Primrec.const 1)).pair
    ((Primrec.list_length.comp moves_primrec).pair (progress_primrec.pair
      ((EncodedLeaderAlphabet.outcomeName_primrec.comp context_primrec initial_primrec).pair
        (offerTable_primrec.pair legalTable_primrec))))
theorem solve_primrec : Primrec solve := EncodedSupportedGame.solve_primrec.comp compile_primrec

end Characterisation.EncodedPublicLeaderGame
