/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingScans
import DistributedSynthesis.Library.Distributed.LeaderPhases.PointedGraphRoots
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect

/-! Concrete graph-rule tables for the fixed adversary. The numbering uses
the characterisation graph convention and the existing checked root rules.
These tables depend only on the adversary and its graph bounds. -/
namespace Characterisation.EncodedClosingScans
open DistributedSynthesis

def graphNumber : Graph ≃ Fin 3 where
  toFun := graphCode
  invFun i := if i=0 then .right else if i=1 then .both else .left
  left_inv g := by cases g <;> rfl
  right_inv i := by fin_cases i <;> rfl

variable {GQ : Type} {d K S : Nat} [Fintype GQ] [DecidableEq GQ]
  (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
  (states : GraphRootState GQ d K ≃ Fin S)

def ruleNumber := FiniteFunctionCodes.prod (FiniteFunctionCodes.prod states graphNumber) states
def boundaryNumber := FiniteFunctionCodes.prod states graphNumber

def rulesEncode : Rules :=
  (S,List.ofFn (fun i => let p := (ruleNumber states).symm i
      checkGraphRootStep recognizer p.1.1 p.1.2 p.2),
    List.ofFn (fun i => let p := (boundaryNumber states).symm i
      graphRootBoundary recognizer p.1 p.2),
    List.ofFn (fun i => (states.symm i).isSome))

theorem allowed_encode (q next : GraphRootState GQ d K) (g : Graph) :
    allowed (rulesEncode recognizer states) (states q).val (graphCode g).val (states next).val =
      checkGraphRootStep recognizer q g next := by
  have h := EncodedClosingBanks.table_eval (ruleNumber states)
    (fun p => checkGraphRootStep recognizer p.1.1 p.1.2 p.2) false ((q,g),next)
  have index : (ruleNumber states ((q,g),next)).val =
      ((states q).val*3+(graphCode g).val)*S+(states next).val := by
    change (states next).val + S*((graphCode g).val+3*(states q).val) = _
    ring
  rw [index] at h
  exact h

theorem boundaryRule_encode (q : GraphRootState GQ d K) (g : Graph) :
    boundaryRule (rulesEncode recognizer states) (states q).val (graphCode g).val =
      graphRootBoundary recognizer q g := by
  have h := EncodedClosingBanks.table_eval (boundaryNumber states)
    (fun p => graphRootBoundary recognizer p.1 p.2) false (q,g)
  have index : (boundaryNumber states (q,g)).val = (states q).val*3+(graphCode g).val := by
    change (graphCode g).val+3*(states q).val = _
    ring
  rw [index] at h
  exact h

theorem liveRule_encode (q : GraphRootState GQ d K) :
    liveRule (rulesEncode recognizer states) (states q).val = q.isSome :=
  EncodedClosingBanks.table_eval states Option.isSome false q

end Characterisation.EncodedClosingScans
