/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderLegality
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedInitialState

/-! Generate the singleton initial family and its persistent-thread code.
The initial graph representation is fixed before the specification varies. -/
namespace Characterisation.EncodedPublicLeaderGame
open DistributedSynthesis
attribute [local irreducible] Primrec

def objectiveInitial (o : EncodedRoundObjectives.Data) :=
  EncodedParityTables.initial o.2 % EncodedRoundObjectives.stateCount o
def firstOutcome (o : EncodedRoundObjectives.Data) (graph : Nat) : EncodedLeaderAlphabet.Outcome :=
  ((1,[1],[1],[EncodedLeaderObjective.priorityBound o + (EncodedLeaderObjective.priorityBound o+1)*
    (objectiveInitial o + EncodedRoundObjectives.stateCount o*graph)]),[0],[EncodedLeaderObjective.priorityBound o])
def firstCode (o : EncodedRoundObjectives.Data) :=
  (0,EncodedRoundObjectives.objectivePriority o (objectiveInitial o))
def initialData (g : EncodedHeaderCompiler.GraphData) (ls : List Bool) (o : EncodedRoundObjectives.Data) (graph : Nat) : Data :=
  (g,ls,o,firstOutcome o graph,firstCode o)

theorem objectiveInitial_primrec : Primrec objectiveInitial := Primrec.nat_mod.comp
  (EncodedParityTables.initial_primrec.comp Primrec.snd) EncodedRoundObjectives.stateCount_primrec
theorem firstOutcome_primrec : Primrec₂ firstOutcome := by
  have obj : Primrec (fun x : EncodedRoundObjectives.Data × Nat => x.1) := Primrec.fst
  have c := EncodedLeaderObjective.priorityBound_primrec.comp obj
  have label := Primrec.nat_add.comp c (Primrec.nat_mul.comp (Primrec.succ.comp c)
    (Primrec.nat_add.comp (objectiveInitial_primrec.comp obj)
      (Primrec.nat_mul.comp (EncodedRoundObjectives.stateCount_primrec.comp obj) Primrec.snd)))
  exact ((Primrec.const 1).pair ((Primrec.const [1]).pair ((Primrec.const [1]).pair
    (Primrec.list_cons.comp label (Primrec.const []))))).pair
    ((Primrec.const [0]).pair (Primrec.list_cons.comp c (Primrec.const [])))
theorem firstCode_primrec : Primrec firstCode := (Primrec.const 0).pair
  (EncodedRoundObjectives.objectivePriority_primrec.comp Primrec.id objectiveInitial_primrec)
theorem initialData_primrec : Primrec (fun x : EncodedHeaderCompiler.GraphData × List Bool × EncodedRoundObjectives.Data × Nat =>
    initialData x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      ((firstOutcome_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
        (firstCode_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))))

def solveInitial (g : EncodedHeaderCompiler.GraphData) (ls : List Bool) (o : EncodedRoundObjectives.Data) (graph : Nat) :=
  solve (initialData g ls o graph)

theorem solveInitial_primrec : Primrec (fun x : EncodedHeaderCompiler.GraphData × List Bool × EncodedRoundObjectives.Data × Nat =>
    solveInitial x.1 x.2.1 x.2.2.1 x.2.2.2) := solve_primrec.comp initialData_primrec

section Correct
variable {GQ : Type} {S B D K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (o : EncodedRoundObjectives.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ D K ≃ Fin S) (positive : 0 < B) (g : GraphRootState GQ D K)
local notation "M" => EncodedLeaderObjective.automaton o
local notation "rankBound" => EncodedLeaderObjective.priorityBound o
local notation "annNumber" => leaderAnnotationNumber (C:=rankBound) M graphs (Equiv.refl _)
local instance publicInitialObjectiveEq : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))
local notation "choice" => numberedInitialChoice (C:=rankBound) M positive g

omit [Fintype GQ] [DecidableEq GQ] in
theorem firstOutcome_encode : firstOutcome o (graphs g).val =
    EncodedLeaderAlphabet.outcomeEncode annNumber choice.1 := by
  rfl

omit [Fintype GQ] [DecidableEq GQ] in
theorem firstCode_encode : firstCode o =
    ((numberedGameInitialCode M (EncodedLeaderObjective.rank o) choice).1.val,
      (numberedGameInitialCode M (EncodedLeaderObjective.rank o) choice).2.val) := by
  have slot := numberedHistorySlot_at M choice.1.1 choice.2
    (fun i j _ => Subsingleton.elim (α := Fin 1) i j) (0 : Fin 1)
  apply Prod.ext
  · change 0 = (numberedHistorySlot M choice.1.1 choice.2 []).val
    exact (congrArg Fin.val slot).symm
  · change EncodedRoundObjectives.objectivePriority o (objectiveInitial o) =
      (EncodedLeaderObjective.rank o (M).initial).val % (rankBound+1)
    exact (Nat.mod_eq_of_lt (EncodedLeaderObjective.rank o (M).initial).isLt).symm

theorem initialData_encode :
    initialData (EncodedHeaderCompiler.graphDataEncode (B:=B) recognizer graphs) (leaderTable graphs) o (graphs g).val =
      dataEncode o recognizer graphs choice.1 (numberedGameInitialCode M (EncodedLeaderObjective.rank o) choice) := by
  unfold initialData dataEncode
  rw [firstOutcome_encode o graphs positive g,firstCode_encode o positive g]

end Correct
end Characterisation.EncodedPublicLeaderGame
