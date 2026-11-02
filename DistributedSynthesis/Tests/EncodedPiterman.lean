/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanTransition
import DistributedSynthesis.Library.Automata.EncodedPitermanAllocation
import DistributedSynthesis.Library.Automata.EncodedPitermanStep

namespace DistributedSynthesis.Tests.EncodedPiterman
open EncodedPitermanStates EncodedPitermanTransition

#guard FiniteSearch.words ([0, 1] : List Nat) 0 = [[]]
#guard (FiniteSearch.words ([0, 1] : List Nat) 3).length = 8
#guard FiniteSearch.words ([] : List Nat) 2 = []
#guard (allCodes 0).length = 1
#guard (allCodes 1).length = 1024

def tree : Code := ([1, 1, 0, 0], [0, 1, 2, 2], [0, 0, 0, 0], [[0], [1], [], []], 2, 0)
#guard stage1 2 [(0, 1), (1, 1)] tree =
  ([1, 1, 0, 0], [0, 1, 2, 2], [0, 0, 0, 0], [[1], [1], [], []], 2, 2)
#guard stage1 2 [] tree =
  ([1, 1, 0, 0], [0, 1, 2, 2], [0, 0, 0, 0], [[], [], [], []], 2, 2)
-- Out-of-bound source entries must not introduce a successor; the decoder drops them.
#guard stepImage 2 [(99, 1)] [99] = []
#guard stepImage 2 [(0, 99)] [0] = []
#guard stepImage 2 [(0, 1), (0, 1), (1, 0)] [1, 0, 0] = [0, 1]

#guard EncodedPitermanAllocation.rank 8 [6, 2, 2, 99] 6 = 1
#guard EncodedPitermanAllocation.child 8 [6, 2, 2] [7, 1, 4] 2 = 1
#guard EncodedPitermanAllocation.child 8 [6, 2, 2] [7, 1, 4] 6 = 4
#guard EncodedPitermanAllocation.child 8 [6, 2, 2] [7, 1, 4] 5 = 0
#guard EncodedPitermanAllocation.name 8 [5, 0, 3] [6, 2] 2 = 3
#guard EncodedPitermanAllocation.name 8 [5, 0, 3] [6, 2] 6 = 4
#guard EncodedPitermanAllocation.name 8 [5, 0, 3] [6, 2] 5 = 0

example : Primrec allCodes := allCodes_primrec
example : Primrec (fun x : Nat × Edges × Code => stage1 x.1 x.2.1 x.2.2) := stage1_primrec

open NondetBuchiAutomaton.Piterman
example {L : Type} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
    (number : A.State ≃ Fin (Fintype.card A.State)) (t : CompactTreeData A) :
    ∃ code ∈ allCodes (Fintype.card A.State), decode A number code = t :=
  allCodes_complete A number t

example {L : Type} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
    (number : A.State ≃ Fin (Fintype.card A.State)) (edges : Edges) (letter : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
    (decStep : ∀ q a r, Decidable (A.step q a r)) (code : Code) :
    decode A number (stage1 (Fintype.card A.State) edges code) =
      Computable.stage1 A decStep (decode A number code) letter :=
  stage1_eq_executable A number edges letter he decStep code

def branchTree : Code :=
  ([1, 1, 0, 0], [0, 1, 2, 2], [0, 0, 0, 0], [[0, 1], [1], [], []], 2, 2)
def created : Code :=
  ([1, 1, 1, 1], [0, 1, 2, 3], [0, 0, 0, 1], [[0, 1], [1], [1], [1]], 2, 2)
def pruned : Code :=
  ([1, 1, 1, 1], [0, 1, 2, 3], [0, 0, 0, 1], [[0, 1], [1], [], [1]], 2, 2)
def greenDeleted : Code :=
  ([1, 1, 1, 0], [0, 1, 2, 3], [0, 0, 0, 1], [[0, 1], [1], [], []], 2, 1)
def finished : Code :=
  ([1, 1, 0, 0], [0, 1, 2, 3], [0, 0, 0, 1], [[0, 1], [1], [], []], 2, 1)

-- Both original nodes trigger, but the newly created children do not trigger again.
#guard EncodedPitermanCreation.triggers (2, [1], branchTree) = [0, 1]
#guard EncodedPitermanCreation.owner (2, [1], branchTree) 2 = some 0
#guard EncodedPitermanCreation.owner (2, [1], branchTree) 3 = some 1
#guard EncodedPitermanCreation.stage2 (2, [1], branchTree) = created
#guard EncodedPitermanPruning.stage3 (2, created) = pruned
#guard EncodedPitermanGreen.greenNodes (2, pruned) = [1, 2]
#guard EncodedPitermanGreen.removedNodes (2, pruned) = [3]
#guard EncodedPitermanGreen.stage4 (2, pruned) = greenDeleted
#guard EncodedPitermanDeletion.emptyNodes (2, greenDeleted) = [2]
#guard EncodedPitermanDeletion.removed (2, greenDeleted) [3] = [2, 3]
#guard EncodedPitermanDeletion.stage5 (2, greenDeleted) [3] = finished
#guard EncodedPitermanStep.allRemoved (2, [(0, 0), (1, 1)], [1], branchTree) = [2, 3]
#guard EncodedPitermanStep.transition (2, [(0, 0), (1, 1)], [1], branchTree) = finished
#guard EncodedPitermanStep.step (2, [(0, 0), (1, 1)], [1], branchTree) == some finished
#guard EncodedPitermanStep.step (2, [], [1], branchTree) = none

-- A cyclic parent record still has an exact terminating ancestor test.
def cycleTree : Code := ([], [], [0, 2, 1, 0], [], 2, 2)
#guard EncodedPitermanPruning.ancestor (2, cycleTree) 2 1
#guard !EncodedPitermanPruning.ancestor (2, cycleTree) 0 1

-- Blocking must propagate through a younger sibling's descendants.
def descendantTree : Code :=
  ([1, 1, 1, 1, 0, 0], [0, 1, 2, 3, 3, 3], [0, 0, 0, 2, 0, 0],
    [[0, 1], [0], [0], [0], [], []], 3, 3)
#guard EncodedPitermanPruning.blocked (3, descendantTree) 3 0
#guard !EncodedPitermanPruning.blocked (3, descendantTree) 1 0
#guard (EncodedPitermanPruning.stage3 (3, descendantTree)).2.2.2.1 = [[0, 1], [0], [], [], [], []]
#guard EncodedPitermanMinima.minName (3, descendantTree) [1, 3, 99] = 1
#guard EncodedPitermanMinima.minName (3, descendantTree) [3, 4, 99] = 3

def beforeCompaction : Code :=
  ([1, 0, 1, 0, 0, 0], [0, 1, 2, 3, 3, 3], [0, 0, 0, 0, 0, 0],
    [[0, 1], [], [1], [], [], []], 1, 3)
-- Deleted node 1 retains its old name, but surviving node 2 is renamed to 1.
#guard (EncodedPitermanDeletion.stage6 (3, beforeCompaction) [1]).2.1 = [0, 1, 1, 3, 3, 3]

example : Primrec EncodedPitermanStep.step := EncodedPitermanStep.step_primrec
example {L : Type} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
    (number : A.State ≃ Fin (Fintype.card A.State))
    (decStep : ∀ q a r, Decidable (A.step q a r)) (decAccept : DecidablePred A.accepting)
    (edges : Edges) (acc : List Nat) (letter : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
    (ha : ∀ q, (number q).val ∈ acc ↔ A.accepting q)
    (t : CompactTreeData A) (ht : t.WellFormed A) :
    EncodedPitermanStep.step (Fintype.card A.State, edges, acc, encode A number t) =
      (Computable.liveTransition A decStep decAccept ⟨t, ht⟩ letter).map
        (fun live => encode A number live.val) :=
  EncodedPitermanStep.step_correct A number decStep decAccept edges acc letter he ha t ht

end DistributedSynthesis.Tests.EncodedPiterman
