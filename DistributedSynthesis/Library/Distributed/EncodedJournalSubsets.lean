/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalBoundary
import DistributedSynthesis.Library.Computability.FiniteSetCodes

/-! # Canonical numeric thread sets for every journal transition

All unions are enumerated over finite input lists and normalized. Thus two
lists that represent the same set produce the same next-state set code.
-/
namespace DistributedSynthesis.EncodedJournalSubsets
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads
abbrev Args := EncodedOrdinaryThreads.Context × List Nat × Nat
abbrev ChainArgs := EncodedChainThreads.Context × List Nat × Nat

def inputs (d : Data) := (List.range (inputOne d)).product (List.range (inputTwo d))
def step (x : Args) := FiniteSetCodes.imageCodes (atomCount x.1.1) x.2.1
  (List.range (receiverCount x.1)) (fun q r => EncodedOrdinaryThreads.next (x.1,q,r,x.2.2))
def openBlock (x : EncodedOrdinaryThreads.Context × Nat × Nat) :=
  step (x.1,[initial x.1.1 (x.2.1 / stateCount x.1.1)],x.2.2)
def close (x : Args) := FiniteSetCodes.imageCodes (atomCount x.1.1) x.2.1
  (inputs x.1.1) (fun q ij => EncodedJournalBoundary.close (x.1,q,ij))
def reverse (x : Args) := FiniteSetCodes.imageCodes (chainCount x.1.1) x.2.1
  (List.range (senderCount x.1)) (fun q r => EncodedJournalBoundary.reverse
    (x.1,q,(bif x.1.2.1 then r else x.2.2),(bif x.1.2.1 then x.2.2 else r)))
def both (x : EncodedOrdinaryThreads.Context × Nat) := FiniteSetCodes.imageCodes (atomCount x.1.1) [x.2]
  (inputs x.1.1) (fun q ij => EncodedJournalBoundary.both (x.1,q,ij))
def chainStep (x : ChainArgs) := FiniteSetCodes.imageCodes (chainCount x.1.1) x.2.1
  (List.range (bif x.1.2.2.1 then inputTwo x.1.1 else inputOne x.1.1))
  (fun q r => EncodedChainThreads.next
    (x.1,q,(bif x.1.2.2.1 then x.2.2 else r),(bif x.1.2.2.1 then r else x.2.2)))
def chainClose (x : Args) := FiniteSetCodes.imageCodes (atomCount x.1.1) x.2.1
  (inputs x.1.1) (fun q ij => EncodedJournalBoundary.chainClose (x.1,q,ij))

theorem inputs_primrec : Primrec inputs := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp inputOne_primrec) (Primrec.list_range.comp inputTwo_primrec)
private theorem d_pr : Primrec (fun x : Args => x.1.1) := Primrec.fst.comp Primrec.fst
private theorem set_pr : Primrec (fun x : Args => x.2.1) := Primrec.fst.comp Primrec.snd
theorem step_primrec : Primrec step := by
  apply FiniteSetCodes.imageCodes_primrec (atomCount_primrec.comp d_pr) set_pr
    (Primrec.list_range.comp (receiverCount_primrec.comp Primrec.fst))
  exact EncodedOrdinaryThreads.next_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp Primrec.snd).pair ((Primrec.snd.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
theorem openBlock_primrec : Primrec openBlock := by
  have hd : Primrec (fun x : EncodedOrdinaryThreads.Context × Nat × Nat => x.1.1) := Primrec.fst.comp Primrec.fst
  exact step_primrec.comp (Primrec.fst.pair
    ((Primrec.list_cons.comp (initial_primrec.comp hd
      (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd) (stateCount_primrec.comp hd))) (Primrec.const [])).pair
      (Primrec.snd.comp Primrec.snd)))
theorem close_primrec : Primrec close := by
  apply FiniteSetCodes.imageCodes_primrec (atomCount_primrec.comp d_pr) set_pr (inputs_primrec.comp d_pr)
  exact EncodedJournalBoundary.close_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
theorem reverse_primrec : Primrec reverse := by
  apply FiniteSetCodes.imageCodes_primrec (chainCount_primrec.comp d_pr) set_pr
    (Primrec.list_range.comp (senderCount_primrec.comp Primrec.fst))
  have hs : Primrec (fun x : Args × Nat × Nat => x.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hr : Primrec (fun x : Args × Nat × Nat => x.2.2) := Primrec.snd.comp Primrec.snd
  have hi : Primrec (fun x : Args × Nat × Nat => x.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact EncodedJournalBoundary.reverse_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp Primrec.snd).pair ((Primrec.cond hs hr hi).pair (Primrec.cond hs hi hr))))
theorem both_primrec : Primrec both := by
  have hd : Primrec (fun x : EncodedOrdinaryThreads.Context × Nat => x.1.1) := Primrec.fst.comp Primrec.fst
  apply FiniteSetCodes.imageCodes_primrec (atomCount_primrec.comp hd)
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) (inputs_primrec.comp hd)
  exact EncodedJournalBoundary.both_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
theorem chainStep_primrec : Primrec chainStep := by
  have hd : Primrec (fun x : ChainArgs => x.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun x : ChainArgs => x.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  apply FiniteSetCodes.imageCodes_primrec (chainCount_primrec.comp hd)
    (Primrec.fst.comp Primrec.snd)
    (Primrec.list_range.comp (Primrec.cond hs (inputTwo_primrec.comp hd) (inputOne_primrec.comp hd)))
  have hr : Primrec (fun x : ChainArgs × Nat × Nat => x.2.2) := Primrec.snd.comp Primrec.snd
  have hi : Primrec (fun x : ChainArgs × Nat × Nat => x.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact EncodedChainThreads.next_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp Primrec.snd).pair ((Primrec.cond (hs.comp Primrec.fst) hi hr).pair
      (Primrec.cond (hs.comp Primrec.fst) hr hi))))
theorem chainClose_primrec : Primrec chainClose := by
  apply FiniteSetCodes.imageCodes_primrec (atomCount_primrec.comp d_pr) set_pr (inputs_primrec.comp d_pr)
  exact EncodedJournalBoundary.chainClose_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
end DistributedSynthesis.EncodedJournalSubsets
