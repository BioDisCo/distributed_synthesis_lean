/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainThreads

/-! # Numeric set-started chain monitor

State zero is the pre-start state, one is the even dead state, and `2+t`
is a live chain. A receiver input includes an initial thread guess. That
guess is checked against the handoff set only on the first step.
-/
namespace DistributedSynthesis.EncodedChainMonitor
open EncodedRoundObjectives EncodedChainThreads
abbrev Input := Data × List Nat
abbrev Letter := Bool × Bool × EncodedJournalLabels.Code × Nat
abbrev Context := Input × Letter
abbrev Receiver := Nat × Nat × Nat
abbrev Move := Context × Nat × Receiver

def stateCount (d : Data) := chainCount d + 2
def receivers (d : Data) : List Receiver :=
  (List.range (inputOne d)).product ((List.range (inputTwo d)).product (List.range (chainCount d)))
def chosen (x : Move) := if x.2.1 = 0 then x.2.2.2.2 else x.2.1-2
def chainMove (x : Move) : EncodedChainThreads.Move :=
  ((x.1.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2.1),chosen x,
    (bif x.1.2.2.1 then x.1.2.2.2.2 else x.2.2.1),
    (bif x.1.2.2.1 then x.2.2.2.1 else x.1.2.2.2.2))
def next (x : Move) :=
  if x.2.1 = 1 ∨ (x.2.1 = 0 ∧ x.2.2.2.2 ∉ x.1.1.2) then 1
  else EncodedChainThreads.next (chainMove x) + 2
def priority (d : Data) (q : Nat) := if q < 2 then 0 else
  objectivePriority d (current d (q-2) / EncodedRoundObjectives.stateCount d)
def priorities (d : Data) := (List.range (stateCount d)).map (priority d)
def edges (c : Context) : EncodedThreadBuchi.Edges :=
  (List.range (stateCount c.1.1)).flatMap (fun q => (receivers c.1.1).map (fun r => (q,next (c,q,r))))

theorem stateCount_primrec : Primrec stateCount := Primrec.nat_add.comp chainCount_primrec (Primrec.const 2)
theorem receivers_primrec : Primrec receivers :=
  FiniteSearch.product_primrec.comp (Primrec.list_range.comp inputOne_primrec)
    (FiniteSearch.product_primrec.comp (Primrec.list_range.comp inputTwo_primrec) (Primrec.list_range.comp chainCount_primrec))
private theorem q_pr : Primrec (fun x : Move => x.2.1) := Primrec.fst.comp Primrec.snd
private theorem r_pr : Primrec (fun x : Move => x.2.2) := Primrec.snd.comp Primrec.snd
private theorem guess_pr : Primrec (fun x : Move => x.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp r_pr)
private theorem d_pr : Primrec (fun x : Move => x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
private theorem set_pr : Primrec (fun x : Move => x.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
private theorem letter_pr : Primrec (fun x : Move => x.1.2) := Primrec.snd.comp Primrec.fst
theorem chosen_primrec : Primrec chosen :=
  Primrec.ite (Primrec.eq.comp q_pr (Primrec.const 0)) guess_pr (Primrec.nat_sub.comp q_pr (Primrec.const 2))
theorem chainMove_primrec : Primrec chainMove := by
  have hm := Primrec.fst.comp letter_pr
  have hs := Primrec.fst.comp (Primrec.snd.comp letter_pr)
  have hc := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp letter_pr))
  have hi := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp letter_pr))
  exact (d_pr.pair (hm.pair (hs.pair hc))).pair (chosen_primrec.pair
    ((Primrec.cond hs hi (Primrec.fst.comp r_pr)).pair
      (Primrec.cond hs (Primrec.fst.comp (Primrec.snd.comp r_pr)) hi)))
theorem next_primrec : Primrec next := by
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact Primrec.ite ((Primrec.eq.comp q_pr (Primrec.const 1)).or
    ((Primrec.eq.comp q_pr (Primrec.const 0)).and (hm.comp set_pr guess_pr).not))
    (Primrec.const 1) (Primrec.nat_add.comp
      (EncodedChainThreads.next_primrec.comp chainMove_primrec) (Primrec.const 2))
theorem priority_primrec : Primrec₂ priority :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
    (objectivePriority_primrec.comp Primrec.fst (Primrec.nat_div.comp
      (current_primrec.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 2)))
      (EncodedRoundObjectives.stateCount_primrec.comp Primrec.fst)))
theorem priorities_primrec : Primrec priorities :=
  Primrec.list_map (Primrec.list_range.comp stateCount_primrec) priority_primrec
theorem edges_primrec : Primrec edges :=
  Primrec.list_flatMap (Primrec.list_range.comp (stateCount_primrec.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.list_map (receivers_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      ((Primrec.snd.comp Primrec.fst).pair (next_primrec.comp
        ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))).to₂).to₂
end DistributedSynthesis.EncodedChainMonitor
