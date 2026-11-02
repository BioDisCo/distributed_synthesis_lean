/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GlobalLeaderProgress
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingBankCoherence

/-! Concrete predecessor links join the finite boundary families into one
infinite physical history. No independent history witness is chosen at a
later edge of an already selected thread. -/
namespace Characterisation
open DistributedSynthesis

/-- An increasing sequence of consistent finite histories has one infinite
extension. The lengths may grow arbitrarily fast; no phase bound is used. -/
theorem exists_word_of_prefix_chain {α : Type} (hist : Nat → List α)
    (strict : StrictMono (fun n => (hist n).length))
    (next : ∀ n, (hist n).IsPrefix (hist (n+1))) :
    ∃ word : Nat → α, ∀ n,
      List.ofFn (fun i : Fin (hist n).length => word i.val) = hist n := by
  have nested : ∀ n m, n ≤ m → (hist n).IsPrefix (hist m) := by
    intro n m le
    induction m, le using Nat.le_induction with
    | base => exact ⟨[],by simp⟩
    | succ m _ ih => exact ih.trans (next m)
  have long : ∀ t, t < (hist (t+1)).length := by
    intro t
    induction t with
    | zero =>
      have bound : (hist 0).length < (hist 1).length := strict (by omega)
      exact lt_of_le_of_lt (Nat.zero_le _) bound
    | succ t ih =>
      have bound : (hist (t+1)).length < (hist (t+1+1)).length := strict (by omega)
      exact lt_of_le_of_lt (Nat.succ_le_of_lt ih) bound
  let word : Nat → α := fun t => (hist (t+1))[t]'(long t)
  refine ⟨word,?_⟩
  intro n
  apply List.ext_getElem
  · simp
  · intro t _ within
    simp only [List.getElem_ofFn]
    change (hist (t+1))[t]'(long t) = (hist n)[t]
    rcases Nat.le_total (t+1) n with le | le
    · exact (nested _ _ le).getElem (long t)
    · exact ((nested _ _ le).getElem within).symm

theorem branchNode_eq_ofFn {α : Type} (word : Nat → α) (n : Nat) :
    branchNode word n = List.ofFn (fun i : Fin n => word i.val) := by
  induction n with
  | zero => simp [branchNode]
  | succ n ih =>
    rw [branchNode,ih,List.ofFn_succ']
    simp only [Fin.val_castSucc,Fin.val_last,List.concat_eq_append]

/-- Every consistent hidden slot thread lifts to one actual word, provided
the advertised predecessor links are literal prefix links in the common
family sequence. This applies simultaneously to all hidden threads. -/
theorem handover_thread_lifts_history {α Q : Type} {B C : Nat}
    (initial : HandoverCode B C) (word : Nat → LeaderHandover Q B C × Unit)
    (family : Nat → Fin (B+1) → List α) (cuts : Nat → Nat)
    (depth : ∀ n i, (family n i).length = cuts n) (mono : StrictMono cuts)
    (parents : ∀ n (i : Fin (word n).1.1.1.val),
      (family n ((word n).1.2.1 i)).IsPrefix
        (family (n+1) (handoverSlot (word n).1 i)))
    (thread : HiddenCodeContinuityThread initial HandoverEdge word) :
    ∃ physical : Nat → α, ∀ n,
      branchNode physical (cuts n) = family n (thread.code n).1 := by
  let hist n := family n (thread.code n).1
  have strict : StrictMono (fun n => (hist n).length) := by
    intro n m le
    simpa only [hist,depth] using mono le
  have next : ∀ n, (hist n).IsPrefix (hist (n+1)) := by
    intro n
    obtain ⟨i,old,nextCode⟩ := thread.edge n
    have nextSlot := congrArg Prod.fst nextCode
    simpa only [hist,← old,nextSlot] using parents n i
  obtain ⟨physical,exactHistory⟩ := exists_word_of_prefix_chain hist strict next
  refine ⟨physical,?_⟩
  intro n
  rw [branchNode_eq_ofFn,← depth n (thread.code n).1]
  exact exactHistory n

/-- A certificate's predecessor is an actual prefix of its child history.
For carried sources, root is the preceding boundary family and past adds
the common one-way word. No completeness or parity assumption is needed. -/
theorem closingCertificate_parent_prefix {H I₁ I₂ O₁ O₂ Q : Type} {B D n : Nat}
    (root past : H → EnvHistory I₁ I₂)
    (carried : ∀ h, (root h).IsPrefix (past h))
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (i : Fin move.1.val) :
    (root (closingLayerRoot n (move.2.2.1 i))).IsPrefix
      (closingLayerHistory past n (move.2.2.1 i)) := by
  rw [closingLayerHistory_word]
  exact (carried _).trans ⟨_,rfl⟩

end Characterisation
