/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton

/-! # Nonemptiness under a surjective change of tree alphabets

A deterministic simulation preserves nonemptiness in both directions when
every semantic branch and label has a representing code. Repeated codes are
allowed; the state projection need not be injective or surjective.
-/
namespace DistributedSynthesis.TreeMonitorRetraction
variable {B C L K : Type*} (N : DeterministicBlockMonitor B L) (M : DeterministicBlockMonitor C K)
  (state : N.State → M.State) (branch : B → C) (label : L → K)
  (hinit : state N.initial = M.initial)
  (hstep : ∀ q l b, state (N.step q l b) = M.step (state q) (label l) (branch b))
  (hpriority : ∀ q, N.priority q = M.priority (state q))

theorem map_branchNode (f : B → C) (b : Nat → B) (t : Nat) :
    (branchNode b t).map f = branchNode (fun n => f (b n)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (branchNode b t ++ [b t]).map f = _
    rw [List.map_append,ih]
    rfl

include hinit hstep in
theorem control_along (tn : LabeledTree B L) (tm : LabeledTree C K)
    (bn : Nat → B) (bm : Nat → C) (hb : ∀ t, branch (bn t) = bm t)
    (hl : ∀ t, label (tn (branchNode bn t)) = tm (branchNode bm t)) (t : Nat) :
    state (N.control tn (branchNode bn t)) = M.control tm (branchNode bm t) := by
  induction t with
  | zero => exact hinit
  | succ t ih =>
    change state (N.control tn (branchNode bn t ++ [bn t])) = M.control tm (branchNode bm t ++ [bm t])
    rw [N.control_append,M.control_append,hstep,ih,hb,hl]

include hinit hstep hpriority in
theorem nonempty_iff (hbranch : Function.Surjective branch) (hlabel : Function.Surjective label) :
    (∃ tree, N.toRunAutomaton.acceptsTree tree) ↔ ∃ tree, M.toRunAutomaton.acceptsTree tree := by
  classical
  obtain ⟨bs,hbs⟩ := hbranch.hasRightInverse
  obtain ⟨ls,hls⟩ := hlabel.hasRightInverse
  have hbn (b : Nat → C) (t : Nat) :
      (branchNode (fun n => bs (b n)) t).map branch = branchNode b t := by
    rw [map_branchNode]
    congr 1
    funext n
    exact hbs (b n)
  constructor
  · rintro ⟨tn,hn⟩
    let tm : LabeledTree C K := fun node => label (tn (node.map bs))
    refine ⟨tm,(M.acceptsTree_iff_winningTree tm).mpr ?_⟩
    intro bm
    have hc := control_along N M state branch label hinit hstep tn tm
      (fun n => bs (bm n)) bm (fun n => hbs (bm n)) (fun n => by
        dsimp only [tm]
        rw [map_branchNode])
    have hp : (fun t => N.priority (N.control tn (branchNode (fun n => bs (bm n)) t))) =
        fun t => M.priority (M.control tm (branchNode bm t)) := by
      funext t
      rw [hpriority,hc]
    have h := ((N.acceptsTree_iff_winningTree tn).mp hn) (fun n => bs (bm n))
    exact Eq.mp (congrArg NatSeqMinEvenParity hp) h
  · rintro ⟨tm,hm⟩
    let tn : LabeledTree B L := fun node => ls (tm (node.map branch))
    refine ⟨tn,(N.acceptsTree_iff_winningTree tn).mpr ?_⟩
    intro bn
    have hc := control_along N M state branch label hinit hstep tn tm
      bn (fun n => branch (bn n)) (fun _ => rfl) (fun n => by
        dsimp only [tn]
        rw [hls,map_branchNode])
    have hp : (fun t => N.priority (N.control tn (branchNode bn t))) =
        fun t => M.priority (M.control tm (branchNode (fun n => branch (bn n)) t)) := by
      funext t
      rw [hpriority,hc]
    have h := ((M.acceptsTree_iff_winningTree tm).mp hm) (fun n => branch (bn n))
    exact Eq.mpr (congrArg NatSeqMinEvenParity hp) h
end DistributedSynthesis.TreeMonitorRetraction
