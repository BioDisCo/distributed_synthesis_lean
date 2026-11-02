/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemOwnerOpenPairDynamics
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController

/-!
# A state-dependent safety test for retained owners

Process one must output its previous receipt bit. This is locally realizable
with one bit of memory. A homogeneous right controller, however, must output
`false` after its first round. Retaining that controller across a physical
left round therefore cannot implement this objective.
-/

namespace DistributedSynthesis
namespace ReceiptMemoryOwnerObstruction
open DetParityAutomaton

abbrev Record := RoundRecord Unit Unit Graph Bool Bool

def receivesOne : Graph → Bool
  | .right => false
  | _ => true

/-- The second coordinate is a sticky safety bit. -/
def objective : DetParityAutomaton Record where
  State := Bool × Bool
  stateFinite := inferInstance
  initial := (false, true)
  step := fun q r ↦ (receivesOne r.graph, q.2 && decide (r.outputOne = q.1))
  priority := fun q ↦ if q.2 then 0 else 1

def received {p : Proc} : View Unit Unit p → Bool
  | .recv .. => true
  | _ => false

def previousReceipt {p : Proc} : View Unit Unit p → Bool
  | .empty _ => false
  | .recv previous _ _ _ => received previous
  | .noRecv previous _ => received previous

def source : StrategyPair Unit Unit Bool Bool where
  one := previousReceipt
  two := fun _ ↦ false

/-- A two-state local Mealy implementation; process two has one state. -/
def controller : FinitePairedMealyController Unit Unit Bool Bool where
  OneControl := Bool
  TwoControl := Unit
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := false
  initialTwo := ()
  noRecvOne := fun previous _ ↦ (false, previous)
  recvOne := fun previous _ _ _ ↦ (true, previous)
  noRecvTwo := fun _ _ ↦ ((), false)
  recvTwo := fun _ _ _ _ ↦ ((), false)

theorem controller_noRecv_realizes (view : View Unit Unit .one) :
    controller.noRecvOne (received view) () =
      (received (.noRecv view (.inl ())), source.one (.noRecv view (.inl ()))) := rfl

theorem controller_recv_realizes (view : View Unit Unit .one)
    (other : View Unit Unit .two) :
    controller.recvOne (received view) () () () =
      (received (.recv view (.inl ()) other (.inr ())),
        source.one (.recv view (.inl ()) other (.inr ()))) := rfl

theorem source_next (history : History Unit Unit Graph Bool Bool)
    (env : EnvironmentRound Unit Unit) :
    (nextRound source history env).outputOne = received (currentView .one history) := by
  cases env with
  | mk one two graph => cases graph <;> rfl

theorem source_entry_state {history : History Unit Unit Graph Bool Bool}
    (h : StrategyGeneratedPrefix source history) :
    entryState (A := objective) history = (received (currentView .one history), true) := by
  induction h with
  | empty => rfl
  | @append history h env ih =>
    have he : entryState (A := objective)
        (History.append history (nextRound source history env)) =
        objective.step (entryState (A := objective) history) (nextRound source history env) := by
      simp [entryState, History.append, List.foldl_append]
    rw [he]
    rw [ih]
    change (receivesOne env.graph, true && decide
      ((nextRound source history env).outputOne = received (currentView .one history))) = _
    rw [source_next]
    cases env with
    | mk one two graph =>
      cases graph <;>
        simp [currentView_one_append, nextRound, receivesOne, received]

theorem source_run (env : EnvironmentSequence Unit Unit) (n : Nat) :
    objective.run (execution source env) n =
      (received (currentView .one (executionPrefix source env n)), true) := by
  have hfold : objective.run (execution source env) n =
      entryState (A := objective) (executionPrefix source env n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [run_succ, ih, executionPrefix_succ]
      simp [entryState, History.append, List.foldl_append, execution_apply]
  rw [hfold]
  exact source_entry_state (strategyGeneratedPrefix_executionPrefix source env n)

theorem source_wins (env : EnvironmentSequence Unit Unit) :
    objective.Accepts (execution source env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, fun p _ ↦ Nat.zero_le p⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  change objective.priority (objective.run (execution source env) N) = 0
  rw [source_run]
  rfl

/-- Read the strict successor's safety bit. -/
def strictSafe : PairedEntryTreeState objective → Bool
  | .inl _ => false
  | .inr (.inl slot) => slot.1.1.2
  | .inr (.inr slot) => slot.1.1.2

noncomputable section

theorem right_allowed_safe
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget objective family direction target) :
    strictSafe (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) = true := by
  obtain ⟨row, past, input, rfl⟩ := hallowed
  have ht := (profiledRawJointRightSiblingActivation objective source_wins
    family direction member hmember false).target_state row past input
  dsimp only [profiledRawJointRightSiblingActivation] at ht
  rw [ht]
  cases row with
  | first =>
    change (pairedRightFreshChildCodeLeft objective member.1.code
      member.1.lambdaOfStrategy past input).1.2 = true
    rw [pairedRightFreshChildCodeLeft_lambdaOfStrategy]
    exact congrArg Prod.snd (source_entry_state
      (procTwoFreshPair source _
        (strategyGenerated_extendPrefix_basic source member.1.leftGenerated _)
        input.2 input.1).rightGenerated)
  | both =>
    change (pairedRightFreshChildCodeBoth objective member.1.code
      member.1.lambdaOfStrategy past input).1.2 = true
    rw [pairedRightFreshChildCodeBoth_lambdaOfStrategy]
    exact congrArg Prod.snd (source_entry_state
      (procTwoFreshPair source _
        (strategyGenerated_extendPrefix_basic source member.1.bothGenerated _)
        input.2 input.1).rightGenerated)

/-- This is forced by the actual semantic target relation, for every accepted
finite right table, not merely for a hand-picked clock policy. -/
theorem right_physical_output_after_first
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (move : ProfiledRawJointRightPhysicalSiblingMove objective)
    (hdescriptor : move.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (env : Nat → Unit × Unit) (n : Nat) :
    let monitor := profiledRawJointRightPhysicalSiblingMonitor objective move.1 false
    let play := treePlay (narrowedInducedTree monitor
      (move.memberController objective false).labeledTree) env
    (play (n + 1)).2.2 = false := by
  dsimp only
  let monitor := profiledRawJointRightPhysicalSiblingMonitor objective move.1 false
  let play := treePlay (narrowedInducedTree monitor
    (move.memberController objective false).labeledTree) env
  obtain ⟨hclose, hallowed⟩ := move.memberController_targetSafe objective false env (n + 1) .first
  nth_rw 1 [hdescriptor] at hallowed
  rw [profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff] at hallowed
  have hs := right_allowed_safe family direction member hmember _ hallowed
  rw [hclose] at hs
  change (((monitor.run play (n + 1)).2.1.1.1.2 &&
    decide ((play (n + 1)).2.2 = (monitor.run play (n + 1)).2.1.1.1.1))) = true at hs
  have heq := of_decide_eq_true (Bool.and_eq_true_iff.mp hs).2
  have hprevious : (monitor.run play (n + 1)).2.1.1.1.1 = false := by
    rw [BlockRecordMonitor.run]
    rfl
  exact heq.trans hprevious

/-- At every reachable owner control, one further virtual right step fixes
the following blind output to `false`. The chosen receiver fibre is irrelevant. -/
theorem right_owner_after_step_false
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (move : ProfiledRawJointRightPhysicalSiblingMove objective)
    (hdescriptor : move.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (owner : (move.memberController objective false).Control)
    (hreachable : ProfiledRawJointRightPhysicalSiblingOwnerReachable objective move owner) :
    (((move.memberController objective false).labelOf
      ((move.memberController objective false).step owner ())).1 ()) = false := by
  obtain ⟨inputs, howner⟩ := hreachable
  let past : List (Unit × Unit) := inputs.map (fun _ ↦ ((), ()))
  have hsender : senderWord past = inputs := by
    simp only [past, senderWord, List.map_map]
    have hfun : (fun _ : Unit ↦ ()) = id := funext (fun x ↦ Subsingleton.elim _ _)
    change List.map (fun _ : Unit ↦ ()) inputs = inputs
    rw [hfun, List.map_id]
  have hlength : past.length = inputs.length := List.length_map _
  have h := right_physical_output_after_first family direction member hmember move hdescriptor
    (omegaOfList (past ++ [((), ())] ++ [((), ())])) inputs.length
  have hat := profiledRawJointRightPhysicalSibling_treePlay_at_prefix objective
    move (past ++ [((), ())]) ((), ())
  dsimp only at h hat
  rw [show inputs.length + 1 = (past ++ [((), ())]).length by simp [hlength]] at h
  rw [hat] at h
  change (((move.memberController objective false).labelOf
    ((move.memberController objective false).controlAt
      (senderWord (past ++ [((), ())])))).1 ()) = false at h
  rw [senderWord_append, hsender, TransitionRationalTree.controlAt_append] at h
  change (((move.memberController objective false).labelOf
    ((move.memberController objective false).step
      ((move.memberController objective false).controlAt inputs) ())).1 ()) = false at h
  rwa [← howner] at h

/-- Once violated, the safety condition cannot be repaired by a later suffix. -/
theorem unsafe_persists (q : objective.State) (word : Nat → Record) (N : Nat)
    (hbad : (objective.runFrom q word N).2 = false) :
    ∀ n, N ≤ n → (objective.runFrom q word n).2 = false := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hbad
  | succ k ih =>
    rw [Nat.add_succ, runFrom]
    change ((objective.runFrom q word (N + k)).2 && _) = false
    rw [ih (Nat.le_add_right N k)]
    rfl

theorem rejects_of_unsafe (q : objective.State) (word : Nat → Record) (N : Nat)
    (hbad : (objective.runFrom q word N).2 = false) :
    ¬ objective.AcceptsFrom q word := by
  intro hacc
  obtain ⟨p, ⟨m, hm⟩, hinf, _⟩ := hacc
  obtain ⟨n, hn, hp⟩ := hinf N
  have hs := unsafe_persists q word N hbad n hn
  change (if (objective.runFrom q word n).2 then 0 else 1) = p at hp
  rw [hs] at hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hp
  omega

theorem rejects_of_left_right_false (q : objective.State) (word : Nat → Record)
    (hleft : (word 0).graph = .left) (hfalse : (word 1).outputOne = false) :
    ¬ objective.AcceptsFrom q word := by
  apply rejects_of_unsafe q word 2
  rw [show 2 = (0 + 1) + 1 by omega, runFrom, runFrom]
  change ((objective.step q (word 0)).2 &&
    decide ((word 1).outputOne = receivesOne (word 0).graph)) = false
  rw [hfalse, hleft]
  simp [receivesOne]

/-- A necessary condition on every winning replacement, not just the named
source. The current blind output must retain the previous receipt event. -/
theorem accepting_word_remembers_previous (q : objective.State) (word : Nat → Record)
    (hacc : objective.AcceptsFrom q word) (n : Nat) :
    (word (n + 1)).outputOne = receivesOne (word n).graph := by
  have hs : (objective.runFrom q word ((n + 1) + 1)).2 = true := by
    apply Bool.eq_true_of_not_eq_false
    intro hbad
    exact rejects_of_unsafe q word ((n + 1) + 1) hbad hacc
  rw [runFrom] at hs
  change (((objective.runFrom q word (n + 1)).2 &&
    decide ((word (n + 1)).outputOne = (objective.runFrom q word (n + 1)).1))) = true at hs
  have heq := of_decide_eq_true (Bool.and_eq_true_iff.mp hs).2
  exact heq

/-- Even when the current input and current no-receive event agree, the two
histories require different outputs. Any future local-state quotient must
keep these contexts distinct at the next blind step. -/
theorem winning_strategy_separates_previous_receipts
    (strategy : StrategyPair Unit Unit Bool Bool)
    (hwin : ∀ env, objective.Accepts (execution strategy env)) :
    let leftThenRight : EnvironmentSequence Unit Unit :=
      fun n ↦ ⟨(), (), if n = 0 then .left else .right⟩
    let rightOnly : EnvironmentSequence Unit Unit := fun _ ↦ ⟨(), (), .right⟩
    (execution strategy leftThenRight 1).outputOne = true ∧
      (execution strategy rightOnly 1).outputOne = false := by
  dsimp only
  constructor
  · have h := accepting_word_remembers_previous objective.initial _
      (hwin (fun n ↦ ⟨(), (), if n = 0 then .left else .right⟩)) 0
    simpa only [execution_apply, nextRound, ↓reduceIte, receivesOne] using h
  · have h := accepting_word_remembers_previous objective.initial _
      (hwin (fun _ ↦ ⟨(), (), .right⟩)) 0
    simpa only [execution_apply, nextRound, receivesOne] using h

universe m
variable {Memory : Type m}

private abbrev Tables :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) objective source
private abbrev Controls :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) objective source ×
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) objective source

def ownerControlAt (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) (graphs : Nat → Graph) :
    Nat → Controls (Memory := Memory)
  | 0 => initial
  | n + 1 => (tables.ownerFibreRound objective source source_wins
      (ownerControlAt tables initial graphs n) ((), ()) (graphs n)).1

def ownerWord (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) (graphs : Nat → Graph) : Nat → Record :=
  fun n ↦ tables.ownerFibreRoundRecord objective source source_wins
    (ownerControlAt tables initial graphs n) ((), ()) (graphs n)

theorem ownerWord_graph (tables : Tables (Memory := Memory))
    (initial : Controls (Memory := Memory)) (graphs : Nat → Graph) (n : Nat) :
    (ownerWord tables initial graphs n).graph = graphs n := rfl

/-- The literal right output after a physical left round is wrong: the
preserved right owner has advanced once, but has not learned the receipt bit. -/
theorem open_left_right_output_false
    (tables : Tables (Memory := Memory))
    (pair : OpenOwnerPair (Memory := Memory) objective source)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective pair.right)
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member) :
    (tables.ownerFibreRound objective source source_wins
      ((tables.ownerFibreRound objective source source_wins
        (pair.controls objective source) ((), ()) .left).1) ((), ()) .right).2.1 = false := by
  rw [pair.round_left objective source source_wins tables,
    OpenOwnerPair.round_right_outputs]
  obtain ⟨past, howner, _⟩ := hvalid
  exact right_owner_after_step_false family direction member hmember
    pair.right.1 hdescriptor pair.right.2.1 ⟨senderWord past, howner⟩

/-- Every continuation of this actual two-round prefix rejects, from every
automaton state. No choice of bank resolver or accepted finite right table
can change the forced output. -/
theorem open_left_right_rejects
    (tables : Tables (Memory := Memory))
    (pair : OpenOwnerPair (Memory := Memory) objective source)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective pair.right)
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (graphs : Nat → Graph) (hzero : graphs 0 = .left) (hone : graphs 1 = .right)
    (q : objective.State) :
    ¬ objective.AcceptsFrom q (ownerWord tables (pair.controls objective source) graphs) := by
  have hout := open_left_right_output_false tables pair hvalid family direction member
    hmember hdescriptor
  have houtput : (ownerWord tables (pair.controls objective source) graphs 1).outputOne = false := by
    simpa only [ownerWord,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRoundRecord,
      ownerControlAt, hzero, hone] using hout
  exact rejects_of_left_right_false q _ hzero houtput

/-- The obstruction already occurs in the first two rounds of the staged
return cycle. This is the same staged shape used by the pulsed acceptance
theorem; an arbitrarily chosen fresh left move does not repair the right owner. -/
theorem staged_left_right_output_false
    (tables : Tables (Memory := Memory))
    (pair : StagedRightOwnerPair (Memory := Memory) objective source)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective pair.right)
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : pair.packet.successor.2.1.1.2.2 = some move) :
    (tables.ownerFibreRound objective source source_wins
      ((tables.ownerFibreRound objective source source_wins
        (pair.controls objective source) ((), ()) .left).1) ((), ()) .right).2.1 = false := by
  rw [pair.round_left objective source source_wins tables move hmove]
  change (((pair.right.1.memberController objective false).labelOf
    ((pair.right.1.memberController objective false).step pair.right.2.1 ())).1 ()) = false
  obtain ⟨past, howner, _⟩ := hvalid
  exact right_owner_after_step_false family direction member hmember
    pair.right.1 hdescriptor pair.right.2.1 ⟨senderWord past, howner⟩

theorem staged_left_right_rejects
    (tables : Tables (Memory := Memory))
    (pair : StagedRightOwnerPair (Memory := Memory) objective source)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective pair.right)
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : pair.packet.successor.2.1.1.2.2 = some move)
    (graphs : Nat → Graph) (hzero : graphs 0 = .left) (hone : graphs 1 = .right)
    (q : objective.State) :
    ¬ objective.AcceptsFrom q (ownerWord tables (pair.controls objective source) graphs) := by
  have hout := staged_left_right_output_false tables pair hvalid family direction member
    hmember hdescriptor move hmove
  have houtput : (ownerWord tables (pair.controls objective source) graphs 1).outputOne = false := by
    simpa only [ownerWord,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRoundRecord,
      ownerControlAt, hzero, hone] using hout
  exact rejects_of_left_right_false q _ hzero houtput

/-- The installed/staged controls are exactly the right honest-entry
constructor's endpoint shape. Reachability here is reachability of its
installed right owner; no accepting invariant for the mixed run is assumed. -/
theorem installed_entry_left_right_rejects
    (tables : Tables (Memory := Memory))
    (state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
      (Memory := Memory) objective source)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver objective)
    (owner : (receiver.1.memberController objective false).Control)
    (hreachable : ProfiledRawJointRightPhysicalSiblingOwnerReachable objective receiver.1 owner)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver objective)
    (packet : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) objective source)
    (family : ProfiledRawJointSemanticFamily objective source (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : receiver.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : packet.successor.2.1.1.2.2 = some move)
    (graphs : Nat → Graph) (hzero : graphs 0 = .left) (hone : graphs 1 = .right)
    (q : objective.State) :
    let initial :=
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryOne
        objective source state receiver owner template packet,
       ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryTwo
        objective source state receiver packet)
    ¬ objective.AcceptsFrom q (ownerWord tables initial graphs) := by
  dsimp only
  apply rejects_of_left_right_false q _ hzero
  have hout := tables.ownerFibreRound_left_right_installedStaged_blind
    objective source source_wins state receiver owner template packet move hmove
    (state, packet.successor) (state, packet.successor) ((), ()) ((), ())
  have hf := right_owner_after_step_false family direction member hmember
    receiver.1 hdescriptor owner hreachable
  simpa only [ownerWord,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRoundRecord,
    ownerControlAt, hzero, hone] using hout.trans hf

end
end ReceiptMemoryOwnerObstruction
end DistributedSynthesis
