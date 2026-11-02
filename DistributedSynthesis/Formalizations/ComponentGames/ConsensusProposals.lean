/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusExecution

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2000000
variable {V W : Type}

def plainOutput (table : StrategyPair V V V V) : (p : Proc) → View V V p → V
  | .one => table.one
  | .two => table.two

def ProposalTableCorrect (table : StrategyPair V V V V) (A : Set (Nat → Graph)) (R : Nat) : Prop :=
  ∀ x gs, gs.length = R → LivePrefix A gs →
    (task V).allows x (fun p => plainOutput table p (currentView p (proposalHistory x gs)))

theorem relabel_proposalView (f g : V → W) (x : Proc → V) (gs : List Graph) (p : Proc) :
    InputAlphabetRelabeling.view f g (currentView p (proposalHistory x gs)) =
    currentView p (proposalHistory (fun q => match q with | .one => f (x .one) | .two => g (x .two)) gs) := by
  induction gs using List.reverseRecOn generalizing p with
  | nil => cases p <;> rfl
  | append_singleton gs a ih =>
    rw [proposalHistory_append,proposalHistory_append]
    change InputAlphabetRelabeling.view f g (currentView p (History.append _ _)) = currentView p (History.append _ _)
    cases p
    all_goals simp only [currentView_one_append,currentView_two_append]
    all_goals cases a <;> simp [InputAlphabetRelabeling.view,InputAlphabetRelabeling.payload,Proc.other,ih]

theorem silentAge_proposals (x : Proc → V) (y : Proc → W) (gs : List Graph) (p : Proc) :
    silentAge (currentView p (proposalHistory x gs)) = silentAge (currentView p (proposalHistory y gs)) := by
  rw [← silentAge_erase,eraseView_current,← silentAge_erase (currentView p (proposalHistory y gs)),eraseView_current]
  simp [History.graphSequence,proposalHistory,List.map_map,Function.comp_def]

/-- If no message has been received, changing the other proposal leaves
the local view unchanged: the indistinguishability step in the paper. -/
theorem blind_proposals_equal (x y : Proc → V) (gs : List Graph) (p : Proc)
    (own : x p = y p) (blind : gs.length ≤ silentAge (currentView p (proposalHistory x gs))) :
    currentView p (proposalHistory x gs) = currentView p (proposalHistory y gs) := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs a ih =>
    rw [proposalHistory_append] at blind
    rw [proposalHistory_append,proposalHistory_append]
    change _ ≤ silentAge (currentView p (History.append _ _)) at blind
    change currentView p (History.append _ _) = currentView p (History.append _ _)
    cases p
    all_goals simp only [currentView_one_append,currentView_two_append] at blind ⊢
    all_goals cases a <;> simp only [silentAge,List.length_append,List.length_singleton] at blind ⊢
    all_goals first
      | omega
      | rw [ih (by omega),own]

def binaryIds : Proc → Bool
  | .one => false
  | .two => true

/-- A process deciding on the other process's simulated ID must have
received a message by that round. No extra round is introduced. -/
theorem binary_choice_received (table : StrategyPair Bool Bool Bool Bool)
    (A : Set (Nat → Graph)) (R : Nat) (correct : ProposalTableCorrect table A R)
    (gs : List Graph) (len : gs.length = R) (live : LivePrefix A gs) (p : Proc)
    (other : plainOutput table p (currentView p (proposalHistory binaryIds gs)) ≠ binaryIds p) :
    silentAge (currentView p (proposalHistory binaryIds gs)) < R := by
  by_contra late
  let uniform : Proc → Bool := fun _ => binaryIds p
  have same := blind_proposals_equal binaryIds uniform gs p rfl (by omega)
  have valid := correct uniform gs len live
  change table.one _ = table.two _ ∧ (table.one _ = binaryIds p ∨ table.one _ = binaryIds p) at valid
  have first := valid.2.elim id id
  have all (q : Proc) : plainOutput table q (currentView q (proposalHistory uniform gs)) = binaryIds p := by
    cases q
    · exact first
    · exact valid.1.symm.trans first
  exact other ((congrArg (plainOutput table p) same).trans (all p))

def payloadValue : PSum V V → V
  | .inl x => x
  | .inr x => x

def readProposal (fallback : V) (q : Proc) {p : Proc} (v : View V V p) : V :=
  (((if q = p then ownInputs v else otherInputs v).head?).map payloadValue).getD fallback

theorem inputWord_proposals (x : Proc → V) (gs : List Graph) (p : Proc) :
    inputWord p (proposalHistory x gs) = List.replicate gs.length (proposalPayload x p) := by
  cases p <;> simp [inputWord,proposalHistory,proposalPayload,List.map_map,Function.comp_def,RoundRecord.input]

theorem readProposal_own (fallback : V) (x : Proc → V) (gs : List Graph) (positive : 0 < gs.length) (p : Proc) :
    readProposal fallback p (currentView p (proposalHistory x gs)) = x p := by
  rw [readProposal,if_pos rfl,ownInputs_current,inputWord_proposals]
  cases len : gs.length with
  | zero => omega
  | succ n => cases p <;> simp [proposalPayload,List.replicate_succ,payloadValue]

theorem readProposal_other (fallback : V) (x : Proc → V) (gs : List Graph) (p : Proc)
    (received : silentAge (currentView p (proposalHistory x gs)) < gs.length) :
    readProposal fallback p.other (currentView p (proposalHistory x gs)) = x p.other := by
  have known := otherInputs_history (proposalHistory x gs)
  have len : History.length (proposalHistory x gs) = gs.length := by simp [History.length,proposalHistory]
  cases p
  all_goals simp only [readProposal,Proc.other,reduceCtorEq,if_false]
  · rw [known.1.1,inputWord_proposals,len,List.take_replicate]
    have pos : 0 < min (gs.length - silentAge (currentView Proc.one (proposalHistory x gs))) gs.length := by omega
    cases eq : min (gs.length - silentAge (currentView Proc.one (proposalHistory x gs))) gs.length with
    | zero => omega
    | succ n => simp [proposalPayload,List.replicate_succ,payloadValue]
  · rw [known.2.1,inputWord_proposals,len,List.take_replicate]
    have pos : 0 < min (gs.length - silentAge (currentView Proc.two (proposalHistory x gs))) gs.length := by omega
    cases eq : min (gs.length - silentAge (currentView Proc.two (proposalHistory x gs))) gs.length with
    | zero => omega
    | succ n => simp [proposalPayload,List.replicate_succ,payloadValue]

def boolProcess (b : Bool) : Proc := if b then .two else .one

/-- Simulate the two distinct binary IDs, then decide the selected
broadcaster's actual proposal using the existing input-knowledge operations. -/
def liftBinaryTable (fallback : V) (table : StrategyPair Bool Bool Bool Bool) : StrategyPair V V V V :=
  ⟨fun v => readProposal fallback (boolProcess (table.one (InputAlphabetRelabeling.view (fun _ => false) (fun _ => true) v))) v,
   fun v => readProposal fallback (boolProcess (table.two (InputAlphabetRelabeling.view (fun _ => false) (fun _ => true) v))) v⟩

theorem liftBinaryTable_correct (fallback : V) (table : StrategyPair Bool Bool Bool Bool)
    (A : Set (Nat → Graph)) (R : Nat) (positive : 0 < R)
    (correct : ProposalTableCorrect table A R) : ProposalTableCorrect (liftBinaryTable fallback table) A R := by
  intro x gs len live
  have valid := correct binaryIds gs len live
  let decision := table.one (currentView .one (proposalHistory binaryIds gs))
  have same (p : Proc) : plainOutput table p (currentView p (proposalHistory binaryIds gs)) = decision := by
    cases p
    · rfl
    · exact valid.1.symm
  have outputs (p : Proc) : plainOutput (liftBinaryTable fallback table) p (currentView p (proposalHistory x gs)) =
      x (boolProcess decision) := by
    have localRule : plainOutput (liftBinaryTable fallback table) p (currentView p (proposalHistory x gs)) =
        readProposal fallback (boolProcess (plainOutput table p (currentView p (proposalHistory binaryIds gs))))
          (currentView p (proposalHistory x gs)) := by
      cases p <;> simp only [plainOutput,liftBinaryTable,relabel_proposalView] <;> rfl
    rw [localRule,same]
    by_cases own : boolProcess decision = p
    · rw [own]
      exact readProposal_own fallback x gs (by omega) p
    · have other : boolProcess decision = p.other := by
        cases p <;> cases eq : boolProcess decision <;> simp_all [Proc.other]
      have differs : plainOutput table p (currentView p (proposalHistory binaryIds gs)) ≠ binaryIds p := by
        rw [same]
        intro eq
        apply own
        rw [eq]
        cases p <;> rfl
      have received := binary_choice_received table A R correct gs len live p differs
      rw [← silentAge_proposals x binaryIds gs p] at received
      rw [other]
      exact readProposal_other fallback x gs p (by omega)
  change _ = _ ∧ (_ = x .one ∨ _ = x .two)
  simp only [outputs]
  refine ⟨True.intro,?_⟩
  cases eq : boolProcess decision
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ProposalTableCorrect.solves (table : StrategyPair V V V V)
    (A : Set (Nat → Graph)) (R : Nat) (positive : 0 < R)
    (correct : ProposalTableCorrect table A R) : SolvesBy (retainTable R table) A R := by
  apply retainTable_solves R positive table A
  intro env admitted
  exact correct (proposals env) (graphPrefix (fun t => (env t).graph) R)
    (by simp [graphPrefix]) ⟨(fun t => (env t).graph),admitted,by simp [graphPrefix_length]⟩

variable (M : DetParityAutomaton Graph) [DecidableEq M.State]

theorem checkState_proposalCorrect (q : M.State) (R : Nat) (success : checkState M q R = true) :
    ∃ table : StrategyPair Bool Bool Bool Bool, ProposalTableCorrect table (stateLanguage M q) R := by
  obtain ⟨table,correct⟩ := (checkState_exact M q R).mp success
  refine ⟨table,fun x gs len live => ?_⟩
  let c : TestCase R := ⟨x,⟨gs,len⟩⟩
  have stateLive : liveState M ((prefixRecognizer M).evalFrom q gs) = true := by
    obtain ⟨word,admitted,pref⟩ := live
    apply (liveState_correct M _).mpr
    refine ⟨OmegaWord.drop word gs.length,?_⟩
    rw [← pref,prefixRecognizer_eval]
    simpa only [graphPrefix_length] using (M.acceptsFrom_runFrom_drop_iff q word gs.length).mpr admitted
  exact correct c stateLive

/-- A successful binary finite test gives genuine consensus for every
nonempty proposal alphabet at exactly the same R. Finiteness is not needed
for this conversion. -/
theorem solves_general_of_checkState [Nonempty V] (q : M.State) (R : Nat) (positive : 0 < R)
    (success : checkState M q R = true) :
    ∃ σ : StrategyPair V V (Option V) (Option V), SolvesBy σ (stateLanguage M q) R := by
  classical
  obtain ⟨table,correct⟩ := checkState_proposalCorrect M q R success
  let fallback : V := Classical.choice inferInstance
  exact ⟨retainTable R (liftBinaryTable fallback table),
    (liftBinaryTable_correct fallback table (stateLanguage M q) R positive correct).solves _ _ _ positive⟩

end Characterisation.ComponentGames.Consensus
