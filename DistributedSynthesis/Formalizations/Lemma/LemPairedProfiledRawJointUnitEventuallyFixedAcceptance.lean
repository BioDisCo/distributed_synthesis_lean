/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPersistentStrictAcceptance

/-!
# Eventually fixed strict Unit tails

An eventually fixed strict execution has only finitely many maximal blocks.
To reuse the persistent strict carrier without assuming another physical
reversal, we extend the environment after the first permanently fixed block
by a proof-only alternating graph suffix.  The extension agrees with the
actual execution through that block's entry cut.  Causality therefore
transports both the concrete Unit control and the original checker state back
to the actual execution, whose remaining fixed tail is one of the certified
one-sided words.
-/

namespace DistributedSynthesis

universe u v x y s

/-! ## Graph and cut facts -/

/-- The canonical operational cuts grow at least as quickly as the identity. -/
theorem le_operationalCloseCuts
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs) :
    ∀ k : Nat, k ≤ operationalCloseCuts graphs hterm k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := operationalCloseCuts_strictMono graphs hterm
        (Nat.lt_succ_self k)
      simp only [Nat.succ_eq_add_one] at hstep ⊢
      omega

/-- Every graph-change position is one of the canonical operational cuts. -/
theorem exists_operationalCloseCut_eq_of_graph_ne_previous
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    {n : Nat} (hn : 0 < n) (hchange : graphs n ≠ graphs (n - 1)) :
    ∃ k : Nat, operationalCloseCuts graphs hterm k = n := by
  let cuts := operationalCloseCuts graphs hterm
  have hexists : ∃ k : Nat, n ≤ cuts k :=
    ⟨n, le_operationalCloseCuts graphs hterm n⟩
  let k := Nat.find hexists
  have hkUpper : n ≤ cuts k := Nat.find_spec hexists
  have hkPos : 0 < k := by
    by_contra hnot
    have hkZero : k = 0 := by omega
    have : n ≤ 0 := by simpa [cuts, hkZero] using hkUpper
    omega
  let j := k - 1
  have hjk : j + 1 = k := by
    dsimp only [j]
    omega
  have hjLower : cuts j < n := by
    by_contra hnot
    have hnle : n ≤ cuts j := by omega
    exact (Nat.find_min hexists (show j < k by omega)) hnle
  have hlePred : cuts j ≤ n - 1 := by omega
  have hnPredLt : n - 1 < cuts k := by omega
  have hnext :
      operationalCloseNext graphs hterm (cuts j) = cuts k := by
    change operationalCloseNext graphs hterm
        (operationalCloseCuts graphs hterm j) =
      operationalCloseCuts graphs hterm k
    rw [← hjk]
    rfl
  by_cases heq : cuts k = n
  · exact ⟨k, heq⟩
  · have hnLt : n < cuts k := by omega
    have hpred := operationalCloseNext_graph_eq_of_mem graphs hterm
      hlePred (by simpa only [hnext] using hnPredLt)
    have hnow := operationalCloseNext_graph_eq_of_mem graphs hterm
      (show cuts j ≤ n by omega) (by simpa only [hnext] using hnLt)
    exact False.elim (hchange (hnow.trans hpred.symm))

/-- Keep a finite environment prefix and append an alternating strict graph
tail.  Inputs are never changed. -/
def alternatingStrictExtension
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (cut : Nat) :
    EnvironmentSequence In₁ In₂ :=
  fun n ↦
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := if n ≤ cut then (env n).graph
        else if n % 2 = 0 then .right else .left }

@[simp] theorem alternatingStrictExtension_eq_of_le
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (cut n : Nat)
    (hn : n ≤ cut) :
    alternatingStrictExtension env cut n = env n := by
  apply EnvironmentRound.equivProd.injective
  simp [alternatingStrictExtension, hn]

/-- The appended alternating tail contains both strict directions
arbitrarily late. -/
theorem alternatingStrictExtension_bothStrictDirectionsRecurrent
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (cut : Nat) :
    BothStrictDirectionsRecurrent
      (fun n ↦ (alternatingStrictExtension env cut n).graph) := by
  constructor
  · intro start
    let t := start + cut + 1
    refine ⟨2 * t + 1, ?_, ?_⟩
    · dsimp only [t]
      omega
    · have hcut : ¬ 2 * t + 1 ≤ cut := by
        dsimp only [t]
        omega
      simp [alternatingStrictExtension, hcut]
  · intro start
    let t := start + cut + 1
    refine ⟨2 * t, ?_, ?_⟩
    · dsimp only [t]
      omega
    · have hcut : ¬ 2 * t ≤ cut := by
        dsimp only [t]
        omega
      simp [alternatingStrictExtension, hcut]

/-- If the retained prefix has no simultaneous graph, neither does the
alternating extension. -/
theorem alternatingStrictExtension_ne_both
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (cut : Nat)
    (hnoboth : ∀ n : Nat, (env n).graph ≠ .both) :
    ∀ n : Nat, (alternatingStrictExtension env cut n).graph ≠ .both := by
  intro n
  by_cases hn : n ≤ cut
  · simpa [alternatingStrictExtension, hn] using hnoboth n
  · by_cases heven : n % 2 = 0 <;>
      simp [alternatingStrictExtension, hn, heven]

/-- An eventually-right word has a first permanently-right position, which
is either zero or a genuine graph change. -/
theorem exists_first_eventuallyStrictRight
    {graphs : Nat → Graph} (h : EventuallyStrictRight graphs) :
    ∃ cut : Nat,
      (∀ n : Nat, cut ≤ n → graphs n = .right) ∧
        (cut = 0 ∨ graphs cut ≠ graphs (cut - 1)) := by
  classical
  let P : Nat → Prop := fun cut ↦
    ∀ n : Nat, cut ≤ n → graphs n = .right
  have hexists : ∃ cut : Nat, P cut := h
  let cut := Nat.find hexists
  have htail : P cut := Nat.find_spec hexists
  refine ⟨cut, htail, ?_⟩
  by_cases hzero : cut = 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    have hcutRight : graphs cut = .right := htail cut (Nat.le_refl cut)
    intro heq
    have hpredRight : graphs (cut - 1) = .right := heq.symm.trans hcutRight
    have hpredTail : P (cut - 1) := by
      intro n hn
      rcases Nat.eq_or_lt_of_le hn with heqPred | hlt
      · simpa [heqPred] using hpredRight
      · apply htail n
        omega
    exact (Nat.find_min hexists (show cut - 1 < cut by omega)) hpredTail

/-- First permanently-left mirror. -/
theorem exists_first_eventuallyStrictLeft
    {graphs : Nat → Graph} (h : EventuallyStrictLeft graphs) :
    ∃ cut : Nat,
      (∀ n : Nat, cut ≤ n → graphs n = .left) ∧
        (cut = 0 ∨ graphs cut ≠ graphs (cut - 1)) := by
  classical
  let P : Nat → Prop := fun cut ↦
    ∀ n : Nat, cut ≤ n → graphs n = .left
  have hexists : ∃ cut : Nat, P cut := h
  let cut := Nat.find hexists
  have htail : P cut := Nat.find_spec hexists
  refine ⟨cut, htail, ?_⟩
  by_cases hzero : cut = 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    have hcutLeft : graphs cut = .left := htail cut (Nat.le_refl cut)
    intro heq
    have hpredLeft : graphs (cut - 1) = .left := heq.symm.trans hcutLeft
    have hpredTail : P (cut - 1) := by
      intro n hn
      rcases Nat.eq_or_lt_of_le hn with heqPred | hlt
      · simpa [heqPred] using hpredLeft
      · apply htail n
        omega
    exact (Nat.find_min hexists (show cut - 1 < cut by omega)) hpredTail

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

private abbrev UnitKernel
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-! ## Fixed-tail endpoints for both cut-carrier shapes -/

/-- Inputs of a physical suffix, ordered for the right-controller play. -/
def profiledRawJointUnitRightInputsAfter
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₂ × In₁ :=
  fun n ↦ ((physicalEnv (start + n)).inputTwo,
    (physicalEnv (start + n)).inputOne)

/-- Inputs of a physical suffix, ordered for the left-controller play. -/
def profiledRawJointUnitLeftInputsAfter
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₁ × In₂ :=
  fun n ↦ ((physicalEnv (start + n)).inputOne,
    (physicalEnv (start + n)).inputTwo)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- An all-right graph suffix is literally the right-controller
environment built from its physical inputs. -/
theorem profiledRawJointUnit_drop_eq_strictRightEnvironment
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (hgraph : ∀ n, start ≤ n → (physicalEnv n).graph = .right) :
    OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictRightEnvironment
        (profiledRawJointUnitRightInputsAfter physicalEnv start) := by
  funext n
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simpa [OmegaWord.drop,
        profiledRawJointUnitStrictRightEnvironment] using
        hgraph (start + n) (by omega)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- All-left mirror. -/
theorem profiledRawJointUnit_drop_eq_strictLeftEnvironment
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (hgraph : ∀ n, start ≤ n → (physicalEnv n).graph = .left) :
    OmegaWord.drop physicalEnv start =
      profiledRawJointUnitStrictLeftEnvironment
        (profiledRawJointUnitLeftInputsAfter physicalEnv start) := by
  funext n
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simpa [OmegaWord.drop,
        profiledRawJointUnitStrictLeftEnvironment] using
        hgraph (start + n) (by omega)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A completed matched-left carrier selected again by `.right` has the
certified right omega word of its stored target. -/
theorem profiledRawJointUnitMatchedLeft_strictRight_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    A.AcceptsFrom
      (pairedCodeStateForRow A left.2.1
        (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
          policy bank left).slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left owner oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment env)) := by
  rw [profiledRawJointUnitMatchedLeft_right_traceWord]
  cases hrow : left.2.1 with
  | first =>
      simpa [pairedCodeStateForRow, hrow] using
        (bank.right_physical_acceptsFrom A
          (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
            policy bank left) .first env)
  | both =>
      simpa [pairedCodeStateForRow, hrow] using
        (bank.right_physical_acceptsFrom A
          (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
            policy bank left) .both env)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A completed matched-right carrier selected again by `.left` has the
certified left omega word of its stored target. -/
theorem profiledRawJointUnitMatchedRight_strictLeft_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    A.AcceptsFrom
      (pairedCodeStateForRow A right.2.1
        (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
          policy bank right).slot.1.1)
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter owner right oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment env)) := by
  rw [profiledRawJointUnitMatchedRight_left_traceWord]
  cases hrow : right.2.1 with
  | first =>
      simpa [pairedCodeStateForRow, hrow] using
        (bank.left_physical_acceptsFrom A
          (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
            policy bank right) .first env)
  | both =>
      simpa [pairedCodeStateForRow, hrow] using
        (bank.left_physical_acceptsFrom A
          (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
            policy bank right) .both env)

/-! ## Transport through a proof-only persistent extension -/

/-- The cut-carrier shape at physical offset zero, stated independently of a
termination proof so it can be transported to a proof-only extension. -/
def ProfiledRawJointUnitStrictControlAtZero
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (row : PairedEntryRow)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) : Prop :=
  match seed with
  | .inl source =>
      (physicalEnv 0).graph = .right ∧
        ((∃ outputOne outputTwo,
            origin = profiledRawJointUnitFreshMatchedRightState A strategy
              initial policy bank adapter source row outputOne outputTwo) ∨
          ∃ left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
              initial policy,
            ∃ owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
              initial policy bank,
            ∃ outputOne outputTwo,
              origin = profiledRawJointUnitMatchedLeftState A strategy initial
                policy bank adapter left owner outputOne outputTwo ∧
              profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
                policy bank left = source ∧
              left.2.1 = row)
  | .inr source =>
      (physicalEnv 0).graph = .left ∧
        ((∃ outputOne outputTwo,
            origin = profiledRawJointUnitFreshMatchedLeftState A strategy
              initial policy bank adapter source row outputOne outputTwo) ∨
          ∃ owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
              initial policy bank,
            ∃ right : ProfiledRawJointUnitRightPolicyReceiverControl A
              strategy initial policy,
            ∃ outputOne outputTwo,
              origin = profiledRawJointUnitMatchedRightState A strategy initial
                policy bank adapter owner right outputOne outputTwo ∧
              profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
                policy bank right = source ∧
              right.2.1 = row)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- A zero shape becomes the canonical persistent carrier for any extension
with the same first physical round. -/
theorem ProfiledRawJointUnitStrictControlAtZero.toPersistent
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State}
    {physicalEnv extension : EnvironmentSequence In₁ In₂}
    {row : PairedEntryRow}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (zero : ProfiledRawJointUnitStrictControlAtZero A strategy initial policy
      bank adapter origin physicalEnv row seed)
    (hfirst : extension 0 = physicalEnv 0)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail extension 0)) :
    ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy
      bank adapter origin extension hterm row seed 0 := by
  cases seed with
  | inl source =>
      change (extension 0).graph = .right ∧ _
      change (physicalEnv 0).graph = .right ∧ _ at zero
      simpa [hfirst] using zero
  | inr source =>
      change (extension 0).graph = .left ∧ _
      change (physicalEnv 0).graph = .left ∧ _ at zero
      simpa [hfirst] using zero

/-- State-relative acceptance when an aligned all-strict Unit execution is
eventually fixed to `.right`.  The finite switching prefix is discharged by
the persistent carrier on a proof-only alternating extension. -/
theorem profiledRawJointUnit_eventuallyStrictRight_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (zero : ProfiledRawJointUnitStrictControlAtZero A strategy initial policy
      bank adapter origin physicalEnv .first seed)
    (physicalState : A.State)
    (hphysicalState : physicalState =
      seed.entryStateForRow A strategy initial policy .first)
    (hnoboth : ∀ n : Nat, (physicalEnv n).graph ≠ .both)
    (heventual : EventuallyStrictRight (fun n ↦ (physicalEnv n).graph)) :
    let kernel := UnitKernel A strategy initial policy bank adapter
    A.AcceptsFrom physicalState
      ((kernel.globalMachine.reroot origin).globalMachineTraceWord
        kernel.globalOutputOne kernel.globalOutputTwo physicalEnv) := by
  dsimp only
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  let R := G.reroot origin
  let outputOne :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
  let outputTwo :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
  rcases exists_first_eventuallyStrictRight heventual with
    ⟨cut, htailGraph, hcutShape⟩
  let extension := alternatingStrictExtension physicalEnv cut
  have hrecurrent :=
    alternatingStrictExtension_bothStrictDirectionsRecurrent physicalEnv cut
  have hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail extension 0) := by
    change OperationalStrictRunsTerminate (fun n ↦ (extension (0 + n)).graph)
    simpa only [Nat.zero_add] using
      operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
        hrecurrent
  have hnoBothExtension : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail extension 0 n ≠ .both := by
    intro n
    simpa [profiledRawJointPhysicalGraphTail, extension] using
      alternatingStrictExtension_ne_both physicalEnv cut hnoboth n
  have hfirst : extension 0 = physicalEnv 0 := by
    exact alternatingStrictExtension_eq_of_le physicalEnv cut 0 (Nat.zero_le _)
  have zeroExtension :
      ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy
        bank adapter origin extension hterm .first seed 0 :=
    zero.toPersistent A strategy initial policy bank hfirst hterm
  let graphs := profiledRawJointPhysicalGraphTail extension 0
  let cuts := operationalCloseCuts graphs hterm
  have hcutIndex : ∃ k : Nat, cuts k = cut := by
    rcases hcutShape with hzero | hchange
    · exact ⟨0, by simp [cuts, hzero]⟩
    · have hchangeExtension : graphs cut ≠ graphs (cut - 1) := by
        have hcutLe : cut ≤ cut := Nat.le_refl cut
        have hpredLe : cut - 1 ≤ cut := Nat.sub_le cut 1
        simpa [graphs, profiledRawJointPhysicalGraphTail, extension,
          alternatingStrictExtension_eq_of_le physicalEnv cut cut hcutLe,
          alternatingStrictExtension_eq_of_le physicalEnv cut (cut - 1)
            hpredLe] using hchange
      exact exists_operationalCloseCut_eq_of_graph_ne_previous graphs hterm
        (by
          by_contra hnot
          have : cut = 0 := by omega
          subst cut
          exact hchange rfl)
        hchangeExtension
  rcases hcutIndex with ⟨k, hk⟩
  have carrierAt := zeroExtension.all A strategy initial policy bank
    hnoBothExtension
  have carrier := carrierAt k
  let root := profiledRawJointUnitPersistentStrictRootAt A strategy initial
    policy bank extension hterm .first seed k
  have carrierShape :
      match root with
      | .inl source => graphs (cuts k) = .right ∧
          ((∃ outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitFreshMatchedRightState A strategy initial
                  policy bank adapter source .first outputOne outputTwo) ∨
            ∃ left owner outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitMatchedLeftState A strategy initial policy
                  bank adapter left owner outputOne outputTwo ∧
              profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
                policy bank left = source ∧
              left.2.1 = .first)
      | .inr source => graphs (cuts k) = .left ∧
          ((∃ outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitFreshMatchedLeftState A strategy initial
                  policy bank adapter source .first outputOne outputTwo) ∨
            ∃ owner right outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitMatchedRightState A strategy initial policy
                  bank adapter owner right outputOne outputTwo ∧
              profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
                policy bank right = source ∧
              right.2.1 = .first) := by
    simpa [ProfiledRawJointUnitPersistentStrictControlAt, root, graphs, cuts,
      R, G] using carrier
  have checkerAt :=
    profiledRawJointUnitPersistentStrict_checkerStateAt A strategy initial
      policy bank adapter origin extension hterm seed hnoBothExtension
        zeroExtension physicalState hphysicalState
  let extensionWord :=
    R.globalMachineTraceWord outputOne outputTwo extension
  let physicalWord :=
    R.globalMachineTraceWord outputOne outputTwo physicalEnv
  have hprefix : ∀ n : Nat, n < cut → extension n = physicalEnv n := by
    intro n hn
    exact alternatingStrictExtension_eq_of_le physicalEnv cut n (by omega)
  have hcontrolPrefix :
      R.globalStateTrace extension cut =
        R.globalStateTrace physicalEnv cut :=
    R.globalStateTrace_eq_of_forall_lt extension physicalEnv cut hprefix
  have hwordPrefix : omegaPrefix extensionWord cut =
      omegaPrefix physicalWord cut := by
    exact R.omegaPrefix_globalMachineTraceWord_eq_of_forall_lt outputOne
      outputTwo extension physicalEnv cut hprefix
  have hrunPrefix :
      A.runFrom physicalState extensionWord cut =
        A.runFrom physicalState physicalWord cut := by
    rw [runFrom_eq_omegaPrefix_foldl A physicalState extensionWord cut,
      runFrom_eq_omegaPrefix_foldl A physicalState physicalWord cut,
      hwordPrefix]
  have hcheckerExtension :
      A.runFrom physicalState extensionWord cut =
        root.entryStateForRow A strategy initial policy .first := by
    simpa [extensionWord, cuts, graphs, root, hk] using checkerAt k
  have hcheckerPhysical :
      A.runFrom physicalState physicalWord cut =
        root.entryStateForRow A strategy initial policy .first :=
    hrunPrefix.symm.trans hcheckerExtension
  have hgraphCut : graphs cut = .right := by
    simpa [graphs, profiledRawJointPhysicalGraphTail, extension,
      alternatingStrictExtension_eq_of_le physicalEnv cut cut (Nat.le_refl _)]
      using htailGraph cut (Nat.le_refl cut)
  cases hroot : root with
  | inl source =>
      rw [hroot] at carrierShape
      rcases carrierShape with ⟨_hgraph, hshape⟩
      have hstate : A.runFrom physicalState physicalWord cut =
          pairedCodeStateForRow A .first source.slot.1.1 := by
        simpa [hroot, root,
          ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow] using
          hcheckerPhysical
      let env := profiledRawJointUnitRightInputsAfter physicalEnv cut
      have henv : OmegaWord.drop physicalEnv cut =
          profiledRawJointUnitStrictRightEnvironment env := by
        exact profiledRawJointUnit_drop_eq_strictRightEnvironment physicalEnv
          cut htailGraph
      have hsuffix : A.AcceptsFrom
          (A.runFrom physicalState physicalWord cut)
          (OmegaWord.drop physicalWord cut) := by
        rw [hstate]
        have hreroot := R.reroot_globalMachineTraceWord_drop outputOne
          outputTwo physicalEnv cut
        rw [← hreroot]
        rcases hshape with hfresh | hmatched
        · rcases hfresh with ⟨oldOutputOne, oldOutputTwo, hcontrol⟩
          have hcontrolPhysical : R.globalStateTrace physicalEnv cut =
              profiledRawJointUnitFreshMatchedRightState A strategy initial
                policy bank adapter source .first oldOutputOne oldOutputTwo :=
            hcontrolPrefix.symm.trans (by simpa [cuts, graphs, hk] using hcontrol)
          rw [hcontrolPhysical, henv]
          exact profiledRawJointUnitFreshMatchedRight_acceptsFrom A strategy
            initial policy bank adapter source .first oldOutputOne oldOutputTwo
              env
        · rcases hmatched with
            ⟨left, owner, oldOutputOne, oldOutputTwo, hcontrol, htarget,
              hrow⟩
          have hcontrolPhysical : R.globalStateTrace physicalEnv cut =
              profiledRawJointUnitMatchedLeftState A strategy initial policy
                bank adapter left owner oldOutputOne oldOutputTwo :=
            hcontrolPrefix.symm.trans (by simpa [cuts, graphs, hk] using hcontrol)
          rw [hcontrolPhysical, henv, ← htarget, ← hrow]
          exact profiledRawJointUnitMatchedLeft_strictRight_acceptsFrom A
            strategy initial policy bank adapter left owner oldOutputOne
              oldOutputTwo env
      exact (A.acceptsFrom_runFrom_drop_iff physicalState physicalWord cut).mp
        hsuffix
  | inr source =>
      rw [hroot] at carrierShape
      have hleft : graphs (cuts k) = .left := carrierShape.1
      rw [hk, hgraphCut] at hleft
      exact Graph.noConfusion hleft

/-- State-relative acceptance when an aligned all-strict Unit execution is
eventually fixed to `.left`. -/
theorem profiledRawJointUnit_eventuallyStrictLeft_acceptsFrom
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (origin :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.State)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (zero : ProfiledRawJointUnitStrictControlAtZero A strategy initial policy
      bank adapter origin physicalEnv .first seed)
    (physicalState : A.State)
    (hphysicalState : physicalState =
      seed.entryStateForRow A strategy initial policy .first)
    (hnoboth : ∀ n : Nat, (physicalEnv n).graph ≠ .both)
    (heventual : EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph)) :
    let kernel := UnitKernel A strategy initial policy bank adapter
    A.AcceptsFrom physicalState
      ((kernel.globalMachine.reroot origin).globalMachineTraceWord
        kernel.globalOutputOne kernel.globalOutputTwo physicalEnv) := by
  dsimp only
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  let R := G.reroot origin
  let outputOne :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
  let outputTwo :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
  rcases exists_first_eventuallyStrictLeft heventual with
    ⟨cut, htailGraph, hcutShape⟩
  let extension := alternatingStrictExtension physicalEnv cut
  have hrecurrent :=
    alternatingStrictExtension_bothStrictDirectionsRecurrent physicalEnv cut
  have hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail extension 0) := by
    change OperationalStrictRunsTerminate (fun n ↦ (extension (0 + n)).graph)
    simpa only [Nat.zero_add] using
      operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
        hrecurrent
  have hnoBothExtension : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail extension 0 n ≠ .both := by
    intro n
    simpa [profiledRawJointPhysicalGraphTail, extension] using
      alternatingStrictExtension_ne_both physicalEnv cut hnoboth n
  have hfirst : extension 0 = physicalEnv 0 := by
    exact alternatingStrictExtension_eq_of_le physicalEnv cut 0 (Nat.zero_le _)
  have zeroExtension :
      ProfiledRawJointUnitPersistentStrictControlAt A strategy initial policy
        bank adapter origin extension hterm .first seed 0 :=
    zero.toPersistent A strategy initial policy bank hfirst hterm
  let graphs := profiledRawJointPhysicalGraphTail extension 0
  let cuts := operationalCloseCuts graphs hterm
  have hcutIndex : ∃ k : Nat, cuts k = cut := by
    rcases hcutShape with hzero | hchange
    · exact ⟨0, by simp [cuts, hzero]⟩
    · have hchangeExtension : graphs cut ≠ graphs (cut - 1) := by
        have hcutLe : cut ≤ cut := Nat.le_refl cut
        have hpredLe : cut - 1 ≤ cut := Nat.sub_le cut 1
        simpa [graphs, profiledRawJointPhysicalGraphTail, extension,
          alternatingStrictExtension_eq_of_le physicalEnv cut cut hcutLe,
          alternatingStrictExtension_eq_of_le physicalEnv cut (cut - 1)
            hpredLe] using hchange
      exact exists_operationalCloseCut_eq_of_graph_ne_previous graphs hterm
        (by
          by_contra hnot
          have : cut = 0 := by omega
          subst cut
          exact hchange rfl)
        hchangeExtension
  rcases hcutIndex with ⟨k, hk⟩
  have carrierAt := zeroExtension.all A strategy initial policy bank
    hnoBothExtension
  have carrier := carrierAt k
  let root := profiledRawJointUnitPersistentStrictRootAt A strategy initial
    policy bank extension hterm .first seed k
  have carrierShape :
      match root with
      | .inl source => graphs (cuts k) = .right ∧
          ((∃ outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitFreshMatchedRightState A strategy initial
                  policy bank adapter source .first outputOne outputTwo) ∨
            ∃ left owner outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitMatchedLeftState A strategy initial policy
                  bank adapter left owner outputOne outputTwo ∧
              profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
                policy bank left = source ∧
              left.2.1 = .first)
      | .inr source => graphs (cuts k) = .left ∧
          ((∃ outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitFreshMatchedLeftState A strategy initial
                  policy bank adapter source .first outputOne outputTwo) ∨
            ∃ owner right outputOne outputTwo,
              R.globalStateTrace extension (cuts k) =
                profiledRawJointUnitMatchedRightState A strategy initial policy
                  bank adapter owner right outputOne outputTwo ∧
              profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
                policy bank right = source ∧
              right.2.1 = .first) := by
    simpa [ProfiledRawJointUnitPersistentStrictControlAt, root, graphs, cuts,
      R, G] using carrier
  have checkerAt :=
    profiledRawJointUnitPersistentStrict_checkerStateAt A strategy initial
      policy bank adapter origin extension hterm seed hnoBothExtension
        zeroExtension physicalState hphysicalState
  let extensionWord :=
    R.globalMachineTraceWord outputOne outputTwo extension
  let physicalWord :=
    R.globalMachineTraceWord outputOne outputTwo physicalEnv
  have hprefix : ∀ n : Nat, n < cut → extension n = physicalEnv n := by
    intro n hn
    exact alternatingStrictExtension_eq_of_le physicalEnv cut n (by omega)
  have hcontrolPrefix :
      R.globalStateTrace extension cut =
        R.globalStateTrace physicalEnv cut :=
    R.globalStateTrace_eq_of_forall_lt extension physicalEnv cut hprefix
  have hwordPrefix : omegaPrefix extensionWord cut =
      omegaPrefix physicalWord cut := by
    exact R.omegaPrefix_globalMachineTraceWord_eq_of_forall_lt outputOne
      outputTwo extension physicalEnv cut hprefix
  have hrunPrefix :
      A.runFrom physicalState extensionWord cut =
        A.runFrom physicalState physicalWord cut := by
    rw [runFrom_eq_omegaPrefix_foldl A physicalState extensionWord cut,
      runFrom_eq_omegaPrefix_foldl A physicalState physicalWord cut,
      hwordPrefix]
  have hcheckerExtension :
      A.runFrom physicalState extensionWord cut =
        root.entryStateForRow A strategy initial policy .first := by
    simpa [extensionWord, cuts, graphs, root, hk] using checkerAt k
  have hcheckerPhysical :
      A.runFrom physicalState physicalWord cut =
        root.entryStateForRow A strategy initial policy .first :=
    hrunPrefix.symm.trans hcheckerExtension
  have hgraphCut : graphs cut = .left := by
    simpa [graphs, profiledRawJointPhysicalGraphTail, extension,
      alternatingStrictExtension_eq_of_le physicalEnv cut cut (Nat.le_refl _)]
      using htailGraph cut (Nat.le_refl cut)
  cases hroot : root with
  | inl source =>
      rw [hroot] at carrierShape
      have hright : graphs (cuts k) = .right := carrierShape.1
      rw [hk, hgraphCut] at hright
      exact Graph.noConfusion hright
  | inr source =>
      rw [hroot] at carrierShape
      rcases carrierShape with ⟨_hgraph, hshape⟩
      have hstate : A.runFrom physicalState physicalWord cut =
          pairedCodeStateForRow A .first source.slot.1.1 := by
        simpa [hroot, root,
          ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow] using
          hcheckerPhysical
      let env := profiledRawJointUnitLeftInputsAfter physicalEnv cut
      have henv : OmegaWord.drop physicalEnv cut =
          profiledRawJointUnitStrictLeftEnvironment env := by
        exact profiledRawJointUnit_drop_eq_strictLeftEnvironment physicalEnv
          cut htailGraph
      have hsuffix : A.AcceptsFrom
          (A.runFrom physicalState physicalWord cut)
          (OmegaWord.drop physicalWord cut) := by
        rw [hstate]
        have hreroot := R.reroot_globalMachineTraceWord_drop outputOne
          outputTwo physicalEnv cut
        rw [← hreroot]
        rcases hshape with hfresh | hmatched
        · rcases hfresh with ⟨oldOutputOne, oldOutputTwo, hcontrol⟩
          have hcontrolPhysical : R.globalStateTrace physicalEnv cut =
              profiledRawJointUnitFreshMatchedLeftState A strategy initial
                policy bank adapter source .first oldOutputOne oldOutputTwo :=
            hcontrolPrefix.symm.trans (by simpa [cuts, graphs, hk] using hcontrol)
          rw [hcontrolPhysical, henv]
          exact profiledRawJointUnitFreshMatchedLeft_acceptsFrom A strategy
            initial policy bank adapter source .first oldOutputOne oldOutputTwo
              env
        · rcases hmatched with
            ⟨owner, right, oldOutputOne, oldOutputTwo, hcontrol, htarget,
              hrow⟩
          have hcontrolPhysical : R.globalStateTrace physicalEnv cut =
              profiledRawJointUnitMatchedRightState A strategy initial policy
                bank adapter owner right oldOutputOne oldOutputTwo :=
            hcontrolPrefix.symm.trans (by simpa [cuts, graphs, hk] using hcontrol)
          rw [hcontrolPhysical, henv, ← htarget, ← hrow]
          exact profiledRawJointUnitMatchedRight_strictLeft_acceptsFrom A
            strategy initial policy bank adapter owner right oldOutputOne
              oldOutputTwo env
      exact (A.acceptsFrom_runFrom_drop_iff physicalState physicalWord cut).mp
        hsuffix

end

end

end DetParityAutomaton

end DistributedSynthesis
