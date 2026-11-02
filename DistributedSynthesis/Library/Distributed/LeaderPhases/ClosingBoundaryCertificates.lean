/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingComponents

/-! Finite certificates for a complete, renumbered closing component. The
checker rejects missing histories and duplicate slots. It needs coverage of
the selected target component in the closing layer. Covering entire source
components is a sufficient specialization, not a necessary hypothesis. -/
namespace Characterisation
open DistributedSynthesis

def checkClosingEnumeration {S T : Type} [Fintype S] [Fintype T]
    [DecidableEq T] (mask : T → Bool) (keep : S → T) : Bool :=
  decide (Function.Injective keep ∧ ∀ t, mask t = true ↔ ∃ s, keep s = t)

theorem checkClosingEnumeration_correct {S T I₁ I₂ : Type}
    [Fintype S] [Fintype T] [DecidableEq T]
    (P : List Graph → Prop) (past : T → EnvHistory I₁ I₂)
    (injective : Function.Injective past) (root : T) (mask : T → Bool)
    (exactMask : ∀ t, mask t = true ↔ InputConnected P (past root) (past t))
    (covers : ∀ k, InputConnected P (past root) k → ∃ t, past t = k)
    (keep : S → T) :
    checkClosingEnumeration mask keep = true ↔
      Function.Injective (past ∘ keep) ∧
      ∀ k, InputConnected P (past root) k ↔ ∃ s, past (keep s) = k := by
  simp only [checkClosingEnumeration,decide_eq_true_eq]
  constructor
  · rintro ⟨unique,complete⟩
    refine ⟨injective.comp unique,fun k => ⟨?_,?_⟩⟩
    · intro conn
      obtain ⟨t,eq⟩ := covers k conn
      obtain ⟨s,hs⟩ := (complete t).mp ((exactMask t).mpr (by simpa only [eq] using conn))
      exact ⟨s,by simpa only [hs] using eq⟩
    · rintro ⟨s,rfl⟩
      exact (exactMask _).mp ((complete _).mpr ⟨s,rfl⟩)
  · rintro ⟨unique,complete⟩
    refine ⟨fun s t eq => unique (congrArg past eq),fun t => ⟨?_,?_⟩⟩
    · intro member
      obtain ⟨s,eq⟩ := (complete (past t)).mp ((exactMask t).mp member)
      exact ⟨s,injective eq⟩
    · rintro ⟨s,rfl⟩
      exact (exactMask _).mpr ((complete _).mpr ⟨s,rfl⟩)

/-- A fixed finite alphabet contains all candidate renumbered targets and
their bounded response policies. Legality is checked separately. -/
abbrev ClosingBoundaryCertificate (H I₁ I₂ O₁ O₂ Q : Type) (B D n : Nat) :=
  Σ size : Fin (B+1), ClosingMove H (Fin size.val) I₁ I₂ O₁ O₂ Q D n

instance closingBoundaryCertificate_fintype {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] (B D n : Nat) :
    Fintype (ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n) := by
  unfold ClosingBoundaryCertificate
  infer_instance

/-- In addition to checking the outputs and the target annotations, check
that the target contains exactly one slot for every history of the selected
live component. Source labels and the live mask remain explicit inputs. -/
def checkClosingBoundaryCertificate {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    (shape : InputShape H)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {B D n : Nat} (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n)
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n) : Bool :=
  checkClosingMove shape step initial move.2.1 bound move.2.2.1 move.2.2.2
      (fun target => Allowed ⟨move.1,target⟩) &&
    checkClosingEnumeration (closingComponentMask (closingLayerShape shape n) live root) move.2.2.1

/-- Exact semantics of the finite certificate check. Complete component
coverage is a conclusion about the target, justified by target coverage in the layer.
The allowed-target condition alone would not establish this conclusion. -/
theorem checkClosingBoundaryCertificate_correct_of_target_coverage {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop)
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {B D n : Nat} (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root)))
    (covers : ∀ k, InputConnected P (closingLayerHistory past n root) k →
      ∃ s, closingLayerHistory past n s = k)
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n) :
    let out := move.2.1
    let keep := move.2.2.1
    let target := move.2.2.2
    checkClosingBoundaryCertificate shape step initial bound live root Allowed move = true ↔
      ((∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ t s,
          σ.one (currentView .one (closingLayerHistory past (t.val+1) s)) = (out t s).1 ∧
          σ.two (currentView .two (closingLayerHistory past (t.val+1) s)) = (out t s).2) ∧
        (RepresentsInputShape (closingLayerHistory past n ∘ keep) target.1 ∧
          ∀ s, target.2 s =
            (closingLayerTrace out n bound (keep s)).foldl (fun q letter => step q letter.1 letter.2)
              (initial (closingLayerRoot n (keep s)))) ∧ Allowed ⟨move.1,target⟩) ∧
      (Function.Injective (closingLayerHistory past n ∘ keep) ∧
        ∀ k, InputConnected P (closingLayerHistory past n root) k ↔
          ∃ s, closingLayerHistory past n (keep s) = k) := by
  dsimp only
  simp only [checkClosingBoundaryCertificate,Bool.and_eq_true]
  rw [checkClosingMove_correct past shape rep L depth step initial]
  rw [checkClosingEnumeration_correct P (closingLayerHistory past n)
    (closingLayerHistory_injective past injective n) root _
    (closingComponentMask_exact P (closingLayerHistory past n) (closingLayerShape shape n)
      (closingLayerShape_exact past shape rep n) live liveExact root rootLive covers) covers]


/-- The original component-closed-source specialization follows from the
more general target-coverage theorem. -/
theorem checkClosingBoundaryCertificate_correct {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (covers : ∀ s k, InputConnected P (past s) k → ∃ t, past t = k)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {B D n : Nat} (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root)))
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n) :
    let out := move.2.1
    let keep := move.2.2.1
    let target := move.2.2.2
    checkClosingBoundaryCertificate shape step initial bound live root Allowed move = true ↔
      ((∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ t s,
          σ.one (currentView .one (closingLayerHistory past (t.val+1) s)) = (out t s).1 ∧
          σ.two (currentView .two (closingLayerHistory past (t.val+1) s)) = (out t s).2) ∧
        (RepresentsInputShape (closingLayerHistory past n ∘ keep) target.1 ∧
          ∀ s, target.2 s =
            (closingLayerTrace out n bound (keep s)).foldl (fun q letter => step q letter.1 letter.2)
              (initial (closingLayerRoot n (keep s)))) ∧ Allowed ⟨move.1,target⟩) ∧
      (Function.Injective (closingLayerHistory past n ∘ keep) ∧
        ∀ k, InputConnected P (closingLayerHistory past n root) k ↔
          ∃ s, closingLayerHistory past n (keep s) = k) := by
  exact checkClosingBoundaryCertificate_correct_of_target_coverage P past injective shape rep L depth
    step initial bound live liveExact root rootLive
    (closingLayer_component_coverage P closed past covers n root) Allowed move

/-- Every coherent bounded response policy has a truthful certificate when
the computed component fits the prescribed bound. The proof reuses the
existing switch-interface representation and component equivalence. -/
theorem exists_checked_closing_boundary_of_target_coverage {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop)
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {B D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (coherent : ClosingPolicyCoherent shape out) (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root)))
    (covers : ∀ k, InputConnected P (closingLayerHistory past n root) k →
      ∃ s, closingLayerHistory past n s = k)
    (small : Nat.card (InputHistoryComponent P (closingLayerHistory past n root)) ≤ B) :
    ∃ move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n,
      move.2.1 = out ∧
      checkClosingBoundaryCertificate shape step initial bound live root (fun _ => True) move = true := by
  classical
  let T := ClosingComponentSlots shape n live root
  let hist : T → EnvHistory I₁ I₂ := fun s => closingLayerHistory past n s.val
  have unique := closingLayerHistory_injective past injective n
  have coverage := covers
  obtain ⟨equiv⟩ := closingComponentMask_equiv P (closingLayerHistory past n) unique
    (closingLayerShape shape n) (closingLayerShape_exact past shape rep n)
    live liveExact root rootLive coverage
  have card : Nat.card T ≤ B := (Nat.card_congr equiv).le.trans small
  obtain ⟨target,e,observations,labels⟩ := finite_switch_interface B card hist
    (fun s : T => closingLayerLabels step initial out n bound s.val)
  let keep : Fin target.1.val → ClosingLayer H I₁ I₂ n := fun i => (e i).val
  let move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n :=
    ⟨target.1,out,keep,target.2⟩
  refine ⟨move,rfl,?_⟩
  change (checkClosingMove shape step initial out bound keep target.2 (fun _ => True) &&
    checkClosingEnumeration (closingComponentMask (closingLayerShape shape n) live root) keep) = true
  rw [Bool.and_eq_true]
  constructor
  · apply (checkClosingMove_correct past shape rep L depth step initial out bound keep target.2 (fun _ => True)).mpr
    refine ⟨(closingPolicyCoherent_iff_local past shape rep L depth out).mp coherent,⟨?_,?_⟩,trivial⟩
    · exact observations
    · intro i
      exact (labels i).trans (closingLayerLabels_replay step initial out n bound (keep i))
  · simp only [checkClosingEnumeration,decide_eq_true_eq]
    refine ⟨Subtype.val_injective.comp e.injective,fun s => ⟨?_,?_⟩⟩
    · intro member
      obtain ⟨i,eq⟩ := e.surjective (⟨s,member⟩ : T)
      exact ⟨i,congrArg Subtype.val eq⟩
    · rintro ⟨i,rfl⟩
      exact (e i).property


/-- Preserve the original API when the source family covers all of its
components. Only coverage of the selected target is needed internally. -/
theorem exists_checked_closing_boundary {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (covers : ∀ s k, InputConnected P (past s) k → ∃ t, past t = k)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {B D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (coherent : ClosingPolicyCoherent shape out) (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past n s)))
    (root : ClosingLayer H I₁ I₂ n)
    (rootLive : P (History.graphSequence (closingLayerHistory past n root)))
    (small : Nat.card (InputHistoryComponent P (closingLayerHistory past n root)) ≤ B) :
    ∃ move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n,
      move.2.1 = out ∧
      checkClosingBoundaryCertificate shape step initial bound live root (fun _ => True) move = true := by
  exact exists_checked_closing_boundary_of_target_coverage P past injective shape rep L depth
    step initial out coherent bound live liveExact root rootLive
    (closingLayer_component_coverage P closed past covers n root) small

end Characterisation
