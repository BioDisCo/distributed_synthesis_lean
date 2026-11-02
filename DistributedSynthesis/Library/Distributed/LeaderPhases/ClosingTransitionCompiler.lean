/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderRootControllers

/-! Compute bounded closing transitions from the existing one-round
observation update. Proposed target labels are compared with replayed labels;
they are not trusted as certificates. No global game reduction is asserted. -/
namespace Characterisation
open DistributedSynthesis

/-- Iterated existing next-round scenarios; the root and every round remain
explicit, so no possible private-input or graph continuation is discarded. -/
def ClosingLayer (H I₁ I₂ : Type) : Nat → Type
  | 0 => H
  | n+1 => NextScenario (ClosingLayer H I₁ I₂ n) I₁ I₂

instance closingLayer_fintype {H I₁ I₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] (n : Nat) : Fintype (ClosingLayer H I₁ I₂ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype H)
  | succ n ih => unfold ClosingLayer NextScenario; infer_instance

instance closingLayer_decidableEq {H I₁ I₂ : Type}
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] (n : Nat) :
    DecidableEq (ClosingLayer H I₁ I₂ n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq H)
  | succ n ih => unfold ClosingLayer NextScenario; infer_instance

def closingLayerHistory {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂) :
    (n : Nat) → ClosingLayer H I₁ I₂ n → EnvHistory I₁ I₂
  | 0 => past
  | n+1 => scenarioHistory (closingLayerHistory past n)

def closingLayerShape {H I₁ I₂ : Type} [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H) : (n : Nat) → InputShape (ClosingLayer H I₁ I₂ n)
  | 0 => shape
  | n+1 => advanceInputShape (closingLayerShape shape n)

theorem closingLayerShape_exact {H I₁ I₂ : Type} [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (n : Nat) :
    RepresentsInputShape (closingLayerHistory past n)
      (closingLayerShape (I₁:=I₁) (I₂:=I₂) shape n) := by
  induction n with
  | zero => exact rep
  | succ n ih => exact advanceInputShape_exact _ _ ih

abbrev ClosingPolicy (H I₁ I₂ O₁ O₂ : Type) (D : Nat) :=
  (n : Fin D) → ClosingLayer H I₁ I₂ (n.val+1) → O₁ × O₂

def ClosingPolicyCoherent {H I₁ I₂ O₁ O₂ : Type} [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H) {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) : Prop :=
  ∀ n, ShapeCoherent (closingLayerShape (I₁:=I₁) (I₂:=I₂) shape (n.val+1)) (out n)

instance closingPolicyCoherent_decidable {H I₁ I₂ O₁ O₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
    (shape : InputShape H) {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) :
    Decidable (ClosingPolicyCoherent shape out) := by
  unfold ClosingPolicyCoherent
  infer_instance

def closingLayerRoot {H I₁ I₂ : Type} : (n : Nat) → ClosingLayer H I₁ I₂ n → H
  | 0 => id
  | n+1 => fun s => closingLayerRoot n s.1

theorem closingLayerHistory_length {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) : List.length (closingLayerHistory past n s) = L+n := by
  induction n with
  | zero => exact depth s
  | succ n ih =>
    simp [closingLayerHistory,scenarioHistory,ih,Nat.add_assoc]

/-- The computed coherence check is equivalent to one actual local strategy
implementing all rounds of the window, when roots have a common depth. -/
theorem closingPolicyCoherent_iff_local {H I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) :
    ClosingPolicyCoherent shape out ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ n s,
      σ.one (currentView .one (closingLayerHistory past (n.val+1) s)) = (out n s).1 ∧
      σ.two (currentView .two (closingLayerHistory past (n.val+1) s)) = (out n s).2 := by
  have timeEq : ∀ (n m : Fin D) s t,
      InputAdjacent (closingLayerHistory past (n.val+1) s)
        (closingLayerHistory past (m.val+1) t) → n = m := by
    intro n m s t adj
    have len := adjacent_same_depth (inputAdjacent_projects adj)
    have lengths : List.length (closingLayerHistory past (n.val+1) s) =
        List.length (closingLayerHistory past (m.val+1) t) := by
      simpa [History.graphSequence] using len
    rw [closingLayerHistory_length past L depth,closingLayerHistory_length past L depth] at lengths
    apply Fin.ext
    omega
  constructor
  · intro coherent
    apply (tables_compatible_iff_local
      (fun n s => closingLayerHistory past (n.val+1) s) out).mp
    constructor
    · intro n m s t eq
      obtain rfl := timeEq n m s t (Or.inl eq)
      exact (coherent n).1 s t ((closingLayerShape_exact past shape rep _ .one s t).mpr eq)
    · intro n m s t eq
      obtain rfl := timeEq n m s t (Or.inr eq)
      exact (coherent n).2 s t ((closingLayerShape_exact past shape rep _ .two s t).mpr eq)
  · rintro ⟨σ,correct⟩ n
    exact (shapeCoherent_iff_local _ _ (closingLayerShape_exact past shape rep _) (out n)).mpr
      ⟨σ,correct n⟩

/-- Monitor labels are recomputed along every prefix, including every
intermediate output. Q may include objective/adversary states and minima. -/
def closingLayerLabels {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) :
    (n : Nat) → n ≤ D → ClosingLayer H I₁ I₂ n → Q
  | 0, _ => initial
  | n+1, bound => fun s => step
      (closingLayerLabels step initial out n (by omega) s.1) s.2 (out ⟨n,by omega⟩ s)

def closingLayerTrace {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) :
    (n : Nat) → n ≤ D → ClosingLayer H I₁ I₂ n → List ((I₁ × I₂ × Graph) × (O₁ × O₂))
  | 0, _ => fun _ => []
  | n+1, bound => fun s => closingLayerTrace out n (by omega) s.1 ++ [(s.2,out ⟨n,by omega⟩ s)]

theorem closingLayerLabels_replay {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step initial out n bound s =
      (closingLayerTrace out n bound s).foldl (fun q letter => step q letter.1 letter.2)
        (initial (closingLayerRoot n s)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [closingLayerLabels,closingLayerTrace,closingLayerRoot,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih]

/-- The same replay computes the adversary recognizer state independently
of all prescribed outputs. No separate graph-transition algorithm is needed. -/
theorem closingLayerLabels_recognizer {H I₁ I₂ O₁ O₂ Q : Type}
    (M : Recognizer Graph Q) (past : H → EnvHistory I₁ I₂) (initial : H → Q)
    (startExact : ∀ h, initial h = M.eval (History.graphSequence (past h)))
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels (fun q move _ => M.step q move.2.2) initial out n bound s =
      M.eval (History.graphSequence (closingLayerHistory past n s)) := by
  induction n with
  | zero => exact startExact s
  | succ n ih =>
    simp only [closingLayerLabels]
    rw [ih]
    simp [closingLayerHistory,scenarioHistory,History.graphSequence,
      Recognizer.eval,Recognizer.evalFrom,List.foldl_append]

def closingLayerLive {H I₁ I₂ O₁ O₂ Q : Type}
    (M : Recognizer Graph Q) [DecidablePred (fun q => q ∈ M.accept)]
    (initial : H → Q) {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) : Bool :=
  decide (closingLayerLabels (fun q move _ => M.step q move.2.2) initial out n bound s ∈ M.accept)

theorem closingLayerLive_exact {H I₁ I₂ O₁ O₂ Q : Type}
    (M : Recognizer Graph Q) [DecidablePred (fun q => q ∈ M.accept)]
    (P : List Graph → Prop) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (past : H → EnvHistory I₁ I₂) (initial : H → Q)
    (startExact : ∀ h, initial h = M.eval (History.graphSequence (past h)))
    {D : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLive M initial out n bound s = true ↔
      P (History.graphSequence (closingLayerHistory past n s)) := by
  simp only [closingLayerLive,decide_eq_true_eq,closingLayerLabels_recognizer M past initial startExact]
  exact (recognizes _).symm

/-- The retained slots are supplied explicitly. This computes their view
equalities and monitor labels, without claiming they form a full component. -/
def computedClosingTarget {H S I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H) (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (initial : H → Q) {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (keep : S → ClosingLayer H I₁ I₂ n) : InputShape S × (S → Q) :=
  (restrictInputShape (closingLayerShape shape n) keep,
    fun s => closingLayerLabels step initial out n bound (keep s))

theorem computedClosingTarget_exact {H S I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (keep : S → ClosingLayer H I₁ I₂ n) :
    RepresentsInputShape (closingLayerHistory past n ∘ keep)
      (computedClosingTarget shape step initial out bound keep).1 ∧
    ∀ s, (computedClosingTarget shape step initial out bound keep).2 s =
      (closingLayerTrace out n bound (keep s)).foldl (fun q letter => step q letter.1 letter.2)
        (initial (closingLayerRoot n (keep s))) :=
  ⟨restrictInputShape_exact _ _ (closingLayerShape_exact past shape rep n) keep,
    fun s => closingLayerLabels_replay step initial out n bound (keep s)⟩

/-- The proposed target is exact precisely when its observation matrix and
every retained monitor label match the actual bounded replay. -/
theorem computedClosingTarget_characterization {H S I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (keep : S → ClosingLayer H I₁ I₂ n)
    (proposed : InputShape S × (S → Q)) :
    proposed = computedClosingTarget shape step initial out bound keep ↔
      RepresentsInputShape (closingLayerHistory past n ∘ keep) proposed.1 ∧
      ∀ s, proposed.2 s =
        (closingLayerTrace out n bound (keep s)).foldl (fun q letter => step q letter.1 letter.2)
          (initial (closingLayerRoot n (keep s))) := by
  have correct := computedClosingTarget_exact past shape rep step initial out bound keep
  constructor
  · rintro rfl
    exact correct
  · rintro ⟨observations,labels⟩
    apply Prod.ext
    · funext p s t
      exact Bool.eq_iff_iff.mpr ((observations p s t).trans (correct.1 p s t).symm)
    · funext s
      exact (labels s).trans (correct.2 s).symm

/-- Executable finite check: local implementability, exact target, and an
allowed-target predicate. The initial labels are trusted inputs to this
transition checker and must be tied to the game state by its caller. -/
def checkClosingMove {H S I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype S] [Fintype I₁] [Fintype I₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    (shape : InputShape H) (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (initial : H → Q) {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (keep : S → ClosingLayer H I₁ I₂ n)
    (proposed : InputShape S × (S → Q))
    (Allowed : InputShape S × (S → Q) → Prop) [DecidablePred Allowed] : Bool :=
  decide (ClosingPolicyCoherent shape out ∧
    proposed = computedClosingTarget shape step initial out bound keep ∧ Allowed proposed)

/-- Correctness includes every output position and the complete target
matrix and label vector, not only membership in a set of allowed targets. -/
theorem checkClosingMove_correct {H S I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype S] [Fintype I₁] [Fintype I₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    {D n : Nat} (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (keep : S → ClosingLayer H I₁ I₂ n)
    (proposed : InputShape S × (S → Q))
    (Allowed : InputShape S × (S → Q) → Prop) [DecidablePred Allowed] :
    checkClosingMove shape step initial out bound keep proposed Allowed = true ↔
      (∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ t s,
        σ.one (currentView .one (closingLayerHistory past (t.val+1) s)) = (out t s).1 ∧
        σ.two (currentView .two (closingLayerHistory past (t.val+1) s)) = (out t s).2) ∧
      (RepresentsInputShape (closingLayerHistory past n ∘ keep) proposed.1 ∧
        ∀ s, proposed.2 s =
          (closingLayerTrace out n bound (keep s)).foldl (fun q letter => step q letter.1 letter.2)
            (initial (closingLayerRoot n (keep s)))) ∧ Allowed proposed := by
  simp only [checkClosingMove,decide_eq_true_eq]
  rw [closingPolicyCoherent_iff_local past shape rep L depth,
    computedClosingTarget_characterization past shape rep step initial out bound keep]

/-- A fixed finite set of candidates suffices for each finite source family,
window length and retained slot count. This is enumeration, not efficiency. -/
abbrev ClosingMove (H S I₁ I₂ O₁ O₂ Q : Type) (D n : Nat) :=
  ClosingPolicy H I₁ I₂ O₁ O₂ D × (S → ClosingLayer H I₁ I₂ n) × InputShape S × (S → Q)

instance closingMove_fintype {H S I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype S] [Fintype I₁] [Fintype I₂]
    [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq S] [DecidableEq I₁] [DecidableEq I₂] (D n : Nat) :
    Fintype (ClosingMove H S I₁ I₂ O₁ O₂ Q D n) := by
  unfold ClosingMove ClosingPolicy InputShape
  infer_instance

end Characterisation
