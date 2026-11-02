/- Decision-task excerpts from consensusLTL.
Source declarations and hashes are recorded in ../source-manifest.json. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Konig
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Views
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

set_option linter.unusedSectionVars false

/- From TaskColouring.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe v x

variable {V : Type v} {O : Type x}

/-- `p` has the same full view at time `r`: the same graph view, the same own input, and the
same other input if it has heard. -/
def FullEq (p : Bool) (r : ℕ) (σ τ : ℕ → Event Bool) (I J : Bool → V) : Prop :=
  ViewEq p r σ τ ∧ I p = J p ∧ ((∃ i, i < r ∧ Hears p σ i) → I (!p) = J (!p))

namespace FullEq

variable {p : Bool} {r : ℕ} {σ τ ρ : ℕ → Event Bool} {I J L : Bool → V}

theorem view (h : FullEq p r σ τ I J) : ViewEq p r σ τ := h.1
theorem own (h : FullEq p r σ τ I J) : I p = J p := h.2.1

theorem other (h : FullEq p r σ τ I J) {i : ℕ} (hi : i < r) (hh : Hears p σ i) :
    I (!p) = J (!p) := h.2.2 ⟨i, hi, hh⟩

theorem refl (p : Bool) (r : ℕ) (σ : ℕ → Event Bool) (I : Bool → V) : FullEq p r σ σ I I :=
  ⟨ViewEq.refl p r σ, rfl, fun _ => rfl⟩

theorem symm (h : FullEq p r σ τ I J) : FullEq p r τ σ J I :=
  ⟨h.view.symm, h.own.symm, fun ⟨i, hi, hh⟩ =>
    (h.2.2 ⟨i, hi, (h.view.hears_iff hi).mpr hh⟩).symm⟩

theorem trans (h₁ : FullEq p r σ τ I J) (h₂ : FullEq p r τ ρ J L) : FullEq p r σ ρ I L :=
  ⟨h₁.view.trans h₂.view, h₁.own.trans h₂.own, fun ⟨i, hi, hh⟩ =>
    (h₁.2.2 ⟨i, hi, hh⟩).trans (h₂.2.2 ⟨i, hi, (h₁.view.hears_iff hi).mp hh⟩)⟩

theorem mono {r' : ℕ} (h : FullEq p r' σ τ I J) (hle : r ≤ r') : FullEq p r σ τ I J :=
  ⟨h.view.mono hle, h.own, fun ⟨i, hi, hh⟩ => h.2.2 ⟨i, lt_of_lt_of_le hi hle, hh⟩⟩

/-- On two processes an input assignment is its two values, so a full view that has heard
determines the whole input assignment. -/
theorem inputs_eq (h : FullEq p r σ τ I J) {i : ℕ} (hi : i < r) (hh : Hears p σ i) : I = J := by
  funext q
  rcases Bool.eq_or_eq_not q p with hq | hq
  · rw [hq]; exact h.own
  · rw [hq]; exact h.other hi hh

end FullEq

section Hist

variable {p : Bool} {r : ℕ} {σ τ : ℕ → Event Bool} {I J : Bool → V}

/-- **The view lemma with inputs, forward.**  Equal histories give equal full views. -/
theorem fullEq_of_hist_eq (h : hist σ I r p = hist τ J r p) : FullEq p r σ τ I J := by
  obtain ⟨hv, hown⟩ := viewEq_of_hist_eq r p h
  refine ⟨hv, hown, ?_⟩
  rintro ⟨i, hi, hh⟩
  have h₁ : (hist σ I r p).other = some (I (!p)) := hist_other_of_heard hh r hi
  have h₂ : (hist τ J r p).other = some (J (!p)) :=
    hist_other_of_heard ((hv.hears_iff hi).mp hh) r hi
  rw [h, h₂] at h₁
  exact (Option.some_inj.mp h₁).symm

/-- **The view lemma with inputs, converse.**  Equal full views give equal histories: the
history is the state of the full-information algorithm, which is a function of the view. -/
theorem hist_eq_of_fullEq (h : FullEq p r σ τ I J) : hist σ I r p = hist τ J r p := by
  have := run_eq_of_viewEq (historyAlg V)
    h.view h.own h.2.2
  rwa [historyAlg_run, historyAlg_run] at this

/-- Equal histories are at equal times. -/
theorem time_eq_of_hist_eq {r' : ℕ} (h : hist σ I r p = hist τ J r' p) : r = r' := by
  have := congrArg Hist.depth h
  rwa [hist_depth, hist_depth] at this

end Hist

/-- A *scheme* for the task `T`: one output per process and input assignment, each determined
by a finite full view of its own process, the pair always allowed.

`cont` alone implies that a muted process's output ignores the other's input, since two input
assignments agreeing on `p` give `p` the same full view in a run where it never hears. -/
structure OutputScheme (adv : Set (ℕ → Event Bool)) (T : Task Bool V O) where
  /-- The output of `p` on inputs `I` in the run `σ`. -/
  out : Bool → (Bool → V) → (ℕ → Event Bool) → O
  /-- Every process eventually knows its output. -/
  cont : ∀ σ ∈ adv, ∀ (I : Bool → V) (p : Bool), ∃ r, ∀ τ ∈ adv, ∀ J,
    FullEq p r σ τ I J → out p J τ = out p I σ
  /-- The pair of outputs is allowed. -/
  allows : ∀ σ ∈ adv, ∀ I, T.allows I (fun p => out p I σ)

section OfSolver

variable {St : Type v} {adv : Set (ℕ → Event Bool)} {T : Task Bool V O}
  {A : Algorithm Bool V St} {out : Bool → St → Option O}

open Classical in
/-- The value `p` outputs on inputs `I` in the run `σ`. -/
noncomputable def solverOut [Nonempty O] (A : Algorithm Bool V St) (out : Bool → St → Option O)
    (p : Bool) (I : Bool → V) (σ : ℕ → Event Bool) : O :=
  if h : ∃ o : O, ∃ r, out p (A.run σ I r p) = some o then h.choose else Classical.arbitrary O

variable [Nonempty O]

/-- Irrevocability makes the output unique, so `solverOut` reads it off any time. -/
theorem solverOut_eq (hA : A.SolvesTask out T adv) {σ : ℕ → Event Bool} (hσ : σ ∈ adv)
    {I : Bool → V} {p : Bool} {r : ℕ} {o : O} (h : out p (A.run σ I r p) = some o) :
    solverOut A out p I σ = o := by
  classical
  have hex : ∃ o : O, ∃ r, out p (A.run σ I r p) = some o := ⟨o, r, h⟩
  rw [solverOut, dif_pos hex]
  obtain ⟨r', hr'⟩ := hex.choose_spec
  have h₁ := hA.irrev σ hσ I p r (max r r') (le_max_left _ _) o h
  have h₂ := hA.irrev σ hσ I p r' (max r r') (le_max_right _ _) _ hr'
  exact Option.some_inj.mp (h₂.symm.trans h₁)

/-- **A solver yields a scheme.**  Termination gives the finite decision time, the view lemma
gives continuity, and validity gives the allowed pair. -/
noncomputable def outputScheme_of_solvesTask (hA : A.SolvesTask out T adv) :
    OutputScheme adv T where
  out := solverOut A out
  cont := by
    intro σ hσ I p
    obtain ⟨r, o, ho⟩ := hA.term σ hσ I p
    refine ⟨r, fun τ hτ J hv => ?_⟩
    have hrun : A.run σ I r p = A.run τ J r p := run_eq_of_viewEq A hv.view hv.own hv.2.2
    rw [solverOut_eq hA hτ (by rw [← hrun]; exact ho), solverOut_eq hA hσ ho]
  allows := by
    intro σ hσ I
    refine hA.allows σ hσ I _ fun p => ?_
    obtain ⟨r, o, ho⟩ := hA.term σ hσ I p
    exact ⟨r, by rw [ho, solverOut_eq hA hσ ho]⟩

end OfSolver

section OfScheme

variable {adv : Set (ℕ → Event Bool)} {T : Task Bool V O}

/-- The full-information algorithm: its state is the history. -/
noncomputable def histAlg (V : Type v) : Algorithm Bool V (Hist V) :=
  historyAlg V

theorem histAlg_run (σ : ℕ → Event Bool) (I : Bool → V) (r : ℕ) (p : Bool) :
    (histAlg V).run σ I r p = hist σ I r p := historyAlg_run σ I r p

/-- The history `st` determines the output `o` of `p`. -/
def DeterminesOut (adv : Set (ℕ → Event Bool))
    (F : Bool → (Bool → V) → (ℕ → Event Bool) → O) (p : Bool) (st : Hist V) (o : O) : Prop :=
  ∀ σ ∈ adv, ∀ (I : Bool → V) (r : ℕ), hist σ I r p = st → F p I σ = o

open Classical in
/-- Output as soon as the history determines the value. -/
noncomputable def outMap (adv : Set (ℕ → Event Bool))
    (F : Bool → (Bool → V) → (ℕ → Event Bool) → O) (p : Bool) (st : Hist V) : Option O :=
  if h : ∃ o, DeterminesOut adv F p st o then some h.choose else none

variable {F : Bool → (Bool → V) → (ℕ → Event Bool) → O}

theorem outMap_isSome_of_determines {p : Bool} {st : Hist V} {o : O}
    (h : DeterminesOut adv F p st o) : ∃ o', outMap adv F p st = some o' := by
  classical
  exact ⟨_, dif_pos ⟨o, h⟩⟩

/-- Any value output at a realised history is the scheme's value there. -/
theorem outMap_value {σ : ℕ → Event Bool} (hσ : σ ∈ adv) {I : Bool → V} {p : Bool} {r : ℕ}
    {o : O} (h : outMap adv F p (hist σ I r p) = some o) : o = F p I σ := by
  classical
  by_cases hex : ∃ o, DeterminesOut adv F p (hist σ I r p) o
  · rw [outMap, dif_pos hex] at h
    rw [← Option.some_inj.mp h]
    exact (hex.choose_spec σ hσ I r rfl).symm
  · rw [outMap, dif_neg hex] at h
    exact absurd h (by simp)

/-- A history determining the value keeps determining it. -/
theorem determinesOut_mono {σ : ℕ → Event Bool} (hσ : σ ∈ adv) {I : Bool → V} {p : Bool}
    {r r' : ℕ} (hle : r ≤ r') {o : O} (h : DeterminesOut adv F p (hist σ I r p) o) :
    DeterminesOut adv F p (hist σ I r' p) o := by
  intro τ hτ J r'' hr''
  have hrr : r'' = r' := time_eq_of_hist_eq hr''
  subst hrr
  exact h τ hτ J r (hist_eq_of_fullEq ((fullEq_of_hist_eq hr'').mono hle))

/-- Continuity makes the history determine the value. -/
theorem determinesOut_of_cont {σ : ℕ → Event Bool} (hσ : σ ∈ adv) {I : Bool → V} {p : Bool}
    {r : ℕ} (h : ∀ τ ∈ adv, ∀ J, FullEq p r σ τ I J → F p J τ = F p I σ) :
    DeterminesOut adv F p (hist σ I r p) (F p I σ) := by
  intro τ hτ J r' hr'
  have hrr : r' = r := time_eq_of_hist_eq hr'
  subst hrr
  exact h τ hτ J (fullEq_of_hist_eq hr').symm

/-- **A scheme yields a solver**, with irrevocable outputs. -/
theorem solvesTask_of_outputScheme (S : OutputScheme adv T) :
    (histAlg V).SolvesTask (outMap adv S.out) T adv where
  term := by
    intro σ hσ I p
    obtain ⟨r, hr⟩ := S.cont σ hσ I p
    obtain ⟨o, ho⟩ := outMap_isSome_of_determines (determinesOut_of_cont hσ hr)
    refine ⟨r, o, ?_⟩
    change outMap adv S.out p ((histAlg V).run σ I r p) = some o
    rw [histAlg_run]
    exact ho
  irrev := by
    classical
    intro σ hσ I p r r' hle o h
    change outMap adv S.out p ((histAlg V).run σ I r p) = some o at h
    change outMap adv S.out p ((histAlg V).run σ I r' p) = some o
    rw [histAlg_run] at h ⊢
    have hex : ∃ o, DeterminesOut adv S.out p (hist σ I r p) o := by
      by_contra hc
      rw [outMap, dif_neg hc] at h
      exact absurd h (by simp)
    have ho : o = S.out p I σ := outMap_value hσ h
    have hd : DeterminesOut adv S.out p (hist σ I r p) o := by
      rw [outMap, dif_pos hex] at h
      rw [← Option.some_inj.mp h]
      exact hex.choose_spec
    obtain ⟨o', ho'⟩ := outMap_isSome_of_determines (determinesOut_mono hσ hle hd)
    rw [ho', outMap_value hσ ho', ho]
  allows := by
    intro σ hσ I o ho
    have : o = fun p => S.out p I σ := by
      funext p
      obtain ⟨r, hr⟩ := ho p
      change outMap adv S.out p ((histAlg V).run σ I r p) = some (o p) at hr
      rw [histAlg_run] at hr
      exact outMap_value hσ hr
    rw [this]
    exact S.allows σ hσ I

end OfScheme

/-- **A task is solvable iff it has a scheme.**  Termination, irrevocability and validity on
one side; continuity in each process's own full view and an allowed pair on the other. -/
theorem solvesTask_iff_outputScheme [Nonempty O] {adv : Set (ℕ → Event Bool)}
    {T : Task Bool V O} :
    (∃ (St : Type v) (A : Algorithm Bool V St) (out : Bool → St → Option O),
        A.SolvesTask out T adv) ↔ Nonempty (OutputScheme adv T) :=
  ⟨fun ⟨_, _, _, hA⟩ => ⟨outputScheme_of_solvesTask hA⟩,
   fun ⟨S⟩ => ⟨Hist V, histAlg V, outMap adv S.out, solvesTask_of_outputScheme S⟩⟩

/-- The input assignment giving `x` to `p` and `y` to the other process. -/
def inp (p : Bool) (x y : V) : Bool → V := fun q => if q = p then x else y

@[simp] theorem inp_self (p : Bool) (x y : V) : inp p x y p = x := by simp [inp]

@[simp] theorem inp_other (p : Bool) (x y : V) : inp p x y (!p) = y := by
  cases p <;> simp [inp]

theorem inp_eq (I : Bool → V) (p : Bool) : inp p (I p) (I (!p)) = I := by
  funext q; cases p <;> cases q <;> simp [inp]

/-- The colouring `p` uses when the inputs are `I`. -/
def colFor (C : Bool → V → V → Base → O) (I : Bool → V) : Bool → Base → O :=
  fun p b => C p (I p) (I (!p)) b

/-- A colouring of the bases by outputs solving the task `T`. -/
structure TaskColouring (adv : Set (ℕ → Event Bool)) (T : Task Bool V O)
    (C : Bool → V → V → Base → O) : Prop where
  /-- Before hearing, a process's colour cannot depend on the other's input. -/
  init : ∀ p x y y', C p x y none = C p x y' none
  /-- Each process hears at a good base, or ends at its eventual base. -/
  term : ∀ σ ∈ adv, ∀ (I : Bool → V) (p : Bool),
    (∃ i c, Hears p σ i ∧ Good p (colFor C I) (pre σ i) c) ∨
    (∃ b c, (∃ n₀, ∀ n, n₀ ≤ n → base p σ n = b) ∧ End p (colFor C I) b c)
  /-- The pair of current colours is eventually allowed. -/
  allows : ∀ σ ∈ adv, ∀ I, ∃ n₀, ∀ n, n₀ ≤ n →
    T.allows I (fun p => colFor C I p (base p σ n))

section ColToScheme

variable {adv : Set (ℕ → Event Bool)} {T : Task Bool V O} {C : Bool → V → V → Base → O}

open Classical in
/-- The output a colouring prescribes: the eventual colour. -/
noncomputable def colOut [Nonempty O] (C : Bool → V → V → Base → O) (p : Bool) (I : Bool → V)
    (σ : ℕ → Event Bool) : O :=
  if h : ∃ c, EvCol (colFor C I) p σ c then h.choose else Classical.arbitrary O

variable [Nonempty O]

theorem colOut_eq {p : Bool} {I : Bool → V} {σ : ℕ → Event Bool} {c : O}
    (h : EvCol (colFor C I) p σ c) : colOut C p I σ = c := by
  classical
  rw [colOut, dif_pos ⟨c, h⟩]
  exact evCol_unique (Exists.choose_spec ⟨c, h⟩) h

/-- **A colouring yields a scheme.**  The waiting time at a received base is the one supplied by
`stable_of_term_disj`; at the initial base it is the largest of those for the finitely many
values of the *unknown* other input, which is legitimate because `init` makes the colour there
independent of that input. -/
noncomputable def outputScheme_of_taskColouring [Finite V] (hC : TaskColouring adv T C) :
    OutputScheme adv T where
  out := colOut C
  cont := by
    intro σ hσ I p
    choose R c hc hgood using fun y : V =>
      stable_of_term_disj (hC.term σ hσ (inp p (I p) y) p)
    obtain ⟨M, hM⟩ := (Set.finite_range R).bddAbove
    have hRM : ∀ y, R y ≤ M := fun y => hM ⟨y, rfl⟩
    have hev : ∀ (y : V) (τ : ℕ → Event Bool), ViewEq p (R y) σ τ →
        EvCol (colFor C (inp p (I p) y)) p τ (c y) := by
      intro y τ hv
      refine ⟨R y, colour_stable ?_ ?_⟩
      · rw [base_eq_of_viewEq hv]; exact hc y
      · rw [base_eq_of_viewEq hv]; exact hgood y
    have hI : inp p (I p) (I (!p)) = I := inp_eq I p
    have hσI : colOut C p I σ = c (I (!p)) := by
      have := hev (I (!p)) σ (ViewEq.refl p _ σ)
      rw [hI] at this
      exact colOut_eq this
    refine ⟨M, fun τ hτ J hv => ?_⟩
    have hJ : J = inp p (I p) (J (!p)) := by
      funext q
      cases p <;> cases q <;> simp [inp, hv.own.symm]
    have hτJ : colOut C p J τ = c (J (!p)) := by
      have := hev (J (!p)) τ (hv.view.mono (hRM _))
      rw [← hJ] at this
      exact colOut_eq this
    rw [hτJ, hσI]
    by_cases hh : ∃ i, i < M ∧ Hears p σ i
    · obtain ⟨i, hi, hhi⟩ := hh
      rw [hv.inputs_eq hi hhi]
    · -- silence up to `M`: both colours are read at the initial base
      push Not at hh
      have hbase : ∀ y, base p σ (R y) = none :=
        fun y => base_eq_none_of_silent fun i hi => hh i (lt_of_lt_of_le hi (hRM y))
      have hcval : ∀ y, c y = C p (I p) y none := by
        intro y
        rw [← hc y, hbase y]
        simp [colFor]
      rw [hcval, hcval, hC.init]
  allows := by
    intro σ hσ I
    obtain ⟨n₀, hn₀⟩ := hC.allows σ hσ I
    choose R c hc hgood using fun p : Bool =>
      stable_of_term_disj (hC.term σ hσ I p)
    have hcs : ∀ (p : Bool) (n : ℕ), R p ≤ n → colFor C I p (base p σ n) = c p :=
      fun p => colour_stable (hc p) (hgood p)
    have hout : ∀ p, colOut C p I σ = c p := fun p => colOut_eq ⟨R p, hcs p⟩
    have hfun : (fun p => colFor C I p (base p σ (max n₀ (max (R U) (R W)))))
        = fun p => colOut C p I σ := by
      funext p
      rw [hout p]
      refine hcs p _ (le_trans ?_ (le_max_right n₀ (max (R U) (R W))))
      cases p
      · exact le_max_left (R U) (R W)
      · exact le_max_right (R U) (R W)
    have := hn₀ _ (le_max_left n₀ (max (R U) (R W)))
    rwa [hfun] at this

end ColToScheme

section SchemeToCol

variable {adv : Set (ℕ → Event Bool)} {T : Task Bool V O}

/-- `p` is committed to the output `o` at time `n` of `(σ, I)`: some admissible run and input
assignment share its full view at some earlier time, and all of them give output `o`. -/
def CommittedT (adv : Set (ℕ → Event Bool)) (F : Bool → (Bool → V) → (ℕ → Event Bool) → O)
    (p : Bool) (σ : ℕ → Event Bool) (I : Bool → V) (n : ℕ) (o : O) : Prop :=
  ∃ m, m ≤ n ∧ (∃ τ ∈ adv, ∃ J, FullEq p m σ τ I J) ∧
    ∀ τ ∈ adv, ∀ J, FullEq p m σ τ I J → F p J τ = o

variable {F : Bool → (Bool → V) → (ℕ → Event Bool) → O}

theorem CommittedT.mono {p : Bool} {σ : ℕ → Event Bool} {I : Bool → V} {n n' : ℕ} {o : O}
    (h : CommittedT adv F p σ I n o) (hle : n ≤ n') : CommittedT adv F p σ I n' o := by
  obtain ⟨m, hm, hw, hd⟩ := h
  exact ⟨m, le_trans hm hle, hw, hd⟩

theorem CommittedT.unique {p : Bool} {σ : ℕ → Event Bool} {I : Bool → V} {n n' : ℕ} {o o' : O}
    (h : CommittedT adv F p σ I n o) (h' : CommittedT adv F p σ I n' o') : o = o' := by
  obtain ⟨m, -, hw, hd⟩ := h
  obtain ⟨m', -, hw', hd'⟩ := h'
  rcases le_total m m' with hmm | hmm
  · obtain ⟨τ, hτ, J, hv⟩ := hw'
    rw [← hd τ hτ J (hv.mono hmm), hd' τ hτ J hv]
  · obtain ⟨τ, hτ, J, hv⟩ := hw
    rw [← hd τ hτ J hv, hd' τ hτ J (hv.mono hmm)]

/-- Commitment is a property of the full view. -/
theorem CommittedT.of_fullEq {p : Bool} {σ τ : ℕ → Event Bool} {I J : Bool → V} {n : ℕ} {o : O}
    (h : CommittedT adv F p σ I n o) (hv : FullEq p n σ τ I J) :
    CommittedT adv F p τ J n o := by
  obtain ⟨m, hm, ⟨ρ, hρ, L, hL⟩, hd⟩ := h
  have hv' : FullEq p m σ τ I J := hv.mono hm
  exact ⟨m, hm, ⟨ρ, hρ, L, hv'.symm.trans hL⟩,
    fun ρ' hρ' J' hJ' => hd ρ' hρ' J' (hv'.trans hJ')⟩

open Classical in
/-- The colour of a base: the output `p` is committed to on the base's canonical run. -/
noncomputable def taskColour [Nonempty O] (adv : Set (ℕ → Event Bool))
    (F : Bool → (Bool → V) → (ℕ → Event Bool) → O) (p : Bool) (x y : V) (b : Base) : O :=
  if h : ∃ o n, CommittedT adv F p (extRun b) (inp p x y) n o then h.choose
  else Classical.arbitrary O

variable [Nonempty O]

theorem taskColour_eq {p : Bool} {x y : V} {b : Base} {n : ℕ} {o : O}
    (h : CommittedT adv F p (extRun b) (inp p x y) n o) : taskColour adv F p x y b = o := by
  classical
  have hex : ∃ o n, CommittedT adv F p (extRun b) (inp p x y) n o := ⟨o, n, h⟩
  rw [taskColour, dif_pos hex]
  obtain ⟨n', hn'⟩ := hex.choose_spec
  exact hn'.unique h

/-- The colour of a base is that of the current base of any run realising it. -/
theorem taskColour_of_committed {p : Bool} {σ : ℕ → Event Bool} {I : Bool → V} {n : ℕ} {o : O}
    (h : CommittedT adv F p σ I n o) :
    taskColour adv F p (I p) (I (!p)) (base p σ n) = o := by
  refine taskColour_eq (n := n) ?_
  rw [inp_eq]
  exact h.of_fullEq ⟨viewEq_extRun_base p σ n, rfl, fun _ => rfl⟩

/-- **A scheme yields a colouring.** -/
theorem taskColouring_of_outputScheme (S : OutputScheme adv T) :
    TaskColouring adv T (taskColour adv S.out) where
  init := by
    intro p x y y'
    classical
    by_cases hex : ∃ o n, CommittedT adv S.out p (extRun none) (inp p x y) n o
    · obtain ⟨o, n, h⟩ := hex
      -- a silent run never reveals the other input, so the two commitments coincide
      have htrans : ∀ (z z' : V) (o : O) (n : ℕ),
          CommittedT adv S.out p (extRun none) (inp p x z) n o →
          CommittedT adv S.out p (extRun none) (inp p x z') n o := by
        intro z z' o n h
        refine h.of_fullEq ⟨ViewEq.refl p n _, by simp, ?_⟩
        rintro ⟨i, -, hh⟩
        exact absurd hh not_hears_extRun_none
      rw [taskColour_eq h, taskColour_eq (htrans y y' o n h)]
    · have hex' : ¬ ∃ o n, CommittedT adv S.out p (extRun none) (inp p x y') n o := by
        rintro ⟨o, n, h⟩
        refine hex ⟨o, n, h.of_fullEq ⟨ViewEq.refl p n _, by simp, ?_⟩⟩
        rintro ⟨i, -, hh⟩
        exact absurd hh not_hears_extRun_none
      rw [taskColour, dif_neg hex, taskColour, dif_neg hex']
  term := by
    intro σ hσ I p
    obtain ⟨r, hr⟩ := S.cont σ hσ I p
    have hcom : CommittedT adv S.out p σ I r (S.out p I σ) :=
      ⟨r, le_rfl, ⟨σ, hσ, I, FullEq.refl p r σ I⟩, hr⟩
    have hcol : ∀ {n : ℕ}, r ≤ n → colFor (taskColour adv S.out) I p (base p σ n)
        = S.out p I σ := by
      intro n hn
      exact taskColour_of_committed (hcom.mono hn)
    by_cases hex : ∃ i, r ≤ i ∧ Hears p σ i
    · obtain ⟨i, hri, hi⟩ := hex
      refine Or.inl ⟨i, S.out p I σ, hi, ?_, ?_⟩
      · rw [← base_succ_of_hears hi]
        exact hcol (by omega)
      · intro g t _
        have hv : FullEq p r σ (extRun (some (pre σ i ++ g :: t))) I I :=
          ⟨viewEq_extRun_of_prefix ⟨g :: t, rfl⟩ hri, rfl, fun _ => rfl⟩
        rw [← base_extRun_succ (p := p) (pre σ i ++ g :: t)]
        refine taskColour_of_committed ((hcom.of_fullEq hv).mono ?_)
        simp only [List.length_append, pre_length]
        omega
    · push Not at hex
      refine Or.inr ⟨base p σ r, S.out p I σ,
        ⟨r, fun n hn => base_eq_of_silent_between n hn fun i hri _ => hex i hri⟩,
        hcol le_rfl, ?_⟩
      refine (List.finite_length_lt Letter r).subset ?_
      rintro j ⟨hj, hng⟩
      show j.length < r
      rcases Nat.lt_or_ge j.length r with hlt | hlen
      · exact hlt
      exfalso
      apply hng
      have hv : FullEq p r σ (extRun (some j)) I I :=
        ⟨viewEq_extRun_firstReturn hj hlen, rfl, fun _ => rfl⟩
      have hcj : CommittedT adv S.out p (extRun (some j)) I r (S.out p I σ) := hcom.of_fullEq hv
      refine ⟨?_, fun g t _ => ?_⟩
      · rw [← base_extRun_succ (p := p) j]
        exact taskColour_of_committed (hcj.mono (by omega))
      · have hv' : FullEq p r (extRun (some j)) (extRun (some (j ++ g :: t))) I I :=
          ⟨viewEq_of_inN_eq fun i hi q => by
            rw [extRun_eq_of_prefix ⟨g :: t, rfl⟩ (lt_of_lt_of_le hi hlen)], rfl, fun _ => rfl⟩
        rw [← base_extRun_succ (p := p) (j ++ g :: t)]
        refine taskColour_of_committed ((hcj.of_fullEq hv').mono ?_)
        simp only [List.length_append]
        omega
  allows := by
    intro σ hσ I
    obtain ⟨rU, hrU⟩ := S.cont σ hσ I U
    obtain ⟨rW, hrW⟩ := S.cont σ hσ I W
    have hcU : CommittedT adv S.out U σ I rU (S.out U I σ) :=
      ⟨rU, le_rfl, ⟨σ, hσ, I, FullEq.refl _ _ σ I⟩, hrU⟩
    have hcW : CommittedT adv S.out W σ I rW (S.out W I σ) :=
      ⟨rW, le_rfl, ⟨σ, hσ, I, FullEq.refl _ _ σ I⟩, hrW⟩
    refine ⟨max rU rW, fun n hn => ?_⟩
    have hfun : (fun p => colFor (taskColour adv S.out) I p (base p σ n))
        = fun p => S.out p I σ := by
      funext p
      cases p
      · exact taskColour_of_committed (hcU.mono (le_trans (le_max_left _ _) hn))
      · exact taskColour_of_committed (hcW.mono (le_trans (le_max_right _ _) hn))
    rw [hfun]
    exact S.allows σ hσ I

end SchemeToCol

/-- **A task has a scheme iff it has a colouring.** -/
theorem outputScheme_iff_taskColouring [Finite V] [Nonempty O] {adv : Set (ℕ → Event Bool)}
    {T : Task Bool V O} :
    Nonempty (OutputScheme adv T) ↔ ∃ C, TaskColouring adv T C :=
  ⟨fun ⟨S⟩ => ⟨_, taskColouring_of_outputScheme S⟩,
   fun ⟨_, hC⟩ => ⟨outputScheme_of_taskColouring hC⟩⟩

/-- **A decision task on two processes is a colouring of the history tree.**  The task `T` is
solvable under `adv`, with termination and irrevocable outputs, iff the bases carry outputs
such that no colour at an unheard-from base depends on the other input, every process reaches a
good base or ends at one with finitely many bad first returns, and the pair of current colours
is eventually allowed. -/
theorem solvesTask_iff_taskColouring [Finite V] [Nonempty O] {adv : Set (ℕ → Event Bool)}
    {T : Task Bool V O} :
    (∃ (St : Type v) (A : Algorithm Bool V St) (out : Bool → St → Option O),
        A.SolvesTask out T adv) ↔ ∃ C, TaskColouring adv T C :=
  solvesTask_iff_outputScheme.trans outputScheme_iff_taskColouring

end DistributedSynthesis.DecisionTasks.Source

/- From Decision.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe v x

theorem taskColouring_annotated_form {V O : Type} {adv : Set (ℕ → Event Bool)} {T : Task Bool V O}
    {C : Bool → V → V → Base → O} :
    TaskColouring adv T C ↔
      (∀ p x y y', C p x y none = C p x y' none) ∧
      (∀ σ ∈ adv, ∀ (I : Bool → V) (p : Bool),
        (∃ i c, Hears p σ i ∧ colFor C I p (some (pre σ i)) = c ∧
          ∀ a : Letter, a.hears p = true → AllCol p (colFor C I) (pre σ i ++ [a]) c) ∨
        (∃ N c, (∀ i, N ≤ i → ¬ Hears p σ i) ∧ colFor C I p (base p σ N) = c ∧
          ∀ β : ℕ → List Letter, β 0 = [] → IsBranch β →
            ∃ n, NoBelow (Bad p (colFor C I) (base p σ N) c) (β n))) ∧
      (∀ σ ∈ adv, ∀ I, ∃ n₀, ∀ n, n₀ ≤ n →
        T.allows I fun p => colFor C I p (base p σ n)) := by
  constructor
  · rintro ⟨hi, ht, ha⟩
    refine ⟨hi, fun σ hσ I p => ?_, ha⟩
    rcases ht σ hσ I p with ⟨i, c, hh, hg⟩ | ⟨b, c, hb, hC, hfin⟩
    · obtain ⟨h1, h2⟩ := good_iff_allCol.mp hg
      exact Or.inl ⟨i, c, hh, h1, h2⟩
    · obtain ⟨N, hN⟩ := exists_eventual_base_iff.mp ⟨b, hb⟩
      obtain ⟨N', hN'⟩ := hb
      refine Or.inr ⟨max N N', c, fun i hi' => hN i (le_trans (le_max_left _ _) hi'), ?_, ?_⟩
      · rw [hN' _ (le_max_right _ _)]; exact hC
      · rw [hN' _ (le_max_right _ _)]
        exact (finite_iff_eventually_noBelow _).mp hfin
  · rintro ⟨hi, ht, ha⟩
    refine ⟨hi, fun σ hσ I p => ?_, ha⟩
    rcases ht σ hσ I p with ⟨i, c, hh, h1, h2⟩ | ⟨N, c, hsil, hC, hev⟩
    · exact Or.inl ⟨i, c, hh, good_iff_allCol.mpr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨base p σ N, c,
        ⟨N, fun n hn => base_eq_of_silent_between n hn fun i hi' _ => hsil i hi'⟩,
        hC, (finite_iff_eventually_noBelow _).mpr hev⟩

end DistributedSynthesis.DecisionTasks.Source
