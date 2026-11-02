/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEntryThreadClass

/-!
# Same-`θ` entries are interchangeable under output continuations

This file machine-checks the interchange sentence of `prop:starcomplete`(b)
(`real_model/paper.tex`): *"two entry views with the same `θ` are hence
interchangeable -- any output continuation winning at one is winning at the
other."*  Concretely: let `σ` realize the objective on every environment, let
`h` be a generated entry and `h'` any history with the same entry thread
`entryState h = entryState h'`.  Then the **folded play** through `h'` -- the
word whose blind outputs are read from `σ`'s continuation of the
representative `h` while the informed outputs are `σ`'s continuation of `h'`
itself -- is accepted, *provided* the informed continuations of `h` and `h'`
agree (`hinformed`).

The proof exploits a structural fact of the model: views read only inputs
and graphs, never outputs, so a strategy execution is open-loop in its
outputs and the continuation of a play is determined by the base history and
the future environment alone (`continueExec`).  Under `hinformed` the folded
word *is* the `σ`-continuation of the representative `h`; splicing the
environment that generates `h` in front of the continuation environment
exhibits it as a genuine `σ`-execution word (`execution_spliceEnv`), and the
entry-faithfulness of acceptance (`accepts_prependList_congr`,
`prop:starsound`(ii)) moves the prefix from `h` back to `h'`.

**The honest boundary.**  The hypothesis `hinformed` is exactly the paper's
implicit simultaneous-fold obligation: for the *raw* realizing `σ` it is
false in general, because `σ`'s informed side may legitimately depend on
pre-entry details beyond `θ`.  It becomes true after the informed side is
itself folded onto its `G^⋆` coordinate, which is what the hierarchical
finite-memory engine (`thm:dynhiersynth`, the Berwanger import, or its
in-repo delayed-hierarchy analogues) provides.  `InformedPostEntryAgreement`
names that obligation; this file reduces the interchange step of
`prop:starcomplete` to it, with everything else proved.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-! ### Continuing an execution from a base history -/

/-- The `σ`-execution continued from a base history against a (post-entry)
environment sequence. -/
def continueExec (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) : Nat → History In₁ In₂ Graph Out₁ Out₂
  | 0 => base
  | n + 1 =>
      History.append (continueExec σ base env n)
        (nextRound σ (continueExec σ base env n) (env n))

/-- The round records emitted along a continued execution. -/
def contWord (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n => nextRound σ (continueExec σ base env n) (env n)

/-- Splice a generating environment prefix of length `s` in front of a
continuation environment. -/
def spliceEnv (env₀ : EnvironmentSequence In₁ In₂) (s : Nat)
    (env : EnvironmentSequence In₁ In₂) : EnvironmentSequence In₁ In₂ :=
  fun k => if k < s then env₀ k else env (k - s)

theorem spliceEnv_lt (env₀ : EnvironmentSequence In₁ In₂) (s : Nat)
    (env : EnvironmentSequence In₁ In₂) {k : Nat} (hk : k < s) :
    spliceEnv env₀ s env k = env₀ k := by
  simp [spliceEnv, hk]

theorem spliceEnv_add (env₀ : EnvironmentSequence In₁ In₂) (s : Nat)
    (env : EnvironmentSequence In₁ In₂) (m : Nat) :
    spliceEnv env₀ s env (s + m) = env m := by
  simp [spliceEnv, Nat.add_sub_cancel_left]

/-- Continuing from an execution prefix is the execution of the spliced
environment. -/
theorem continueExec_executionPrefix
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env₀ : EnvironmentSequence In₁ In₂) (s : Nat)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    continueExec σ (executionPrefix σ env₀ s) env n =
      executionPrefix σ (spliceEnv env₀ s env) (s + n) := by
  induction n with
  | zero =>
      exact (executionPrefix_congr_of_env_eq_lt σ
        (fun k hk => (spliceEnv_lt env₀ s env hk).symm)).symm ▸ rfl
  | succ n ih =>
      calc
        continueExec σ (executionPrefix σ env₀ s) env (n + 1)
            = History.append (continueExec σ (executionPrefix σ env₀ s) env n)
                (nextRound σ (continueExec σ (executionPrefix σ env₀ s) env n)
                  (env n)) := rfl
        _ = History.append (executionPrefix σ (spliceEnv env₀ s env) (s + n))
              (nextRound σ (executionPrefix σ (spliceEnv env₀ s env) (s + n))
                (spliceEnv env₀ s env (s + n))) := by
              rw [ih, spliceEnv_add]
        _ = executionPrefix σ (spliceEnv env₀ s env) (s + (n + 1)) := by
              rw [show s + (n + 1) = (s + n) + 1 from rfl,
                executionPrefix_succ]

/-! ### Prefix extraction lemmas -/

/-- Reading an execution prefix at an index below its length gives the
execution round. -/
theorem executionPrefix_getElem
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ {n k : Nat} (_ : k < n)
      (hlen : k < List.length (executionPrefix σ env n)),
      (executionPrefix σ env n)[k] = execution σ env k := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk hlen
      have hplen : List.length (executionPrefix σ env n) = n := by
        simpa [History.length] using executionPrefix_length σ env n
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have hlen' : k < List.length (executionPrefix σ env n) := by omega
        calc
          (executionPrefix σ env (n + 1))[k]
              = ((executionPrefix σ env n) ++
                  [nextRound σ (executionPrefix σ env n) (env n)])[k] := rfl
          _ = (executionPrefix σ env n)[k] := List.getElem_append_left hlen'
          _ = execution σ env k := ih hkn hlen'
      · have hkeq : k = n := by omega
        subst hkeq
        calc
          (executionPrefix σ env (k + 1))[k]
              = ((executionPrefix σ env k) ++
                  [nextRound σ (executionPrefix σ env k) (env k)])[k] := rfl
          _ = nextRound σ (executionPrefix σ env k) (env k) := by
              rw [List.getElem_append_right (by omega)]
              have hz : k - List.length (executionPrefix σ env k) = 0 := by omega
              simp [hz]
          _ = execution σ env k := (execution_apply σ env k).symm

namespace OmegaWord

/-- Reading the prepended prefix below its length. -/
theorem prependList_getElem_lt {Letter : Type u} :
    ∀ (l : List Letter) (word : OmegaWord Letter) {k : Nat}
      (hk : k < l.length),
      prependList l word k = l[k] := by
  intro l
  induction l with
  | nil => intro word k hk; simp at hk
  | cons a t ih =>
      intro word k hk
      cases k with
      | zero => rfl
      | succ k =>
          have hk' : k < t.length := by simpa using hk
          calc
            prependList (a :: t) word (k + 1) = prependList t word k := rfl
            _ = t[k] := ih word hk'
            _ = (a :: t)[k + 1] := by simp

/-- Reading the prepended word past the prefix. -/
theorem prependList_length_add {Letter : Type u} (l : List Letter)
    (word : OmegaWord Letter) (m : Nat) :
    prependList l word (l.length + m) = word m := by
  have h := congrFun (drop_length_prependList l word) m
  simpa [OmegaWord.drop] using h

end OmegaWord

/-- **A continued play is a genuine execution word.**  The `σ`-play through a
generated prefix, continued against `env`, equals the execution of the
spliced environment. -/
theorem execution_spliceEnv
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env₀ : EnvironmentSequence In₁ In₂) (s : Nat)
    (env : EnvironmentSequence In₁ In₂) :
    execution σ (spliceEnv env₀ s env) =
      OmegaWord.prependList (executionPrefix σ env₀ s)
        (contWord σ (executionPrefix σ env₀ s) env) := by
  have hplen : List.length (executionPrefix σ env₀ s) = s := by
    simpa [History.length] using executionPrefix_length σ env₀ s
  funext k
  rcases Nat.lt_or_ge k s with hk | hk
  · have hpre :
        executionPrefix σ (spliceEnv env₀ s env) k = executionPrefix σ env₀ k :=
      executionPrefix_congr_of_env_eq_lt σ
        (fun j hj => spliceEnv_lt env₀ s env (by omega))
    have hlen : k < List.length (executionPrefix σ env₀ s) := by omega
    calc
      execution σ (spliceEnv env₀ s env) k
          = nextRound σ (executionPrefix σ (spliceEnv env₀ s env) k)
              (spliceEnv env₀ s env k) := execution_apply σ _ k
      _ = nextRound σ (executionPrefix σ env₀ k) (env₀ k) := by
            rw [hpre, spliceEnv_lt env₀ s env hk]
      _ = execution σ env₀ k := (execution_apply σ env₀ k).symm
      _ = (executionPrefix σ env₀ s)[k] :=
            (executionPrefix_getElem σ env₀ hk hlen).symm
      _ = OmegaWord.prependList (executionPrefix σ env₀ s)
            (contWord σ (executionPrefix σ env₀ s) env) k :=
            (OmegaWord.prependList_getElem_lt _ _ hlen).symm
  · obtain ⟨m, rfl⟩ : ∃ m, k = s + m := ⟨k - s, by omega⟩
    calc
      execution σ (spliceEnv env₀ s env) (s + m)
          = nextRound σ (executionPrefix σ (spliceEnv env₀ s env) (s + m))
              (spliceEnv env₀ s env (s + m)) := execution_apply σ _ (s + m)
      _ = nextRound σ (continueExec σ (executionPrefix σ env₀ s) env m)
            (env m) := by
            rw [continueExec_executionPrefix, spliceEnv_add]
      _ = contWord σ (executionPrefix σ env₀ s) env m := rfl
      _ = OmegaWord.prependList (executionPrefix σ env₀ s)
            (contWord σ (executionPrefix σ env₀ s) env) (s + m) := by
            rw [show s + m = List.length (executionPrefix σ env₀ s) + m by omega]
            exact (OmegaWord.prependList_length_add _ _ m).symm

/-- Every generated continuation word is accepted by a realizing strategy. -/
theorem accepts_prependList_contWord
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts (OmegaWord.prependList h (contWord σ h env)) := by
  obtain ⟨env₀, n, rfl⟩ := strategyGeneratedPrefix_exists_executionPrefix σ hgen
  rw [← execution_spliceEnv]
  exact hwin (spliceEnv env₀ n env)

/-- The replayed continuation of a generated history is accepted through any
prefix reaching the same automaton state: the splice exhibits the replay as a
genuine execution word, and the entry congruence moves the prefix. -/
theorem accepts_prependList_contWord_congr
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hθ : DetParityAutomaton.entryState (A := A) h =
      DetParityAutomaton.entryState (A := A) h')
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts (OmegaWord.prependList h' (contWord σ h env)) := by
  rw [← A.accepts_prependList_congr (l := h) (l' := h') hθ (contWord σ h env)]
  exact accepts_prependList_contWord σ hwin hgen env

/-! ### The interchange theorem -/

/-- The folded continuation word through `hBase`: inputs and graphs from the
environment, blind (process-`1`) outputs from `σ`'s continuation of `hBlind`,
informed (process-`2`) outputs from `σ`'s continuation of `hBase`. -/
def foldedContWordOne (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hBlind hBase : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n =>
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne := (contWord σ hBlind env n).outputOne
      outputTwo := (contWord σ hBase env n).outputTwo }

/-- The mirror: blind (process-`2`) outputs from `hBlind`'s continuation,
informed (process-`1`) outputs from `hBase`'s. -/
def foldedContWordTwo (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hBlind hBase : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n =>
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne := (contWord σ hBase env n).outputOne
      outputTwo := (contWord σ hBlind env n).outputTwo }

/-- **Same-`θ` interchange (blind process `1`).**  If `σ` realizes the
objective everywhere, `h` is a generated entry, `h'` has the same entry
thread, and the informed continuations of `h` and `h'` agree against `env`,
then the folded play through `h'` reading its blind outputs from the
representative `h` is accepted.  This is `prop:starcomplete`(b)'s
interchange sentence with the simultaneous-fold obligation (`hinformed`)
explicit. -/
theorem same_theta_interchange_one
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hθ : DetParityAutomaton.entryState (A := A) h =
      DetParityAutomaton.entryState (A := A) h')
    (env : EnvironmentSequence In₁ In₂)
    (hinformed : ∀ n : Nat,
      (contWord σ h' env n).outputTwo = (contWord σ h env n).outputTwo) :
    A.Accepts (OmegaWord.prependList h' (foldedContWordOne σ h h' env)) := by
  have hword : foldedContWordOne σ h h' env = contWord σ h env := by
    funext n
    simp only [foldedContWordOne]
    rw [hinformed n]
    rfl
  rw [hword,
    ← A.accepts_prependList_congr (l := h) (l' := h') hθ (contWord σ h env)]
  exact accepts_prependList_contWord σ hwin hgen env

/-- **Same-`θ` interchange (blind process `2`).**  The orientation mirror of
`same_theta_interchange_one`. -/
theorem same_theta_interchange_two
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hθ : DetParityAutomaton.entryState (A := A) h =
      DetParityAutomaton.entryState (A := A) h')
    (env : EnvironmentSequence In₁ In₂)
    (hinformed : ∀ n : Nat,
      (contWord σ h' env n).outputOne = (contWord σ h env n).outputOne) :
    A.Accepts (OmegaWord.prependList h' (foldedContWordTwo σ h h' env)) := by
  have hword : foldedContWordTwo σ h h' env = contWord σ h env := by
    funext n
    simp only [foldedContWordTwo]
    rw [hinformed n]
    rfl
  rw [hword,
    ← A.accepts_prependList_congr (l := h) (l' := h') hθ (contWord σ h env)]
  exact accepts_prependList_contWord σ hwin hgen env

/-! ### The named residual obligation -/

/-- **The simultaneous-fold obligation.**  The informed side's post-entry
responses depend on the entry only through its thread `θ`.  For a raw
realizing strategy this is false in general -- `σ`'s informed side may
legitimately remember pre-entry details beyond `θ` -- and making it true by
folding the informed side onto its `G^⋆` coordinate without losing
realization is exactly the hierarchical finite-memory step
(`thm:dynhiersynth` / the Berwanger import).  Everything else in
`prop:starcomplete`'s interchange is proved: given this property, every
blind fold across a same-`θ` class preserves acceptance
(`foldPreservation_of_informedPostEntryAgreement`). -/
def InformedPostEntryAgreement
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    Prop :=
  ∀ (h h' : History In₁ In₂ Graph Out₁ Out₂),
    StrategyGeneratedPrefix σ h → StrategyGeneratedPrefix σ h' →
    DetParityAutomaton.entryState (A := A) h =
      DetParityAutomaton.entryState (A := A) h' →
    ∀ (env : EnvironmentSequence In₁ In₂) (n : Nat),
      (contWord σ h' env n).outputTwo = (contWord σ h env n).outputTwo

/-- Under the simultaneous-fold obligation, the blind fold across every
same-`θ` pair of generated entries preserves acceptance on every
continuation environment. -/
theorem foldPreservation_of_informedPostEntryAgreement
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    (hagree : InformedPostEntryAgreement σ A)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hgen' : StrategyGeneratedPrefix σ h')
    (hθ : DetParityAutomaton.entryState (A := A) h =
      DetParityAutomaton.entryState (A := A) h')
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts (OmegaWord.prependList h' (foldedContWordOne σ h h' env)) :=
  same_theta_interchange_one σ hwin hgen hθ env
    (hagree h h' hgen hgen' hθ env)

/-! ### The paired-representative fold dissolves the obligation

`InformedPostEntryAgreement` demanded agreement between `σ`'s informed
continuations of *different* same-`θ` entries -- false for a raw `σ`.  The
resolution is not to prove it but to **bypass** it: fold *both* sides onto
one representative, chosen as a `b_old` **pair** `(hB, hI)` of entries with
the same blind view.  The informed side, which recovers the full thread `θ`
at the reversal (`lem:reversaltwobits`; class form
`recv_view_determines_prefix_two`), replays `σ`'s continuation of the
variant `hI` matching the play's true `θ`; the blind side replays either
variant -- along the reversed block their blind outputs coincide, because
the two variants carry the same blind view and the blind view extends by
`noRecv` steps only (`continueExec_viewOne_eq`).  The doubly-folded word is
then *literally* `σ`'s replayed continuation of `hI`, a genuine execution
word, and acceptance through any same-`θ` prefix is the prefix congruence.
**No agreement hypothesis remains**: `pairedRepFold_accepted_one` is
unconditional.  What it does not cover is deliberate and structural: the
environment stays inside the reversed block (`hright`); stitching folded
blocks at their closing boundaries is the journal/arena plumbing, not
interchange mathematics. -/

/-- The blind view extends by `noRecv` steps only along an all-`right`
continuation: equal blind base views give equal blind views forever. -/
theorem continueExec_viewOne_eq
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {base base' : History In₁ In₂ Graph Out₁ Out₂}
    (hview : currentView Proc.one base = currentView Proc.one base')
    (env : EnvironmentSequence In₁ In₂)
    (hright : ∀ j : Nat, (env j).graph = Graph.right) (n : Nat) :
    currentView Proc.one (continueExec σ base env n) =
      currentView Proc.one (continueExec σ base' env n) := by
  induction n with
  | zero => exact hview
  | succ n ih =>
      calc
        currentView Proc.one (continueExec σ base env (n + 1))
            = View.noRecv (currentView Proc.one (continueExec σ base env n))
                (PSum.inl (env n).inputOne) := by
              simp [continueExec, currentView_one_append, hright n, nextRound]
        _ = View.noRecv (currentView Proc.one (continueExec σ base' env n))
              (PSum.inl (env n).inputOne) := by rw [ih]
        _ = currentView Proc.one (continueExec σ base' env (n + 1)) := by
              simp [continueExec, currentView_one_append, hright n, nextRound]

/-- Equal blind base views force equal blind outputs along an all-`right`
continuation.  This is the `b_old`-pair coherence of the fold: the two
variants of one blind view drive the same blind table. -/
theorem contWord_outputOne_eq_of_viewOne_eq
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {base base' : History In₁ In₂ Graph Out₁ Out₂}
    (hview : currentView Proc.one base = currentView Proc.one base')
    (env : EnvironmentSequence In₁ In₂)
    (hright : ∀ j : Nat, (env j).graph = Graph.right) (n : Nat) :
    (contWord σ base env n).outputOne = (contWord σ base' env n).outputOne := by
  have hv := continueExec_viewOne_eq σ hview env hright n
  simp only [contWord, nextRound_outputOne]
  simp only [nextView, advanceViewsWithEnvironment, hright n]
  simp only [currentView] at hv
  rw [hv]

/-- **The paired-representative fold is accepted, unconditionally.**  Let `σ`
realize the objective everywhere.  Let `hB, hI` be a `b_old` pair (equal
blind views; `hI` generated), and let `h'` be any history whose entry thread
matches the informed representative (`entryState hI = entryState h'`).
Along the reversed block (`hright`), the word whose blind outputs replay
`σ` from `hB` and whose informed outputs replay `σ` from `hI` is accepted
through `h'`.  Instantiating `hB := hI` covers the matching-variant case;
instantiating `hB` with the other `b_old` variant covers the crossed case --
so, together with `entryState_blindClass_le_two_one` (the class is exactly
the two variants), every play of the θ̄-paired-representative fold through a
same-`θ̄` entry is an accepted word.  `InformedPostEntryAgreement` is not
needed. -/
theorem pairedRepFold_accepted_one
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {hB hI h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgenI : StrategyGeneratedPrefix σ hI)
    (hview : currentView Proc.one hB = currentView Proc.one hI)
    (hθ : DetParityAutomaton.entryState (A := A) hI =
      DetParityAutomaton.entryState (A := A) h')
    (env : EnvironmentSequence In₁ In₂)
    (hright : ∀ j : Nat, (env j).graph = Graph.right) :
    A.Accepts (OmegaWord.prependList h' (foldedContWordOne σ hB hI env)) := by
  have hword : foldedContWordOne σ hB hI env = contWord σ hI env := by
    funext n
    simp only [foldedContWordOne]
    rw [contWord_outputOne_eq_of_viewOne_eq σ hview env hright n]
    rfl
  rw [hword,
    ← A.accepts_prependList_congr (l := hI) (l' := h') hθ (contWord σ hI env)]
  exact accepts_prependList_contWord σ hwin hgenI env

/-- Mirror of `continueExec_viewOne_eq` for process `2` along an all-`left`
continuation. -/
theorem continueExec_viewTwo_eq
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {base base' : History In₁ In₂ Graph Out₁ Out₂}
    (hview : currentView Proc.two base = currentView Proc.two base')
    (env : EnvironmentSequence In₁ In₂)
    (hleft : ∀ j : Nat, (env j).graph = Graph.left) (n : Nat) :
    currentView Proc.two (continueExec σ base env n) =
      currentView Proc.two (continueExec σ base' env n) := by
  induction n with
  | zero => exact hview
  | succ n ih =>
      calc
        currentView Proc.two (continueExec σ base env (n + 1))
            = View.noRecv (currentView Proc.two (continueExec σ base env n))
                (PSum.inr (env n).inputTwo) := by
              simp [continueExec, currentView_two_append, hleft n, nextRound]
        _ = View.noRecv (currentView Proc.two (continueExec σ base' env n))
              (PSum.inr (env n).inputTwo) := by rw [ih]
        _ = currentView Proc.two (continueExec σ base' env (n + 1)) := by
              simp [continueExec, currentView_two_append, hleft n, nextRound]

/-- Mirror of `contWord_outputOne_eq_of_viewOne_eq` for process `2`. -/
theorem contWord_outputTwo_eq_of_viewTwo_eq
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {base base' : History In₁ In₂ Graph Out₁ Out₂}
    (hview : currentView Proc.two base = currentView Proc.two base')
    (env : EnvironmentSequence In₁ In₂)
    (hleft : ∀ j : Nat, (env j).graph = Graph.left) (n : Nat) :
    (contWord σ base env n).outputTwo = (contWord σ base' env n).outputTwo := by
  have hv := continueExec_viewTwo_eq σ hview env hleft n
  simp only [contWord, nextRound_outputTwo]
  simp only [nextView, advanceViewsWithEnvironment, hleft n]
  simp only [currentView] at hv
  rw [hv]

/-- Mirror of `pairedRepFold_accepted_one`: blind process `2`, reversed
`left`-block, informed representative `hI` supplying the process-`1`
outputs. -/
theorem pairedRepFold_accepted_two
    [Inhabited In₁] [Inhabited In₂]
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {hB hI h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgenI : StrategyGeneratedPrefix σ hI)
    (hview : currentView Proc.two hB = currentView Proc.two hI)
    (hθ : DetParityAutomaton.entryState (A := A) hI =
      DetParityAutomaton.entryState (A := A) h')
    (env : EnvironmentSequence In₁ In₂)
    (hleft : ∀ j : Nat, (env j).graph = Graph.left) :
    A.Accepts (OmegaWord.prependList h' (foldedContWordTwo σ hB hI env)) := by
  have hword : foldedContWordTwo σ hB hI env = contWord σ hI env := by
    funext n
    simp only [foldedContWordTwo]
    rw [contWord_outputTwo_eq_of_viewTwo_eq σ hview env hleft n]
    rfl
  rw [hword,
    ← A.accepts_prependList_congr (l := hI) (l' := h') hθ (contWord σ hI env)]
  exact accepts_prependList_contWord σ hwin hgenI env

end DistributedSynthesis
