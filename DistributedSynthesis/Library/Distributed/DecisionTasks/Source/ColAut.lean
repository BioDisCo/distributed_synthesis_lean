/- Extracted from consensusLTL/lean/ConsensusLTL/ColAut.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Cone
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Konig
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Views
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.NodeTransport
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Parity
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.ParityCommit
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Union

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

namespace ColAut

/-- The two node predicates the labelling problem is parameterised by: which root colours a muted
process may carry, and which pairs of current colours are eventually acceptable.  Consensus is
`deafOk p c := decide (c = p)` with equality for `rel`; a task is `deafOk := true` with the task's
own relation at a fixed input assignment. -/
structure Spec (K : Type) where
  deafOk : Bool → K → Bool
  rel : K → K → Bool

/-- The live bad-set check of one process: the colour of its base, whether the check is one that
every branch must discharge, and whether it has been sealed. -/
structure BadChk (K : Type) where
  col : K
  required : Bool
  regime : Bool
  sealed : Bool
  deriving DecidableEq

instance {K : Type} [Fintype K] [DecidableEq K] : Fintype (BadChk K) :=
  Fintype.ofEquiv (K × Bool × Bool × Bool)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun b => ⟨b.col, b.required, b.regime, b.sealed⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The per-process part of a state.  `goodDone` records that an ancestor was good, `lastRec` that
the step into this node was a reception, `baseCol` the colour of the current base. -/
structure PState (K : Type) where
  goodDone : Bool
  heard : Bool
  baseCol : K
  lastRec : Bool
  allCol : Option K
  bad : Option (BadChk K)
  deriving DecidableEq

instance {K : Type} [Fintype K] [DecidableEq K] : Fintype (PState K) :=
  Fintype.ofEquiv (Bool × Bool × K × Bool × Option K × Option (BadChk K))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
      invFun := fun t => ⟨t.goodDone, t.heard, t.baseCol, t.lastRec, t.allCol, t.bad⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The priority bound of the implication layer, and so the range the second record covers. -/
def bImp (bd : ℕ) : ℕ := ParityUnion.unionBound (bd + 1) 2

/-- The record deciding *the adversary rejects, or the clauses hold*. -/
abbrev Rec1 (bd : ℕ) := ParityUnion.UnionMemory (bd + 1) 2

/-- The record conjoining that with the obligation every branch carries. -/
abbrev Rec2 (bd : ℕ) := ParityUnion.MeetMemory (bImp bd) 1

/-- A state.  `bd` bounds the adversary's priorities; `rec1` and `rec2` are the two compiler
memories, which are deterministic functions of the branch and carry no guess. -/
structure St (K AdvQ : Type) (bd : ℕ) where
  q : AdvQ
  pu : PState K
  pv : PState K
  rrK : Bool
  rec1 : Rec1 bd
  rec2 : Rec2 bd
  deriving DecidableEq

instance {K AdvQ : Type} [Fintype K] [DecidableEq K] [Fintype AdvQ] [DecidableEq AdvQ] {bd : ℕ} :
    Fintype (St K AdvQ bd) :=
  Fintype.ofEquiv (AdvQ × PState K × PState K × Bool × Rec1 bd × Rec2 bd)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
      invFun := fun s => ⟨s.q, s.pu, s.pv, s.rrK, s.rec1, s.rec2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A presentation of the adversary by a deterministic parity automaton on letters. -/
structure Adv (AdvQ : Type) where
  step : AdvQ → Letter → AdvQ
  init : AdvQ
  prio : AdvQ → ℕ

variable {K : Type} [Fintype K] [DecidableEq K]
variable {AdvQ : Type} [Fintype AdvQ] [DecidableEq AdvQ] {bd : ℕ}
variable {S : Spec K}

/-- A bound on the adversary's priorities. -/
def advBound (A : Adv AdvQ) : ℕ := Finset.univ.sup A.prio

theorem le_advBound (A : Adv AdvQ) (q : AdvQ) : A.prio q ≤ advBound A :=
  Finset.le_sup (Finset.mem_univ q)

/-- Direction `i` is a reception for `p`. -/
def recDir (p : Bool) (i : Fin 4) : Bool := (dirLetter i).hears p

/-- The part of a state belonging to a process. -/
def St.get (s : St K AdvQ bd) (p : Bool) : PState K := if p then s.pv else s.pu

@[simp] theorem St.get_false (s : St K AdvQ bd) : s.get false = s.pu := rfl
@[simp] theorem St.get_true (s : St K AdvQ bd) : s.get true = s.pv := rfl

/-- The bad-set check of `p` is discharged: there is none, its regime has died, or it is sealed. -/
def PState.ok (t : PState K) : Bool :=
  match t.bad with
  | none => true
  | some b => !b.required || !b.regime || b.sealed

/-- The check of `p` is sealed and still in regime, and is one other branches must also seal. -/
def PState.sealedHere (t : PState K) : Bool :=
  match t.bad with
  | none => false
  | some b => b.required && b.regime && b.sealed

/-- The termination clause of `p`, as a state predicate: an ancestor was good, or the process did
not just hear and its check is sealed.  The check must be *required*, which is what obliges every
other branch of its cone to seal it too, and so makes the bad set finite rather than merely finite
along this branch. -/
def PState.term (t : PState K) : Bool := t.goodDone || (!t.lastRec && t.sealedHere)

/-- The clauses, as a state predicate.  Deafness, termination for both processes, and agreement of
the two current base colours, which is a property of the node. -/
def St.phi (s : St K AdvQ bd) (S : Spec K) (r : Bool → K) : Bool :=
  (S.deafOk false (r false) || s.pu.heard) && (S.deafOk true (r true) || s.pv.heard) &&
    s.pu.term && s.pv.term && S.rel s.pu.baseCol s.pv.baseCol

/-- The discharge of `p`'s obligation on this step: a reception, or a discharged check. -/
def St.disch (s : St K AdvQ bd) (p : Bool) : Bool := (s.get p).lastRec || (s.get p).ok

/-- The wrap of the round robin between the two processes' obligations. -/
def St.firedK (s : St K AdvQ bd) : Bool := s.disch s.rrK && s.rrK

/-- The clause priority.  Min-parity on it says the clauses hold eventually always. -/
def St.cP (s : St K AdvQ bd) (S : Spec K) (r : Bool → K) : ℕ := if s.phi S r then 2 else 1

/-- The obligation priority.  Min-parity on it says the round robin wraps infinitely often. -/
def St.cK (s : St K AdvQ bd) : ℕ := if s.firedK then 0 else 1

/-- The implication layer, read off the first record. -/
def St.uPrio (A : Adv AdvQ) (s : St K AdvQ bd) (S : Spec K) (r : Bool → K) : ℕ :=
  ParityUnion.unionPriority (bd + 1) 2 s.rec1 (A.prio s.q + 1, s.cP S r)

/-- The branch priority, read off the second record. -/
def St.prio (A : Adv AdvQ) (s : St K AdvQ bd) (S : Spec K) (r : Bool → K) : ℕ :=
  ParityUnion.unionPriority (bImp bd + 1) 2 s.rec2
    (s.uPrio A S r + 1, s.cK + 1) + 1

/-- The deterministic update of the first record. -/
def St.rec1Next (A : Adv AdvQ) (s : St K AdvQ bd) (S : Spec K) (r : Bool → K) : Rec1 bd :=
  ParityUnion.unionUpdate (bd + 1) 2 s.rec1 (A.prio s.q + 1, s.cP S r)

/-- The deterministic update of the second record. -/
def St.rec2Next (A : Adv AdvQ) (s : St K AdvQ bd) (S : Spec K) (r : Bool → K) : Rec2 bd :=
  ParityUnion.unionUpdate (bImp bd + 1) 2 s.rec2
    (s.uPrio A S r + 1, s.cK + 1)

/-- The label is compatible with the checks live at this node, and a sealed check in regime makes
this node good.  These are conditions on the tree, not on a branch, so they may be enforced. -/
def labelOk (s : St K AdvQ bd) (lab : Bool → K) : Bool :=
  (match s.pu.allCol with | none => true | some c => lab false == c) &&
  (match s.pv.allCol with | none => true | some c => lab true == c) &&
  (match s.pu.bad with
    | none => true
    | some b => !(b.sealed && b.regime) || (lab false == b.col)) &&
  (match s.pv.bad with
    | none => true
    | some b => !(b.sealed && b.regime) || (lab true == b.col))

/-- A cone check for `p` with colour `c` is started in every reception direction. -/
def spawnCone (p : Bool) (c : K) (succ : Fin 4 → St K AdvQ bd) : Bool :=
  decide (∀ j : Fin 4, recDir p j = true → ((succ j).get p).allCol = some c)

/-- The per-process step.  `good` is the guess that this node is good for `p`. -/
def pStepOk (p : Bool) (s : St K AdvQ bd) (lab : Bool → K) (succ : Fin 4 → St K AdvQ bd)
    (good req : Bool) (i : Fin 4) : Bool :=
  let t := s.get p
  let t' := (succ i).get p
  let r := recDir p i
  (t'.heard == (t.heard || r)) &&
  (t'.baseCol == (if r then lab p else t.baseCol)) &&
  (t'.lastRec == r) &&
  (t'.goodDone == (t.goodDone || (good && r))) &&
  (!good || spawnCone p (lab p) succ) &&
  (match t.allCol with | none => true | some c => t'.allCol == some c) &&
  (match t.bad with
    | none => true
    | some b => !(b.sealed && b.regime) || spawnCone p b.col succ) &&
  (if r then
      (match t'.bad with
        | none => false
        | some b' => (b'.col == lab p) && b'.regime && (b'.required == req))
    else
      (match t.bad, t'.bad with
        | none, none => true
        | some b, some b' =>
            (b'.col == b.col) && (b'.required == b.required) && (b'.regime == b.regime) &&
              (!b.sealed || b'.sealed)
        | _, _ => false))

/-- The label read at a node: one colour per process. -/
def labOf (l : K × K) (p : Bool) : K := if p then l.2 else l.1

/-- The guesses belonging to the root: the colour of each process at the initial base, and whether
the initial bad-set check starts sealed. -/
structure Params (K : Type) where
  r : Bool → K
  requ : Bool
  reqv : Bool
  sealu : Bool
  sealv : Bool
  deriving DecidableEq

instance {K : Type} [Fintype K] [DecidableEq K] : Fintype (Params K) :=
  Fintype.ofEquiv ((Bool → K) × Bool × Bool × Bool × Bool)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
      invFun := fun pr => ⟨pr.r, pr.requ, pr.reqv, pr.sealu, pr.sealv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Both compiler memories advance deterministically, with no guess. -/
def recStepOk (S : Spec K) (A : Adv AdvQ) (pr : Params K) (s : St K AdvQ bd) (succ : Fin 4 → St K AdvQ bd)
    (i : Fin 4) : Bool :=
  decide ((succ i).rec1 = s.rec1Next A S pr.r) &&
  decide ((succ i).rec2 = s.rec2Next A S pr.r)

/-- The round-robin counter advances deterministically. -/
def rrStepOk (s : St K AdvQ bd) (succ : Fin 4 → St K AdvQ bd) (i : Fin 4) : Bool :=
  ((succ i).rrK == (if s.disch s.rrK then !s.rrK else s.rrK))

/-- The whole step, with the two per-process goodness guesses. -/
def stepOk (S : Spec K) (A : Adv AdvQ) (pr : Params K) (s : St K AdvQ bd) (lab : Bool → K)
    (succ : Fin 4 → St K AdvQ bd) (goodu goodv requ reqv : Bool) : Bool :=
  labelOk s lab &&
  decide (∀ i : Fin 4, (succ i).q = A.step s.q (dirLetter i)) &&
  decide (∀ i : Fin 4, pStepOk false s lab succ goodu requ i = true) &&
  decide (∀ i : Fin 4, pStepOk true s lab succ goodv reqv i = true) &&
  decide (∀ i : Fin 4, recStepOk S A pr s succ i = true) &&
  decide (∀ i : Fin 4, rrStepOk s succ i = true)

open DistributedSynthesis.DecisionTasks.Source.FiniteParity.TreeAutomaton

/-- The per-process part of the initial state. -/
def initP (star : K) (rq sl : Bool) : PState K where
  goodDone := false
  heard := false
  baseCol := star
  lastRec := false
  allCol := none
  bad := some { col := star, required := rq, regime := true, sealed := sl }

/-- The initial state. -/
def initSt (A : Adv AdvQ) (pr : Params K) : St K AdvQ (advBound A) where
  q := A.init
  pu := initP (pr.r false) pr.requ pr.sealu
  pv := initP (pr.r true) pr.reqv pr.sealv
  rrK := false
  rec1 := ParityUnion.initial (advBound A + 1) 2
  rec2 := ParityUnion.initial (bImp (advBound A) + 1) 2

/-- The automaton. -/
def automaton (S : Spec K) (A : Adv AdvQ) (pr : Params K) :
    RunParityTreeAutomaton (Fin 4) (K × K) where
  State := St K AdvQ (advBound A)
  stateFinite := inferInstance
  initial := initSt A pr
  delta s label succ :=
    ∃ gu gv ru rv : Bool, stepOk S A pr s (labOf label) succ gu gv ru rv = true
  priority s := s.prio A S pr.r

instance automaton_delta_decidable (S : Spec K) (A : Adv AdvQ) (pr : Params K) :
    ∀ q l f, Decidable ((automaton S A pr).delta q l f) :=
  fun _ _ _ => inferInstanceAs (Decidable (∃ _ _ _ _ : Bool, _))

instance automaton_state_decidableEq (S : Spec K) (A : Adv AdvQ) (pr : Params K) :
    DecidableEq (automaton S A pr).State :=
  inferInstanceAs (DecidableEq (St K AdvQ (advBound A)))

/-- The monitor state after reading `n` letters. -/
def advRun (A : Adv AdvQ) (w : ℕ → Letter) : ℕ → AdvQ
  | 0 => A.init
  | n + 1 => A.step (advRun A w n) (w n)

/-- The set of runs the adversary accepts. -/
def advOf (A : Adv AdvQ) : Set (ℕ → Event Bool) :=
  {σ | DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => A.prio (advRun A (letter σ) n)) false}

theorem stepOk_q {A : Adv AdvQ} {pr : Params K} {s : St K AdvQ bd} {lab : Bool → K}
    {succ : Fin 4 → St K AdvQ bd}
    {gu gv ru rv : Bool} (h : stepOk S A pr s lab succ gu gv ru rv = true) (i : Fin 4) :
    (succ i).q = A.step s.q (dirLetter i) := by
  rw [stepOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2 i

theorem stepOk_label {A : Adv AdvQ} {pr : Params K} {s : St K AdvQ bd} {lab : Bool → K}
    {succ : Fin 4 → St K AdvQ bd}
    {gu gv ru rv : Bool} (h : stepOk S A pr s lab succ gu gv ru rv = true) : labelOk s lab = true := by
  rw [stepOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

theorem stepOk_p {A : Adv AdvQ} {pr : Params K} {s : St K AdvQ bd} {lab : Bool → K}
    {succ : Fin 4 → St K AdvQ bd}
    {gu gv ru rv : Bool} (h : stepOk S A pr s lab succ gu gv ru rv = true) (p : Bool) (i : Fin 4) :
    pStepOk p s lab succ (if p then gv else gu) (if p then rv else ru) i = true := by
  rw [stepOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases p
  · exact h.1.1.1.2 i
  · exact h.1.1.2 i

theorem stepOk_rec {A : Adv AdvQ} {pr : Params K} {s : St K AdvQ bd} {lab : Bool → K}
    {succ : Fin 4 → St K AdvQ bd}
    {gu gv ru rv : Bool} (h : stepOk S A pr s lab succ gu gv ru rv = true) (i : Fin 4) :
    recStepOk S A pr s succ i = true := by
  rw [stepOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2 i

/-- The round-robin counters advance. -/
theorem stepOk_rr {A : Adv AdvQ} {pr : Params K} {s : St K AdvQ bd} {lab : Bool → K}
    {succ : Fin 4 → St K AdvQ bd}
    {gu gv ru rv : Bool} (h : stepOk S A pr s lab succ gu gv ru rv = true) (i : Fin 4) :
    rrStepOk s succ i = true := by
  rw [stepOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2 i

/-- The monitor component of a run follows the adversary along every branch. -/
theorem run_q_eq {A : Adv AdvQ} {pr : Params K} {t : Node 4 → K × K}
    {r : Node 4 → St K AdvQ (advBound A)}
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (b : ℕ → Fin 4) : ∀ n, (r (branchNode b n)).q = advRun A (fun i => dirLetter (b i)) n := by
  intro n
  induction n with
  | zero => rw [branchNode, h0]; rfl
  | succ n ih =>
      have hmem := hstep (branchNode b n)
      simp only [automaton, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      obtain ⟨gu, gv, ru, rv, hs⟩ := hmem
      have := stepOk_q hs (b n)
      show (r (branchNode b n ++ [b n])).q = _
      rw [this, ih]
      rfl

/-- The labelling a labelled tree defines. -/
def colOfTree (pr : Params K) (t : Node 4 → K × K) : Bool → Base → K
  | p, none => pr.r p
  | p, some h => labOf (t (histNode h)) p

section Run

variable {A : Adv AdvQ} {pr : Params K} {t : Node 4 → K × K}
  {r : Node 4 → St K AdvQ (advBound A)}

/-- Read a transition off a run. -/
theorem run_step (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (w : Node 4) : ∃ gu gv ru rv : Bool,
      stepOk S A pr (r w) (labOf (t w)) (fun i => r (w ++ [i])) gu gv ru rv = true := by
  have := hstep w
  exact this

/-- A live cone check is inherited all the way down its cone. -/
theorem run_allCol_cone (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {w : Node 4} {p : Bool} {c : K} (h : ((r w).get p).allCol = some c) :
    ∀ v : Node 4, ((r (w ++ v)).get p).allCol = some c := by
  intro v
  induction v using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton v i ih =>
      obtain ⟨gu, gv, ru, rv, hs⟩ := run_step hstep (w ++ v)
      have hp := stepOk_p hs p i
      rw [pStepOk] at hp
      simp only [Bool.and_eq_true] at hp
      have hinh := hp.1.1.2
      rw [ih] at hinh
      simp only [beq_iff_eq] at hinh
      rw [← List.append_assoc]
      exact hinh

/-- A live cone check forces the colour at its own node. -/
theorem run_allCol_here (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {w : Node 4} {p : Bool} {c : K} (h : ((r w).get p).allCol = some c) :
    labOf (t w) p = c := by
  obtain ⟨gu, gv, ru, rv, hs⟩ := run_step hstep w
  have hl := stepOk_label hs
  rw [labelOk] at hl
  simp only [Bool.and_eq_true] at hl
  cases p
  · have := hl.1.1.1
    rw [St.get_false] at h
    rw [h] at this
    simpa using this
  · have := hl.1.1.2
    rw [St.get_true] at h
    rw [h] at this
    simpa using this

/-- **Cone checks are sound.**  A live cone check means the whole cone carries its colour. -/
theorem run_allCol_sound (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {w : Node 4} {p : Bool} {c : K} (h : ((r w).get p).allCol = some c) :
    AllCol p (colOfTree pr t) (nodeHist w) c := by
  intro j hj
  obtain ⟨v, rfl⟩ := nodeHist_prefix hj
  show labOf (t (histNode (nodeHist (w ++ v)))) p = c
  rw [histNode_nodeHist]
  exact run_allCol_here hstep (run_allCol_cone hstep h v)

/-- The reception directions are exactly the reception letters. -/
theorem recDir_letterDir (p : Bool) (a : Letter) : recDir p (letterDir a) = a.hears p := by
  rw [recDir, dirLetter_letterDir]

/-- **A sealed check in regime makes its node good.**  This is where the second hard constraint of
`stepOk` is used: such a node must carry the check's colour, and must start a cone check in every
reception direction. -/
theorem run_good_of_sealed
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {w : Node 4} {p : Bool} {b : BadChk K} (h : ((r w).get p).bad = some b)
    (hs : b.sealed = true) (hr : b.regime = true) :
    Good p (colOfTree pr t) (nodeHist w) b.col := by
  obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep w
  refine good_iff_allCol.mpr ⟨?_, ?_⟩
  · show labOf (t (histNode (nodeHist w))) p = b.col
    rw [histNode_nodeHist]
    have hl := stepOk_label hstp
    rw [labelOk] at hl
    simp only [Bool.and_eq_true] at hl
    cases p
    · have := hl.1.2
      rw [St.get_false] at h
      rw [h] at this
      simp only [hs, hr, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at this
      exact this
    · have := hl.2
      rw [St.get_true] at h
      rw [h] at this
      simp only [hs, hr, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at this
      exact this
  · intro a ha
    have hp := stepOk_p hstp p (letterDir a)
    rw [pStepOk] at hp
    simp only [Bool.and_eq_true] at hp
    have hspawn := hp.1.2
    rw [h] at hspawn
    simp only [hs, hr, Bool.and_self, Bool.not_true, Bool.false_or, spawnCone,
      decide_eq_true_eq] at hspawn
    have hrec : recDir p (letterDir a) = true := by rw [recDir_letterDir]; exact ha
    have hcone := hspawn (letterDir a) hrec
    have := run_allCol_sound hstep hcone
    rw [nodeHist_append, dirLetter_letterDir] at this
    exact this

/-- The check survives a silent stretch, keeping its colour and regime, and stays sealed. -/
theorem run_bad_silent (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {w : Node 4} {p : Bool} {b : BadChk K} (h : ((r w).get p).bad = some b) :
    ∀ v : Node 4, (∀ i ∈ v, recDir p i = false) →
      ∃ b', ((r (w ++ v)).get p).bad = some b' ∧ b'.col = b.col ∧ b'.required = b.required ∧
        b'.regime = b.regime ∧ (b.sealed = true → b'.sealed = true) := by
  intro v
  induction v using List.reverseRecOn with
  | nil => intro _; exact ⟨b, by simpa using h, rfl, rfl, rfl, id⟩
  | append_singleton v i ih =>
      intro hsil
      obtain ⟨b', hb', hcol, hreq, hreg, hseal⟩ :=
        ih fun j hj => hsil j (List.mem_append_left _ hj)
      obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep (w ++ v)
      have hp := stepOk_p hstp p i
      rw [pStepOk] at hp
      simp only [Bool.and_eq_true] at hp
      have hbad := hp.2
      have hri : recDir p i = false := hsil i (by simp)
      rw [hri] at hbad
      simp only [Bool.false_eq_true, if_false, hb'] at hbad
      rw [← List.append_assoc]
      match hcur : ((r ((w ++ v) ++ [i])).get p).bad with
      | none => rw [hcur] at hbad; exact absurd hbad (by simp)
      | some b'' =>
          rw [hcur] at hbad
          simp only [Bool.and_eq_true, beq_iff_eq] at hbad
          exact ⟨b'', rfl, hbad.1.1.1.trans hcol, hbad.1.1.2.trans hreq, hbad.1.2.trans hreg,
            fun hbs => by
              have := hbad.2
              rw [hseal hbs] at this
              simpa using this⟩

theorem recDir_of_mem_histNode {p : Bool} {s : List Letter} {i : Fin 4}
    (hs : ∀ a ∈ s, a.hears p = false) (hi : i ∈ histNode s) : recDir p i = false := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  rw [recDir_letterDir]
  exact hs a ha

/-- **Sealed checks are sound.**  A sealed check in regime means no bad node lies above its
node, which is the eventuality of `colouring_determined_form`. -/
theorem run_noBelow_sound
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {w : Node 4} {p : Bool} {b : BadChk K} (h : ((r w).get p).bad = some b)
    (hs : b.sealed = true) (hr : b.regime = true) {base : Base}
    (hbase : FirstReturn p base (nodeHist w)) :
    NoBelow (Bad p (colOfTree pr t) base b.col) (nodeHist w) := by
  refine noBelow_iff_regime_good.mpr fun j hj hfr => ?_
  obtain ⟨s, hsj⟩ := hj
  have hsil : ∀ a ∈ s, a.hears p = false := by
    refine firstReturn_suffix_silent hbase ?_
    rw [hsj]
    exact hfr
  have hv : ∀ i ∈ histNode s, recDir p i = false := fun i hi => recDir_of_mem_histNode hsil hi
  obtain ⟨b', hb', hcol, -, hreg, hseal⟩ := run_bad_silent hstep h (histNode s) hv
  have hgood := run_good_of_sealed hstep hb' (hseal hs) (by rw [hreg]; exact hr)
  rw [nodeHist_append_all, nodeHist_histNode, hsj] at hgood
  rw [← hcol]
  exact hgood

/-- The live check always carries the colour of the current base. -/
theorem run_bad_col (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (h0 : r [] = initSt A pr) (p : Bool) : ∀ w : Node 4,
      ∃ b, ((r w).get p).bad = some b ∧ b.col = ((r w).get p).baseCol := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      rw [h0]
      cases p
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
  | append_singleton w i ih =>
      obtain ⟨b, hb, hcol⟩ := ih
      obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep w
      have hp := stepOk_p hstp p i
      rw [pStepOk] at hp
      simp only [Bool.and_eq_true] at hp
      have hbase := hp.1.1.1.1.1.1.2
      have hbad := hp.2
      simp only [beq_iff_eq] at hbase
      by_cases hri : recDir p i = true
      · rw [if_pos hri] at hbad
        match hcur : ((r (w ++ [i])).get p).bad with
        | none => rw [hcur] at hbad; exact absurd hbad (by simp)
        | some b'' =>
            rw [hcur] at hbad
            simp only [Bool.and_eq_true, beq_iff_eq] at hbad
            refine ⟨b'', rfl, ?_⟩
            rw [hbad.1.1, hbase, if_pos hri]
      · rw [Bool.not_eq_true] at hri
        rw [hri] at hbad
        simp only [Bool.false_eq_true, if_false, hb] at hbad
        match hcur : ((r (w ++ [i])).get p).bad with
        | none => rw [hcur] at hbad; exact absurd hbad (by simp)
        | some b'' =>
            rw [hcur] at hbad
            simp only [Bool.and_eq_true, beq_iff_eq] at hbad
            refine ⟨b'', rfl, ?_⟩
            rw [hbad.1.1.1, hcol, hbase, hri]
            simp

/-- Hearing on a branch is a reception direction. -/
theorem hears_runOfBranch {b : ℕ → Fin 4} {p : Bool} {n : ℕ} :
    Hears p (runOfBranch b) n ↔ recDir p (b n) = true := by
  rw [← letter_hears_iff, letter_runOfBranch, recDir]

/-- **The state tracks the colour of the current base.** -/
theorem run_baseCol (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (h0 : r [] = initSt A pr) (bb : ℕ → Fin 4) (p : Bool) : ∀ n : ℕ,
      ((r (branchNode bb n)).get p).baseCol =
        colOfTree pr t p (base p (runOfBranch bb) n) := by
  intro n
  induction n with
  | zero =>
      rw [branchNode, h0, base_zero]
      cases p <;> rfl
  | succ n ih =>
      obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep (branchNode bb n)
      have hp := stepOk_p hstp p (bb n)
      rw [pStepOk] at hp
      simp only [Bool.and_eq_true] at hp
      have hbase := hp.1.1.1.1.1.1.2
      simp only [beq_iff_eq] at hbase
      show ((r (branchNode bb n ++ [bb n])).get p).baseCol = _
      rw [hbase]
      by_cases hri : recDir p (bb n) = true
      · rw [if_pos hri, base_succ_of_hears (hears_runOfBranch.mpr hri)]
        show labOf (t (branchNode bb n)) p = labOf (t (histNode (pre (runOfBranch bb) n))) p
        rw [pre_runOfBranch, histNode_nodeHist]
      · rw [Bool.not_eq_true] at hri
        rw [if_neg (by rw [hri]; simp),
          base_succ_of_not_hears (fun hc => by rw [hears_runOfBranch.mp hc] at hri; simp at hri)]
        exact ih

/-- The `heard` bit records whether the process has ever received. -/
theorem run_heard (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (h0 : r [] = initSt A pr) (bb : ℕ → Fin 4) (p : Bool) : ∀ n : ℕ,
      (((r (branchNode bb n)).get p).heard = true ↔ ∃ i, i < n ∧ Hears p (runOfBranch bb) i) := by
  intro n
  induction n with
  | zero =>
      rw [branchNode, h0]
      constructor
      · intro h; cases p <;> exact absurd h (by simp [initSt, initP])
      · rintro ⟨i, hi, -⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep (branchNode bb n)
      have hp := stepOk_p hstp p (bb n)
      rw [pStepOk] at hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have hh := hp.1.1.1.1.1.1.1
      show (((r (branchNode bb n ++ [bb n])).get p).heard = true) ↔ _
      rw [hh]
      simp only [Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨i, hi, hhi⟩ := ih.mp h
          exact ⟨i, by omega, hhi⟩
        · exact ⟨n, Nat.lt_succ_self n, hears_runOfBranch.mpr h⟩
      · rintro ⟨i, hi, hhi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact Or.inl (ih.mpr ⟨i, hi', hhi⟩)
        · exact Or.inr (hears_runOfBranch.mp (hi' ▸ hhi))

/-- The `lastRec` bit records the step just taken. -/
theorem run_lastRec (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4) (p : Bool) (n : ℕ) :
    (((r (branchNode bb (n + 1))).get p).lastRec = true ↔ Hears p (runOfBranch bb) n) := by
  obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep (branchNode bb n)
  have hp := stepOk_p hstp p (bb n)
  rw [pStepOk] at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hl := hp.1.1.1.1.1.2
  show (((r (branchNode bb n ++ [bb n])).get p).lastRec = true) ↔ _
  rw [hl, hears_runOfBranch]

/-- **The good flag is sound.**  If it is set, the process heard at some earlier round and the
cones above the reception children of that node are constant, which is the first disjunct of the
termination clause. -/
theorem run_goodDone_sound
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (h0 : r [] = initSt A pr) (bb : ℕ → Fin 4) (p : Bool) : ∀ n : ℕ,
      ((r (branchNode bb n)).get p).goodDone = true →
        ∃ i, i < n ∧ Hears p (runOfBranch bb) i ∧
          ∀ a : Letter, a.hears p = true →
            AllCol p (colOfTree pr t) (pre (runOfBranch bb) i ++ [a])
              (colOfTree pr t p (some (pre (runOfBranch bb) i))) := by
  intro n
  induction n with
  | zero =>
      rw [branchNode, h0]
      intro h
      cases p <;> exact absurd h (by simp [initSt, initP])
  | succ n ih =>
      intro hgd
      obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep (branchNode bb n)
      have hp := stepOk_p hstp p (bb n)
      rw [pStepOk] at hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have hg := hp.1.1.1.1.2
      have hspawn := hp.1.1.1.2
      have hgd' : ((r (branchNode bb n)).get p).goodDone = true ∨
          ((if p then gv else gu) = true ∧ recDir p (bb n) = true) := by
        have : ((r (branchNode bb n ++ [bb n])).get p).goodDone = true := hgd
        rw [hg] at this
        simpa only [Bool.or_eq_true, Bool.and_eq_true] using this
      rcases hgd' with h | ⟨hgood, hrec⟩
      · obtain ⟨i, hi, hh, hall⟩ := ih h
        exact ⟨i, by omega, hh, hall⟩
      · refine ⟨n, Nat.lt_succ_self n, hears_runOfBranch.mpr hrec, fun a ha => ?_⟩
        rw [hgood] at hspawn
        simp only [Bool.not_true, Bool.false_or, spawnCone, decide_eq_true_eq] at hspawn
        have hcone := hspawn (letterDir a) (by rw [recDir_letterDir]; exact ha)
        have hAll := run_allCol_sound hstep hcone
        rw [nodeHist_append, dirLetter_letterDir, ← pre_runOfBranch] at hAll
        have hlab : labOf (t (branchNode bb n)) p
            = colOfTree pr t p (some (pre (runOfBranch bb) n)) := by
          show _ = labOf (t (histNode (pre (runOfBranch bb) n))) p
          rw [pre_runOfBranch, histNode_nodeHist]
        rw [← hlab]
        exact hAll

/-- Every run is the run of the branch of its own letters. -/
theorem runOfBranch_letterDir (σ : ℕ → Event Bool) :
    runOfBranch (fun i => letterDir (letter σ i)) = σ := by
  funext i
  refine event_eq_of_inN (funext fun q => ?_)
  show (Event.ofLetter (dirLetter (letterDir (letter σ i)))).inN q = (σ i).inN q
  rw [dirLetter_letterDir]
  exact inN_ofLetter_letter σ i q

theorem run_rec1 (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4) : ∀ n, (r (branchNode bb n)).rec1 =
      ParityUnion.unionRun (advBound A + 1) 2
        (fun k => A.prio (r (branchNode bb k)).q + 1)
        (fun k => (r (branchNode bb k)).cP S pr.r) n := by
  intro n
  induction n with
  | zero => rw [branchNode, h0]; rfl
  | succ n ih =>
      obtain ⟨gu, gv, ru, rv, hs⟩ := run_step hstep (branchNode bb n)
      have hrec := stepOk_rec hs (bb n)
      rw [recStepOk] at hrec
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrec
      show (r (branchNode bb n ++ [bb n])).rec1 = _
      rw [hrec.1, St.rec1Next, ih]
      rfl

theorem run_rec2 (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4) : ∀ n, (r (branchNode bb n)).rec2 =
      ParityUnion.unionRun (bImp (advBound A) + 1) 2
        (fun k => (r (branchNode bb k)).uPrio A S pr.r + 1)
        (fun k => (r (branchNode bb k)).cK + 1) n := by
  intro n
  induction n with
  | zero => rw [branchNode, h0]; rfl
  | succ n ih =>
      obtain ⟨gu, gv, ru, rv, hs⟩ := run_step hstep (branchNode bb n)
      have hrec := stepOk_rec hs (bb n)
      rw [recStepOk] at hrec
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrec
      show (r (branchNode bb n ++ [bb n])).rec2 = _
      rw [hrec.2, St.rec2Next, ih]
      rfl

/-- Along a branch the counter forms a round robin. -/
theorem run_roundRobinK (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4) :
    RoundRobin (fun i n => (r (branchNode bb n)).disch i)
      (fun n => (r (branchNode bb n)).rrK) (fun n => (r (branchNode bb n)).firedK) where
  step := by
    intro n
    obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep (branchNode bb n)
    have hrr := stepOk_rr hstp (bb n)
    rw [rrStepOk] at hrr
    simp only [beq_iff_eq] at hrr
    show (r (branchNode bb n ++ [bb n])).rrK = _
    exact hrr
  fire := fun n => rfl

/-- **The branch condition, read off the two records.**  The automaton's priority along a branch is
exactly the merged priority of `ParityUnion.meet`, so winning the branch is the conjunction of the
implication *the adversary rejects, or the clauses hold eventually* with the obligation that the
round robin wraps infinitely often.  Both are read off the branch, not guessed at a node, which is
what the earlier designs could not arrange. -/
theorem branch_condition_iff
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4) :
    DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode bb n))) false ↔
      ((DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => A.prio (r (branchNode bb n)).q) false →
          ∃ N, ∀ n, N ≤ n → (r (branchNode bb n)).phi S pr.r = true) ∧
        (∀ K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).firedK = true)) := by
  classical
  have hshape : ∀ n, (automaton S A pr).priority (r (branchNode bb n)) =
      ParityUnion.meet (bImp (advBound A)) 1
        (fun k => (r (branchNode bb k)).uPrio A S pr.r)
        (fun k => (r (branchNode bb k)).cK) n := by
    intro n
    show (r (branchNode bb n)).prio A S pr.r = _
    rw [St.prio, run_rec2 h0 hstep bb n]
    rfl
  have hu : ∀ n, (r (branchNode bb n)).uPrio A S pr.r ≤ bImp (advBound A) :=
    fun n => ParityUnion.priority_bound _ _ _ _
  have hk : ∀ n, (r (branchNode bb n)).cK ≤ 1 := by
    intro n
    rw [St.cK]
    split <;> omega
  have hcl : ∀ n, (r (branchNode bb n)).cP S pr.r ≤ 2 := by
    intro n
    rw [St.cP]
    split <;> omega
  have heq : ∀ n, (r (branchNode bb n)).uPrio A S pr.r =
      ParityUnion.combined (advBound A + 1) 2
        (fun k => A.prio (r (branchNode bb k)).q + 1)
        (fun k => (r (branchNode bb k)).cP S pr.r) n := by
    intro n
    rw [St.uPrio, run_rec1 h0 hstep bb n]
    rfl
  rw [funext hshape, ParityUnion.meet_correct hu hk, funext heq,
    ParityUnion.implication_correct (fun n => le_advBound A _) hcl]
  exact and_congr (imp_congr Iff.rfl colourWins_oneTwo) colourWins_zeroOne

/-- The implication and the obligation, on every branch. -/
theorem accepts_branch
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    (bb : ℕ → Fin 4) :
    (DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => A.prio (r (branchNode bb n)).q) false →
        ∃ N, ∀ n, N ≤ n → (r (branchNode bb n)).phi S pr.r = true) ∧
      (∀ K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).firedK = true) :=
  (branch_condition_iff h0 hstep bb).mp (hwin bb)

/-- **The branch condition suffices.**  This is the direction the backward construction needs. -/
theorem win_of_branch
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4)
    (himp : DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => A.prio (r (branchNode bb n)).q) false →
        ∃ N, ∀ n, N ≤ n → (r (branchNode bb n)).phi S pr.r = true)
    (hK : ∀ K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).firedK = true) :
    DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode bb n))) false :=
  (branch_condition_iff h0 hstep bb).mpr ⟨himp, hK⟩

/-- **The clauses hold eventually on every admissible branch.** -/
theorem accepts_phi
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    (bb : ℕ → Fin 4) (hσ : runOfBranch bb ∈ advOf A) :
    (∃ N, ∀ n, N ≤ n → (r (branchNode bb n)).phi S pr.r = true) ∧
      (∀ K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).firedK = true) := by
  have h := accepts_branch h0 hstep hwin bb
  refine ⟨h.1 ?_, h.2⟩
  have hq : (fun n => A.prio (r (branchNode bb n)).q)
      = fun n => A.prio (advRun A (fun i => dirLetter (bb i)) n) :=
    funext fun n => by rw [run_q_eq h0 hstep bb n]
  have hlet : (fun i => dirLetter (bb i)) = letter (runOfBranch bb) :=
    funext fun i => (letter_runOfBranch bb i).symm
  rw [hq, hlet]
  exact hσ

/-- **The two reception children of a node spawn the same check.**  The colour is the label at the
node and the obligation is one guess of the step, so both cones of a base carry the same check.
This is what makes the obligation a property of the base rather than of the letter. -/
theorem run_bad_spawn_agree
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (w : Node 4) (p : Bool) {i j : Fin 4} (hi : recDir p i = true) (hj : recDir p j = true) :
    ∃ b b', ((r (w ++ [i])).get p).bad = some b ∧ ((r (w ++ [j])).get p).bad = some b' ∧
      b.col = labOf (t w) p ∧ b'.col = labOf (t w) p ∧ b.required = b'.required ∧
      b.regime = true ∧ b'.regime = true := by
  obtain ⟨gu, gv, ru, rv, hstp⟩ := run_step hstep w
  have hpi := stepOk_p hstp p i
  have hpj := stepOk_p hstp p j
  rw [pStepOk] at hpi hpj
  simp only [Bool.and_eq_true] at hpi hpj
  have hbi := hpi.2
  have hbj := hpj.2
  rw [if_pos hi] at hbi
  rw [if_pos hj] at hbj
  match hci : ((r (w ++ [i])).get p).bad, hcj : ((r (w ++ [j])).get p).bad with
  | none, _ => rw [hci] at hbi; exact absurd hbi (by simp)
  | _, none => rw [hcj] at hbj; exact absurd hbj (by simp)
  | some b, some b' =>
      rw [hci] at hbi
      rw [hcj] at hbj
      simp only [Bool.and_eq_true, beq_iff_eq] at hbi hbj
      exact ⟨b, b', rfl, rfl, hbi.1.1, hbj.1.1, by rw [hbi.2, hbj.2], hbi.1.2, hbj.1.2⟩

/-- **The discharge obligation recurs on every branch**, admissible or not.  It is the second
conjunct of the branch condition, and it is what makes the bad set finite over the whole tree
rather than only along the branch that needs it. -/
theorem disch_recurs
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    (bb : ℕ → Fin 4) (p : Bool) :
    ∀ K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).disch p = true :=
  (run_roundRobinK hstep bb).of_fired (accepts_branch h0 hstep hwin bb).2 p

/-- Conversely the obligation recurs as soon as both processes' do. -/
theorem firedK_of_disch
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (bb : ℕ → Fin 4)
    (hd : ∀ p K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).disch p = true) :
    ∀ K, ∃ n, K ≤ n ∧ (r (branchNode bb n)).firedK = true :=
  (run_roundRobinK hstep bb).fired_of hd

/-- **Every branch eventually leaves the bad set behind.**  Four cases: the branch misses the base,
or leaves its cone at once by a non-reception letter, or enters and hears again, or enters and stays
silent, in which case the recurring discharge forces its check to seal. -/
theorem noBelow_eventually
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    {p : Bool} {h : List Letter} {c : K}
    (hspawn : ∀ w : Node 4, nodeHist w = h → ∀ g : Fin 4, recDir p g = true →
      ∃ b, ((r (w ++ [g])).get p).bad = some b ∧ b.col = c ∧ b.required = true ∧
        b.regime = true)
    (bb : ℕ → Fin 4) :
    ∃ n, NoBelow (Bad p (colOfTree pr t) (some h) c) (nodeHist (branchNode bb n)) := by
  classical
  set L := h.length with hL
  by_cases hpass : nodeHist (branchNode bb L) = h
  · by_cases hrec : recDir p (bb L) = true
    · obtain ⟨b0, hb0, hb0c, hb0r, hb0g⟩ := hspawn (branchNode bb L) hpass (bb L) hrec
      have hnode : ∀ k, nodeHist (branchNode bb (L + 1 + k)) =
          h ++ dirLetter (bb L) :: segLetters bb (L + 1) k := by
        intro k
        have : L + 1 + k = L + (k + 1) := by omega
        rw [this, nodeHist_branchNode_add, hpass, segLetters_cons]
      by_cases hlater : ∃ k, recDir p (bb (L + 1 + k)) = true
      · obtain ⟨k, hk⟩ := hlater
        refine ⟨L + 1 + (k + 1), ?_⟩
        rw [hnode (k + 1)]
        refine noBelow_of_not_silent (by rw [← recDir]; exact hrec) ?_
        refine ⟨dirLetter (bb (L + 1 + k)), mem_segLetters.mpr ⟨k, Nat.lt_succ_self k, rfl⟩, ?_⟩
        rw [← recDir]
        exact hk
      · push Not at hlater
        have hsil : ∀ k, recDir p (bb (L + 1 + k)) = false := by
          intro k
          exact Bool.eq_false_iff.mpr (hlater k)
        -- the check propagates unchanged, and the discharge forces it to seal
        obtain ⟨n, hn, hd⟩ := disch_recurs h0 hstep hwin bb p (L + 1 + 1)
        obtain ⟨k, hk⟩ : ∃ k, n = L + 1 + k := ⟨n - (L + 1), by omega⟩
        have hdirs : ∀ i ∈ segDirs bb (L + 1) k, recDir p i = false := by
          intro i hi
          obtain ⟨j, -, rfl⟩ := mem_segDirs.mp hi
          exact hsil j
        obtain ⟨b1, hb1, hcol1, hreq1, hreg1, hseal1⟩ :=
          run_bad_silent hstep hb0 (segDirs bb (L + 1) k) hdirs
        have hfold : branchNode bb n = branchNode bb L ++ [bb L] ++ segDirs bb (L + 1) k := by
          rw [hk, branchNode_add]
          rfl
        rw [← hfold] at hb1
        -- the discharge at `n` is the check being sealed
        have hlast : ((r (branchNode bb n)).get p).lastRec = false := by
          obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [Bool.eq_false_iff]
          intro hc
          rw [hm] at hc
          have := (run_lastRec hstep bb p m).mp hc
          rw [hears_runOfBranch] at this
          obtain ⟨k', hk'⟩ : ∃ k', m = L + 1 + k' := ⟨m - (L + 1), by omega⟩
          rw [hk'] at this
          rw [hsil k'] at this
          exact Bool.false_ne_true this
        have hok : ((r (branchNode bb n)).get p).ok = true := by
          rw [St.disch, hlast, Bool.false_or] at hd
          exact hd
        rw [PState.ok, hb1] at hok
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
        have hsealed : b1.sealed = true := by
          rcases hok with (hq | hq) | hq
          · rw [hreq1, hb0r] at hq
            exact absurd hq (by simp)
          · rw [hreg1, hb0g] at hq
            exact absurd hq (by simp)
          · exact hq
        refine ⟨n, ?_⟩
        have hfr : FirstReturn p (some h) (nodeHist (branchNode bb n)) := by
          rw [hk, hnode k]
          refine (firstReturn_cone (by rw [← recDir]; exact hrec)).mpr fun a ha => ?_
          obtain ⟨j, -, rfl⟩ := mem_segLetters.mp ha
          rw [← recDir]
          exact hsil j
        have := run_noBelow_sound hstep hb1 hsealed (by rw [hreg1, hb0g]) hfr
        rw [hcol1, hb0c] at this
        exact this
    · refine ⟨L + 1, ?_⟩
      have : nodeHist (branchNode bb (L + 1)) = h ++ [dirLetter (bb L)] := by
        show nodeHist (branchNode bb L ++ [bb L]) = _
        rw [nodeHist_append, hpass]
      rw [this]
      refine noBelow_of_nonrec ?_
      rw [← recDir]
      exact Bool.eq_false_iff.mpr hrec
  · refine ⟨L, noBelow_of_not_prefix (fun hc => ?_) (by simp [hL])⟩
    exact hpass (hc.eq_of_length (by simp [hL])).symm

/-- **The same for the initial base.**  Its cone is the whole subtree of histories in which the
process never hears, so the check is spawned at the root and the two cases are that the branch
hears at some point, or never does. -/
theorem noBelow_eventually_none
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    {p : Bool} {c : K} {b0 : BadChk K} (hb0 : ((r []).get p).bad = some b0)
    (hb0c : b0.col = c) (hb0r : b0.required = true) (hb0g : b0.regime = true)
    (bb : ℕ → Fin 4) :
    ∃ n, NoBelow (Bad p (colOfTree pr t) none c) (nodeHist (branchNode bb n)) := by
  classical
  by_cases hrec : ∃ k, recDir p (bb k) = true
  · obtain ⟨k, hk⟩ := hrec
    refine ⟨k + 1, noBelow_none_of_rec ⟨dirLetter (bb k), ?_, ?_⟩⟩
    · rw [show (k : ℕ) + 1 = 0 + (k + 1) by omega, nodeHist_branchNode_add]
      refine List.mem_append_right _ ?_
      refine mem_segLetters.mpr ⟨k, Nat.lt_succ_self k, ?_⟩
      congr 2
      omega
    · rw [← recDir]; exact hk
  · push Not at hrec
    have hsil : ∀ k, recDir p (bb k) = false := fun k => Bool.eq_false_iff.mpr (hrec k)
    obtain ⟨n, hn1, hd⟩ := disch_recurs h0 hstep hwin bb p 1
    have hdirs : ∀ i ∈ segDirs bb 0 n, recDir p i = false := by
      intro i hi
      obtain ⟨j, -, rfl⟩ := mem_segDirs.mp hi
      exact hsil (0 + j)
    obtain ⟨b1, hb1, hcol1, hreq1, hreg1, -⟩ := run_bad_silent hstep hb0 (segDirs bb 0 n) hdirs
    have hfold : branchNode bb n = [] ++ segDirs bb 0 n := by
      have h1 : branchNode bb (0 + n) = branchNode bb 0 ++ segDirs bb 0 n := branchNode_add bb 0 n
      rw [Nat.zero_add] at h1
      rw [h1]
      rfl
    rw [← hfold] at hb1
    have hlast : ((r (branchNode bb n)).get p).lastRec = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [hm] at hc
      have hh := (run_lastRec hstep bb p m).mp hc
      rw [hears_runOfBranch, hsil m] at hh
      exact Bool.false_ne_true hh
    have hok : ((r (branchNode bb n)).get p).ok = true := by
      rw [St.disch, hlast, Bool.false_or] at hd
      exact hd
    rw [PState.ok, hb1] at hok
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
    have hsealed : b1.sealed = true := by
      rcases hok with (hq | hq) | hq
      · rw [hreq1, hb0r] at hq; exact absurd hq (by simp)
      · rw [hreg1, hb0g] at hq; exact absurd hq (by simp)
      · exact hq
    refine ⟨n, ?_⟩
    have hfr : FirstReturn p none (nodeHist (branchNode bb n)) := by
      rw [show (n : ℕ) = 0 + n by omega, nodeHist_branchNode_add]
      intro a ha
      simp only [branchNode, nodeHist_nil, List.nil_append] at ha
      obtain ⟨j, -, rfl⟩ := mem_segLetters.mp ha
      rw [← recDir]
      exact hsil (0 + j)
    have := run_noBelow_sound hstep hb1 hsealed (by rw [hreg1, hb0g]) hfr
    rw [hcol1, hb0c] at this
    exact this

/-- **The check a run carries came from the spawn at its base**, and every reception child of that
base spawns the same one.  This turns a fact about one branch into the hypothesis of
`noBelow_eventually`, which is about all of them. -/
theorem spawn_of_run
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    {p : Bool} {bb : ℕ → Fin 4} {N : ℕ} {b : BadChk K}
    (hb : ((r (branchNode bb N)).get p).bad = some b) (hreq : b.required = true)
    {s : ℕ} (hs : s < N) (hrec : recDir p (bb s) = true)
    (hsil : ∀ i, s < i → i < N → recDir p (bb i) = false) :
    ∀ w : Node 4, nodeHist w = nodeHist (branchNode bb s) → ∀ g : Fin 4, recDir p g = true →
      ∃ b', ((r (w ++ [g])).get p).bad = some b' ∧ b'.col = b.col ∧ b'.required = true ∧
        b'.regime = true := by
  intro w hw g hg
  have hwe : w = branchNode bb s := nodeHist_injective hw
  subst hwe
  -- the check at the reception child of the base, on this branch
  obtain ⟨b1, b2, hb1, hb2, hc1, hc2, hr12, hg1, hg2⟩ :=
    run_bad_spawn_agree hstep (branchNode bb s) p hrec hg
  -- it propagates unchanged to `N`
  obtain ⟨k, hk⟩ : ∃ k, N = s + 1 + k := ⟨N - s - 1, by omega⟩
  have hdirs : ∀ i ∈ segDirs bb (s + 1) k, recDir p i = false := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_segDirs.mp hi
    exact hsil (s + 1 + j) (by omega) (by omega)
  obtain ⟨b3, hb3, hcol3, hreq3, hreg3, -⟩ := run_bad_silent hstep hb1 (segDirs bb (s + 1) k) hdirs
  have hfold : branchNode bb N = branchNode bb s ++ [bb s] ++ segDirs bb (s + 1) k := by
    rw [hk, branchNode_add]
    rfl
  rw [← hfold, hb] at hb3
  have hb3e : b3 = b := (Option.some_inj.mp hb3).symm
  subst hb3e
  refine ⟨b2, hb2, ?_, ?_, hg2⟩
  · rw [hc2, ← hc1, ← hcol3]
  · rw [← hr12, ← hreq3, hreq]

theorem phi_parts {s : St K AdvQ bd} {S : Spec K} {r : Bool → K} (h : s.phi S r = true) :
    ((S.deafOk false (r false) || s.pu.heard) = true ∧
        (S.deafOk true (r true) || s.pv.heard) = true) ∧
      (s.pu.term = true ∧ s.pv.term = true) ∧ S.rel s.pu.baseCol s.pv.baseCol = true := by
  rw [St.phi] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨⟨h.1.1.1.1, h.1.1.1.2⟩, ⟨h.1.1.2, h.1.2⟩, h.2⟩

/-- **Deafness.**  A process that never hears has an acceptable root colour. -/
theorem deaf_of_accepts
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    {σ : ℕ → Event Bool} (hσ : σ ∈ advOf A) (p : Bool) (hm : Muted p σ) :
    S.deafOk p (pr.r p) = true := by
  set bb : ℕ → Fin 4 := fun i => letterDir (letter σ i) with hbb
  have hb : runOfBranch bb = σ := runOfBranch_letterDir σ
  obtain ⟨⟨N, hN⟩, -⟩ := accepts_phi h0 hstep hwin bb (by rw [hb]; exact hσ)
  obtain ⟨⟨hu, hv⟩, -, -⟩ := phi_parts (hN N le_rfl)
  have hheard : ((r (branchNode bb N)).get p).heard = false := by
    rw [Bool.eq_false_iff]
    intro hc
    obtain ⟨i, -, hi⟩ := (run_heard hstep h0 bb p N).mp hc
    rw [hb] at hi
    exact hm i hi
  cases p
  · rw [St.get_false] at hheard
    rw [hheard, Bool.or_false] at hu
    exact hu
  · rw [St.get_true] at hheard
    rw [hheard, Bool.or_false] at hv
    exact hv

/-- **The relation.**  The two current base colours eventually satisfy the spec's relation. -/
theorem agree_of_accepts
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    {σ : ℕ → Event Bool} (hσ : σ ∈ advOf A) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      S.rel (colOfTree pr t U (base U σ n)) (colOfTree pr t W (base W σ n)) = true := by
  set bb : ℕ → Fin 4 := fun i => letterDir (letter σ i) with hbb
  have hb : runOfBranch bb = σ := runOfBranch_letterDir σ
  obtain ⟨⟨N, hN⟩, -⟩ := accepts_phi h0 hstep hwin bb (by rw [hb]; exact hσ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨-, -, hag⟩ := phi_parts (hN n hn)
  have hcu := run_baseCol hstep h0 bb U n
  have hcv := run_baseCol hstep h0 bb W n
  rw [hb] at hcu hcv
  rw [← hcu, ← hcv]
  exact hag

/-- **Termination.**  Either the process reaches a good reception, or it falls silent at a base
whose bad set is finite. -/
theorem term_of_accepts
    (h0 : r [] = initSt A pr)
    (hstep : ∀ w, (automaton S A pr).delta (r w) (t w) (fun i => r (w ++ [i])))
    (hwin : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins (fun n => (automaton S A pr).priority (r (branchNode b n))) false)
    {σ : ℕ → Event Bool} (hσ : σ ∈ advOf A) (p : Bool) :
    (∃ i, Hears p σ i ∧ ∀ a : Letter, a.hears p = true →
      AllCol p (colOfTree pr t) (pre σ i ++ [a]) (colOfTree pr t p (some (pre σ i)))) ∨
    (∃ N, (∀ i, N ≤ i → ¬ Hears p σ i) ∧
      ∀ β : ℕ → List Letter, β 0 = [] → IsBranch β →
        ∃ n, NoBelow (Bad p (colOfTree pr t) (base p σ N)
          (colOfTree pr t p (base p σ N))) (β n)) := by
  classical
  set bb : ℕ → Fin 4 := fun i => letterDir (letter σ i) with hbb
  have hb : runOfBranch bb = σ := runOfBranch_letterDir σ
  obtain ⟨⟨N, hN⟩, -⟩ := accepts_phi h0 hstep hwin bb (by rw [hb]; exact hσ)
  by_cases hgd : ∃ n, ((r (branchNode bb n)).get p).goodDone = true
  · obtain ⟨n, hn⟩ := hgd
    obtain ⟨i, -, hh, hall⟩ := run_goodDone_sound hstep h0 bb p n hn
    rw [hb] at hh hall
    exact Or.inl ⟨i, hh, hall⟩
  · push Not at hgd
    have hterm : ∀ n, N ≤ n → ((r (branchNode bb n)).get p).sealedHere = true ∧
        ((r (branchNode bb n)).get p).lastRec = false := by
      intro n hn
      obtain ⟨-, hts, -⟩ := phi_parts (hN n hn)
      have ht : ((r (branchNode bb n)).get p).term = true := by
        cases p
        · exact hts.1
        · exact hts.2
      rw [PState.term] at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at ht
      rcases ht with hg | ⟨hl, hs⟩
      · exact absurd hg (hgd n)
      · exact ⟨hs, hl⟩
    have hsilence : ∀ m, N ≤ m → ¬ Hears p σ m := by
      intro m hm hc
      have hl := (hterm (m + 1) (by omega)).2
      rw [← hb] at hc
      have := (run_lastRec hstep bb p m).mpr hc
      rw [hl] at this
      exact Bool.false_ne_true this
    refine Or.inr ⟨N, hsilence, ?_⟩
    -- the check at time `N`
    obtain ⟨hsealed, -⟩ := hterm N le_rfl
    rw [PState.sealedHere] at hsealed
    match hbadN : ((r (branchNode bb N)).get p).bad with
    | none => rw [hbadN] at hsealed; exact absurd hsealed (by simp)
    | some b =>
        rw [hbadN] at hsealed
        simp only [Bool.and_eq_true] at hsealed
        obtain ⟨⟨hreq, hreg⟩, hsl⟩ := hsealed
        have hcolb : b.col = colOfTree pr t p (base p σ N) := by
          obtain ⟨b', hb', hcol'⟩ := run_bad_col hstep h0 p (branchNode bb N)
          rw [hbadN] at hb'
          have hbe : b' = b := (Option.some_inj.mp hb').symm
          subst hbe
          rw [hcol']
          have := run_baseCol hstep h0 bb p N
          rw [hb] at this
          exact this
        intro β hβ0 hβ
        obtain ⟨bb', hbb'⟩ := exists_dirBranch hβ0 hβ
        rcases hbaseN : base p σ N with _ | h
        · -- the initial base: the check propagates from the root
          have hnorec : ∀ i, i < N → ¬ Hears p σ i := by
            rcases base_cases (p := p) (σ := σ) N with ⟨-, hs⟩ | ⟨s, -, -, -, hbs⟩
            · exact hs
            · rw [hbaseN] at hbs; exact absurd hbs (by simp)
          have hdirs : ∀ i ∈ segDirs bb 0 N, recDir p i = false := by
            intro i hi
            obtain ⟨j, hj, rfl⟩ := mem_segDirs.mp hi
            rw [Bool.eq_false_iff]
            intro hc
            refine hnorec (0 + j) (by omega) ?_
            rw [← hb, hears_runOfBranch]
            exact hc
          obtain ⟨b0, hb0⟩ : ∃ b0, ((r []).get p).bad = some b0 := by
            cases p
            · exact ⟨_, by rw [h0]; rfl⟩
            · exact ⟨_, by rw [h0]; rfl⟩
          obtain ⟨b1, hb1, hc1, hr1, hg1, -⟩ := run_bad_silent hstep hb0 (segDirs bb 0 N) hdirs
          have hfold : branchNode bb N = [] ++ segDirs bb 0 N := by
            have h1 := branchNode_add bb 0 N
            rw [Nat.zero_add] at h1
            rw [h1]; rfl
          rw [← hfold, hbadN] at hb1
          have hb1e : b1 = b := (Option.some_inj.mp hb1).symm
          subst hb1e
          obtain ⟨n, hn⟩ := noBelow_eventually_none h0 hstep hwin hb0
            (by rw [← hc1, hcolb, hbaseN]) (by rw [← hr1, hreq]) (by rw [← hg1, hreg]) bb'
          exact ⟨n, by rw [hbb' n]; exact hn⟩
        · -- a received base: use the spawn
          obtain ⟨s, hsN, hrs, hsil, hbs⟩ :
              ∃ s, s < N ∧ Hears p σ s ∧ (∀ i, s < i → i < N → ¬ Hears p σ i) ∧
                base p σ N = some (pre σ s) := by
            rcases base_cases (p := p) (σ := σ) N with ⟨hb0', -⟩ | ⟨s, h1, h2, h3, h4⟩
            · rw [hbaseN] at hb0'; exact absurd hb0' (by simp)
            · exact ⟨s, h1, h2, h3, h4⟩
          have hhe : h = pre σ s := by
            rw [hbaseN] at hbs
            exact Option.some_inj.mp hbs
          have hspawn := spawn_of_run hstep hbadN hreq hsN
            (by rw [← hb, hears_runOfBranch] at hrs; exact hrs)
            (fun i h1 h2 => by
              rw [Bool.eq_false_iff]
              intro hc
              exact hsil i h1 h2 (by rw [← hb, hears_runOfBranch]; exact hc))
          obtain ⟨n, hn⟩ := noBelow_eventually h0 hstep hwin
            (h := nodeHist (branchNode bb s)) (c := b.col)
            (fun w hw g hg => hspawn w hw g hg) bb'
          refine ⟨n, ?_⟩
          rw [hbb' n]
          have hnh : nodeHist (branchNode bb s) = h := by
            rw [hhe, ← hb, ← pre_runOfBranch]
          rw [hnh] at hn
          rw [hcolb, hbaseN] at hn
          exact hn

end Run

/-- A colouring of the bases by `K` with prescribed root colours, satisfying the spec's deafness
condition, the termination clause, and the spec's relation eventually along every admissible run. -/
structure GenColouring (S : Spec K) (adv : Set (ℕ → Event Bool)) (r : Bool → K)
    (D : Bool → Base → K) : Prop where
  /-- The root colours are the prescribed ones. -/
  root : ∀ p, D p none = r p
  /-- A process that never hears has an acceptable root colour. -/
  deaf : ∀ σ ∈ adv, ∀ p, Muted p σ → S.deafOk p (r p) = true
  /-- Each process hears at a good base, or falls silent at a base whose bad set is finite. -/
  term : ∀ σ ∈ adv, ∀ p,
    (∃ i, Hears p σ i ∧ ∀ a : Letter, a.hears p = true →
      AllCol p D (pre σ i ++ [a]) (D p (some (pre σ i)))) ∨
    (∃ N, (∀ i, N ≤ i → ¬ Hears p σ i) ∧
      ∀ β : ℕ → List Letter, β 0 = [] → IsBranch β →
        ∃ n, NoBelow (Bad p D (base p σ N) (D p (base p σ N))) (β n))
  /-- The two current colours eventually satisfy the relation. -/
  rel : ∀ σ ∈ adv, ∃ n₀, ∀ n, n₀ ≤ n →
    S.rel (D U (base U σ n)) (D W (base W σ n)) = true

/-- **The forward direction.**  An accepting labelled tree is a labelling. -/
theorem genColouring_of_accepts (A : Adv AdvQ) (pr : Params K) {t : Node 4 → K × K}
    (h : (automaton S A pr).acceptsTree t) : GenColouring S (advOf A) pr.r (colOfTree pr t) := by
  obtain ⟨r, ⟨h0, hstep⟩, hwin⟩ := h
  have hw : ∀ b : ℕ → Fin 4,
      DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins
        (fun n => (automaton S A pr).priority (r (branchNode b n))) false :=
    fun b => (DistributedSynthesis.DecisionTasks.Source.FiniteParity.colourWins_false_iff _).mpr (hwin b)
  exact { root := fun _ => rfl
          deaf := fun σ hσ p hm => deaf_of_accepts h0 hstep hw hσ p hm
          term := fun σ hσ p => term_of_accepts h0 hstep hw hσ p
          rel := fun σ hσ => agree_of_accepts h0 hstep hw hσ }

/-- Solvability of the labelling problem at prescribed root colours, as read by the automaton. -/
def AutSolvableAt (S : Spec K) (A : Adv AdvQ) (r : Bool → K) : Prop :=
  ∃ pr : Params K, pr.r = r ∧ (∃ t, (automaton S A pr).acceptsTree t)

/-- **The forward direction, for the automaton.** -/
theorem genColouring_of_autSolvableAt (A : Adv AdvQ) (r : Bool → K) (h : AutSolvableAt S A r) :
    ∃ D, GenColouring S (advOf A) r D := by
  obtain ⟨pr, hpr, t, ht⟩ := h
  exact ⟨_, hpr ▸ genColouring_of_accepts A pr ht⟩

/-- Regular task witnesses use the shared run-based tree-automaton basis theorem. -/
theorem regular_of_autSolvableAt (A : Adv AdvQ) (r : Bool → K) (h : AutSolvableAt S A r) :
    ∃ (pr : Params K) (tree : TransitionRationalTree.{0, 0, 0} (Fin 4) (K × K)),
      pr.r = r ∧ (automaton S A pr).acceptsTree tree.labeledTree := by
  obtain ⟨pr, hpr, tree, ht⟩ := h
  obtain ⟨regular, hregular⟩ :=
    (automaton S A pr).exists_transitionRational_accepted ⟨tree, ht⟩
  exact ⟨pr, regular, hpr, hregular⟩

/-- **It is decidable**, and by an algorithm: there are finitely many remaining root guesses, and
the shared tree backend searches finite positional policies and their finite orbits. -/
instance decidableAutSolvableAt (S : Spec K) (A : Adv AdvQ) (r : Bool → K) :
    Decidable (AutSolvableAt S A r) :=
  letI : ∀ pr : Params K, Decidable (pr.r = r ∧ (∃ t, (automaton S A pr).acceptsTree t)) :=
    fun pr => letI := (automaton S A pr).nonemptyDecidable; inferInstance
  Fintype.decidableExistsFintype

end ColAut

end DistributedSynthesis.DecisionTasks.Source
