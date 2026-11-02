/- Extracted from consensusLTL/lean/ConsensusLTL/Back.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.ColAut
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Konig
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Views
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.NodeTransport
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Parity
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Union

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

namespace ColAut

namespace Back

open DistributedSynthesis.DecisionTasks.Source.FiniteParity.TreeAutomaton
open scoped Classical

variable {K : Type} [Fintype K] [DecidableEq K]
variable {AdvQ : Type} [Fintype AdvQ] [DecidableEq AdvQ]
variable (S : Spec K)

/-- The node carrying the base of `p`, read off the reversed node. -/
def baseNodeRev (p : Bool) : List (Fin 4) → Option (Node 4)
  | [] => none
  | i :: v => if recDir p i then some v.reverse else baseNodeRev p v

/-- The longest proper prefix of `w` out of which the step along `w` is a reception for `p`. -/
def baseNode (p : Bool) (w : Node 4) : Option (Node 4) := baseNodeRev p w.reverse

theorem baseNode_append (p : Bool) (w : Node 4) (i : Fin 4) :
    baseNode p (w ++ [i]) = if recDir p i then some w else baseNode p w := by
  show baseNodeRev p (w ++ [i]).reverse = _
  rw [List.reverse_append]
  show (if recDir p i then some w.reverse.reverse else baseNodeRev p w.reverse) = _
  rw [List.reverse_reverse]
  rfl

/-- The base of `p` at `w`, as a history. -/
def baseOf (p : Bool) (w : Node 4) : Base := (baseNode p w).map nodeHist

theorem baseOf_append (p : Bool) (w : Node 4) (i : Fin 4) :
    baseOf p (w ++ [i]) = if recDir p i then some (nodeHist w) else baseOf p w := by
  rw [baseOf, baseNode_append]
  split <;> rfl

/-- The last step into `w` is a reception for `p`. -/
def lastRecRev (p : Bool) : List (Fin 4) → Bool
  | [] => false
  | i :: _ => recDir p i

/-- The last step into `w` is a reception for `p`. -/
def lastRec (p : Bool) (w : Node 4) : Bool := lastRecRev p w.reverse

theorem lastRec_append (p : Bool) (w : Node 4) (i : Fin 4) :
    lastRec p (w ++ [i]) = recDir p i := by
  show lastRecRev p (w ++ [i]).reverse = _
  rw [List.reverse_append]
  rfl

/-- `p` has heard along `w`. -/
def heard (p : Bool) (w : Node 4) : Bool := decide (∃ i ∈ w, recDir p i = true)

theorem heard_append (p : Bool) (w : Node 4) (i : Fin 4) :
    heard p (w ++ [i]) = (heard p w || recDir p i) := by
  rw [Bool.eq_iff_iff]
  simp only [heard, List.mem_append, List.mem_singleton, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj | rfl, hjr⟩
    · exact Or.inl ⟨j, hj, hjr⟩
    · exact Or.inr hjr
  · rintro (⟨j, hj, hjr⟩ | hi)
    · exact ⟨j, Or.inl hj, hjr⟩
    · exact ⟨i, Or.inr rfl, hi⟩

variable (C : Bool → Base → K)

/-- The colour of the base of `p` at `w`. -/
def baseCol (p : Bool) (w : Node 4) : K := C p (baseOf p w)

theorem baseCol_append (p : Bool) (w : Node 4) (i : Fin 4) :
    baseCol C p (w ++ [i]) = if recDir p i then C p (some (nodeHist w)) else baseCol C p w := by
  rw [baseCol, baseOf_append]
  split <;> rfl

/-- The node is good for `p`: its own colour, and every cone above a reception, is its colour. -/
noncomputable def goodAt (p : Bool) (w : Node 4) : Bool :=
  decide (Good p C (nodeHist w) (C p (some (nodeHist w))))

/-- Some ancestor of `w` was good for `p` and was left by a reception. -/
noncomputable def goodDoneRev (p : Bool) : List (Fin 4) → Bool
  | [] => false
  | i :: v => goodDoneRev p v || (goodAt C p v.reverse && recDir p i)

/-- Some ancestor of `w` was good for `p` and was left by a reception. -/
noncomputable def goodDone (p : Bool) (w : Node 4) : Bool := goodDoneRev C p w.reverse

theorem goodDone_append (p : Bool) (w : Node 4) (i : Fin 4) :
    goodDone C p (w ++ [i]) = (goodDone C p w || (goodAt C p w && recDir p i)) := by
  show goodDoneRev C p (w ++ [i]).reverse = _
  rw [List.reverse_append]
  show (goodDoneRev C p w.reverse || (goodAt C p w.reverse.reverse && recDir p i)) = _
  rw [List.reverse_reverse]
  rfl

/-- The cone below `w` is monochromatic for `p`.  The root is left unmarked so that the initial
state matches `initP`, which is harmless: a check is only ever used downwards. -/
noncomputable def allColAt (p : Bool) (w : Node 4) : Option K :=
  if w ≠ [] ∧ AllCol p C (nodeHist w) (C p (some (nodeHist w))) then
    some (C p (some (nodeHist w))) else none

/-- The bad set of the check spawned by a reception out of `w` is finite. -/
noncomputable def reqAt (p : Bool) (w : Node 4) : Bool :=
  decide ((Bad p C (some (nodeHist w)) (C p (some (nodeHist w)))).Finite)

/-- The check live at `w` is required: its bad set is finite, so every branch can be asked to seal
it. -/
noncomputable def reqOf (p : Bool) (w : Node 4) : Bool :=
  decide ((Bad p C (baseOf p w) (baseCol C p w)).Finite)

theorem reqOf_append (p : Bool) (w : Node 4) (i : Fin 4) :
    reqOf C p (w ++ [i]) = if recDir p i then reqAt C p w else reqOf C p w := by
  by_cases h : recDir p i = true
  · rw [reqOf, baseOf_append, baseCol_append, if_pos h, if_pos h, if_pos h, reqAt]
  · rw [reqOf, baseOf_append, baseCol_append, if_neg h, if_neg h, if_neg h, reqOf]

/-- No bad first return of the current base remains at or below `w`. -/
noncomputable def sealOf (p : Bool) (w : Node 4) : Bool :=
  decide (NoBelow (Bad p C (baseOf p w) (baseCol C p w)) (nodeHist w))

/-- `NoBelow` is inherited downwards. -/
theorem noBelow_mono {S : Set (List Letter)} {x y : List Letter} (h : NoBelow S x)
    (hxy : x <+: y) : NoBelow S y := fun j hj => h j (hxy.trans hj)

/-- The history of a node is a first return of its own base.  This is the cone picture: the base is
the node just before the last reception, and everything since is silent. -/
theorem firstReturn_baseOf (p : Bool) (w : Node 4) : FirstReturn p (baseOf p w) (nodeHist w) := by
  induction w using List.reverseRecOn with
  | nil => intro g hg; exact absurd hg (by simp)
  | append_singleton w i ih =>
      rw [baseOf_append, nodeHist_append]
      by_cases h : recDir p i = true
      · rw [if_pos h]
        exact ⟨dirLetter i, [], h, fun g' hg' => absurd hg' (by simp), rfl⟩
      · rw [Bool.not_eq_true] at h
        rw [if_neg (by simp [h])]
        match hb : baseOf p w with
        | none =>
            rw [hb] at ih
            intro g hg
            rcases List.mem_append.mp hg with hg | hg
            · exact ih g hg
            · rw [List.mem_singleton.mp hg]; exact h
        | some hh =>
            rw [hb] at ih
            obtain ⟨g, t, hgp, hts, hw⟩ := ih
            refine ⟨g, t ++ [dirLetter i], hgp, ?_, ?_⟩
            · intro g' hg'
              rcases List.mem_append.mp hg' with hg' | hg'
              · exact hts g' hg'
              · rw [List.mem_singleton.mp hg']; exact h
            · rw [hw]
              simp

/-- A sealed check makes its node good: the node is itself a first return of the base, and no bad
first return remains at or below it. -/
theorem good_of_seal {p : Bool} {w : Node 4} (h : sealOf C p w = true) :
    Good p C (nodeHist w) (baseCol C p w) := by
  have hnb : NoBelow (Bad p C (baseOf p w) (baseCol C p w)) (nodeHist w) := of_decide_eq_true h
  have hmem := hnb (nodeHist w) List.prefix_rfl
  by_contra hg
  exact hmem ⟨firstReturn_baseOf p w, hg⟩

/-- A sealed check is still sealed one silent step down. -/
theorem sealOf_of_sealOf {p : Bool} {w : Node 4} {i : Fin 4} (hi : recDir p i = false)
    (h : sealOf C p w = true) : sealOf C p (w ++ [i]) = true := by
  have hnb : NoBelow (Bad p C (baseOf p w) (baseCol C p w)) (nodeHist w) := of_decide_eq_true h
  rw [sealOf, baseOf_append, baseCol_append, if_neg (by simp [hi]), if_neg (by simp [hi]),
    decide_eq_true_eq, nodeHist_append]
  exact noBelow_mono hnb ⟨[dirLetter i], rfl⟩

/-- A live cone check is inherited by every child, with the same colour. -/
theorem allColAt_append {p : Bool} {w : Node 4} {c : K} (h : allColAt C p w = some c)
    (i : Fin 4) : allColAt C p (w ++ [i]) = some c := by
  rw [allColAt] at h
  split at h
  · rename_i hw
    have hc : C p (some (nodeHist w)) = c := by
      simpa using h
    have hall := hw.2
    have hpre : (nodeHist w) <+: nodeHist (w ++ [i]) := by
      rw [nodeHist_append]
      exact ⟨[dirLetter i], rfl⟩
    have hhere : C p (some (nodeHist (w ++ [i]))) = c := by
      rw [← hc]; exact hall _ hpre
    have hall2 : AllCol p C (nodeHist (w ++ [i])) (C p (some (nodeHist (w ++ [i])))) := by
      rw [hhere]
      intro j hj
      rw [← hc]
      exact hall j (hpre.trans hj)
    rw [allColAt, if_pos ⟨by simp, hall2⟩, hhere]
  · exact absurd h (by simp)

/-- A good node spawns a monochromatic cone in every reception direction. -/
theorem allColAt_of_good {p : Bool} {w : Node 4} (h : Good p C (nodeHist w) (C p (some (nodeHist w))))
    {j : Fin 4} (hj : recDir p j = true) :
    allColAt C p (w ++ [j]) = some (C p (some (nodeHist w))) := by
  have hall := (good_iff_allCol.mp h).2 (dirLetter j) hj
  rw [← nodeHist_append] at hall
  have hhere : C p (some (nodeHist (w ++ [j]))) = C p (some (nodeHist w)) :=
    hall _ List.prefix_rfl
  have hall2 : AllCol p C (nodeHist (w ++ [j])) (C p (some (nodeHist (w ++ [j])))) := by
    rw [hhere]; exact hall
  rw [allColAt, if_pos ⟨by simp, hall2⟩, hhere]

/-- The per-process annotation at a node. -/
noncomputable def pstate (p : Bool) (w : Node 4) : PState K where
  goodDone := goodDone C p w
  heard := heard p w
  baseCol := baseCol C p w
  lastRec := lastRec p w
  allCol := allColAt C p w
  bad := some { col := baseCol C p w, required := reqOf C p w, regime := true,
                sealed := sealOf C p w }

/-- The labelled tree: each node carries the colour its history has. -/
def labTree (w : Node 4) : K × K := (C false (some (nodeHist w)), C true (some (nodeHist w)))

@[simp] theorem labOf_labTree (w : Node 4) (p : Bool) :
    labOf (labTree C w) p = C p (some (nodeHist w)) := by
  cases p <;> rfl

/-- The root guesses. -/
noncomputable def params : Params K where
  r := fun p => C p none
  requ := reqOf C false []
  reqv := reqOf C true []
  sealu := sealOf C false []
  sealv := sealOf C true []

theorem pstate_nil (p : Bool) :
    pstate C p [] = initP (C p none) (reqOf C p []) (sealOf C p []) := by
  rw [pstate, initP]
  congr 1

variable (A : Adv AdvQ)

/-- The run of the automaton over the labelled tree, by recursion on the reversed node.  Everything
except the two per-process annotations is forced by the transition. -/
noncomputable def runRev : List (Fin 4) → St K AdvQ (advBound A)
  | [] => initSt A (params C)
  | i :: v =>
      { q := A.step (runRev v).q (dirLetter i)
        pu := pstate C false (v.reverse ++ [i])
        pv := pstate C true (v.reverse ++ [i])
        rrK := if (runRev v).disch (runRev v).rrK then !(runRev v).rrK else (runRev v).rrK
        rec1 := (runRev v).rec1Next A S (params C).r
        rec2 := (runRev v).rec2Next A S (params C).r }

/-- The run, as a function on nodes. -/
noncomputable def runSt (w : Node 4) : St K AdvQ (advBound A) := runRev S C A w.reverse

theorem runSt_nil : runSt S C A [] = initSt A (params C) := rfl

theorem runSt_append (w : Node 4) (i : Fin 4) :
    runSt S C A (w ++ [i]) =
      { q := A.step (runSt S C A w).q (dirLetter i)
        pu := pstate C false (w ++ [i])
        pv := pstate C true (w ++ [i])
        rrK := if (runSt S C A w).disch (runSt S C A w).rrK then !(runSt S C A w).rrK
               else (runSt S C A w).rrK
        rec1 := (runSt S C A w).rec1Next A S (params C).r
        rec2 := (runSt S C A w).rec2Next A S (params C).r } := by
  show runRev S C A (w ++ [i]).reverse = _
  rw [List.reverse_append]
  show (⟨A.step (runRev S C A w.reverse).q (dirLetter i), pstate C false (w.reverse.reverse ++ [i]),
      pstate C true (w.reverse.reverse ++ [i]), _, _, _⟩ : St K AdvQ (advBound A)) = _
  rw [List.reverse_reverse]
  rfl

/-- The per-process component of the run is the annotation. -/
theorem runSt_get (p : Bool) (w : Node 4) : (runSt S C A w).get p = pstate C p w := by
  induction w using List.reverseRecOn with
  | nil =>
      rw [runSt_nil]
      cases p
      · show initP ((params C).r false) (params C).requ (params C).sealu = _
        rw [pstate_nil]
        rfl
      · show initP ((params C).r true) (params C).reqv (params C).sealv = _
        rw [pstate_nil]
        rfl
  | append_singleton w i _ =>
      rw [runSt_append]
      cases p <;> rfl

theorem runSt_pu (w : Node 4) : (runSt S C A w).pu = pstate C false w := runSt_get S C A false w

theorem runSt_pv (w : Node 4) : (runSt S C A w).pv = pstate C true w := runSt_get S C A true w

theorem labelOk_run (w : Node 4) : labelOk (runSt S C A w) (labOf (labTree C w)) = true := by
  have hu := runSt_pu S C A w
  have hv := runSt_pv S C A w
  have key : ∀ p : Bool,
      (match (pstate C p w).allCol with
        | none => true
        | some c => C p (some (nodeHist w)) == c) = true ∧
      (match (pstate C p w).bad with
        | none => true
        | some b => !(b.sealed && b.regime) || (C p (some (nodeHist w)) == b.col)) = true := by
    intro p
    constructor
    · show (match allColAt C p w with
        | none => true | some c => C p (some (nodeHist w)) == c) = true
      match hc : allColAt C p w with
      | none => rfl
      | some c =>
          rw [allColAt] at hc
          split at hc
          · simp only [Option.some.injEq] at hc
            simp [hc]
          · exact absurd hc (by simp)
    · show (!(sealOf C p w && true) || (C p (some (nodeHist w)) == baseCol C p w)) = true
      by_cases h : sealOf C p w = true
      · rw [h]
        simp only [Bool.and_true, Bool.not_true, Bool.false_or, beq_iff_eq]
        exact (good_of_seal C h).1
      · rw [Bool.not_eq_true] at h
        rw [h]
        rfl
  rw [labelOk, hu, hv]
  simp only [labOf_labTree, Bool.and_eq_true]
  exact ⟨⟨⟨(key false).1, (key true).1⟩, (key false).2⟩, (key true).2⟩

theorem pStepOk_run (p : Bool) (w : Node 4) (i : Fin 4) :
    pStepOk p (runSt S C A w) (labOf (labTree C w)) (fun j => runSt S C A (w ++ [j]))
      (goodAt C p w) (reqAt C p w) i = true := by
  have hs : ∀ v : Node 4, (runSt S C A v).get p = pstate C p v := runSt_get S C A p
  have hspawn : ∀ c : K, Good p C (nodeHist w) c →
      spawnCone p c (fun j => runSt S C A (w ++ [j])) = true := by
    intro c hc
    have hcol : C p (some (nodeHist w)) = c := hc.1
    rw [spawnCone, decide_eq_true_eq]
    intro j hj
    rw [hs]
    show allColAt C p (w ++ [j]) = some c
    rw [← hcol]
    exact allColAt_of_good C (by rw [hcol]; exact hc) hj
  simp only [pStepOk, hs, labOf_labTree, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show (heard p (w ++ [i]) == (heard p w || recDir p i)) = true
    rw [heard_append]
    simp
  · show (baseCol C p (w ++ [i]) ==
      (if recDir p i = true then C p (some (nodeHist w)) else baseCol C p w)) = true
    rw [baseCol_append]
    simp
  · show (lastRec p (w ++ [i]) == recDir p i) = true
    rw [lastRec_append]
    simp
  · show (goodDone C p (w ++ [i]) == (goodDone C p w || (goodAt C p w && recDir p i))) = true
    rw [goodDone_append]
    simp
  · show (!goodAt C p w || spawnCone p (C p (some (nodeHist w)))
      (fun j => runSt S C A (w ++ [j]))) = true
    by_cases h : goodAt C p w = true
    · rw [h, hspawn _ (of_decide_eq_true h)]
      rfl
    · rw [Bool.not_eq_true] at h
      rw [h]
      rfl
  · show (match allColAt C p w with
      | none => true | some c => allColAt C p (w ++ [i]) == some c) = true
    match hc : allColAt C p w with
    | none => rfl
    | some c => rw [allColAt_append C hc i]; simp
  · show (!(sealOf C p w && true) ||
      spawnCone p (baseCol C p w) (fun j => runSt S C A (w ++ [j]))) = true
    by_cases h : sealOf C p w = true
    · rw [h, hspawn _ (good_of_seal C h)]
      simp
    · rw [Bool.not_eq_true] at h
      rw [h]
      rfl
  · by_cases h : recDir p i = true
    · rw [if_pos h]
      show (match (pstate C p (w ++ [i])).bad with
        | none => false
        | some b' => (b'.col == C p (some (nodeHist w))) && b'.regime &&
            (b'.required == reqAt C p w)) = true
      show ((baseCol C p (w ++ [i]) == C p (some (nodeHist w))) && true &&
        (reqOf C p (w ++ [i]) == reqAt C p w)) = true
      rw [baseCol_append, reqOf_append, if_pos h, if_pos h]
      simp
    · rw [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      show (match (pstate C p w).bad, (pstate C p (w ++ [i])).bad with
        | none, none => true
        | some b, some b' => (b'.col == b.col) && (b'.required == b.required) &&
            (b'.regime == b.regime) && (!b.sealed || b'.sealed)
        | _, _ => false) = true
      show ((baseCol C p (w ++ [i]) == baseCol C p w) &&
        (reqOf C p (w ++ [i]) == reqOf C p w) && (true == true) &&
        (!sealOf C p w || sealOf C p (w ++ [i]))) = true
      rw [baseCol_append, reqOf_append, if_neg (by simp [h]), if_neg (by simp [h])]
      simp only [beq_self_eq_true, Bool.and_true, Bool.true_and, Bool.or_eq_true,
        Bool.not_eq_true']
      by_cases hsl : sealOf C p w = true
      · exact Or.inr (sealOf_of_sealOf C h hsl)
      · exact Or.inl (by simpa using hsl)

theorem recStepOk_run (w : Node 4) (i : Fin 4) :
    recStepOk S A (params C) (runSt S C A w) (fun j => runSt S C A (w ++ [j])) i = true := by
  rw [recStepOk]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · show (runSt S C A (w ++ [i])).rec1 = _
    rw [runSt_append]
  · show (runSt S C A (w ++ [i])).rec2 = _
    rw [runSt_append]

theorem rrStepOk_run (w : Node 4) (i : Fin 4) :
    rrStepOk (runSt S C A w) (fun j => runSt S C A (w ++ [j])) i = true := by
  rw [rrStepOk]
  show ((runSt S C A (w ++ [i])).rrK == _) = true
  rw [runSt_append]
  simp

theorem stepOk_run (w : Node 4) :
    stepOk S A (params C) (runSt S C A w) (labOf (labTree C w)) (fun j => runSt S C A (w ++ [j]))
      (goodAt C false w) (goodAt C true w) (reqAt C false w) (reqAt C true w) = true := by
  rw [stepOk]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨labelOk_run S C A w, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro i
    show (runSt S C A (w ++ [i])).q = _
    rw [runSt_append]
  · exact fun i => pStepOk_run S C A false w i
  · exact fun i => pStepOk_run S C A true w i
  · exact fun i => recStepOk_run S C A w i
  · exact fun i => rrStepOk_run S C A w i

/-- The run really is a run of the automaton over the labelled tree. -/
theorem run_mem_trans (w : Node 4) :
    (automaton S A (params C)).delta (runSt S C A w)
      (labTree C w) (fun i => runSt S C A (w ++ [i])) := by
  exact ⟨goodAt C false w, goodAt C true w, reqAt C false w, reqAt C true w, stepOk_run S C A w⟩

theorem ok_pstate (p : Bool) (w : Node 4) :
    (pstate C p w).ok = (!reqOf C p w || sealOf C p w) := by
  show (!(reqOf C p w) || !true || sealOf C p w) = _
  simp

theorem disch_pstate {p : Bool} (w : Node 4)
    (h : lastRec p w = true ∨ reqOf C p w = false ∨ sealOf C p w = true) :
    (runSt S C A w).disch p = true := by
  rw [St.disch, runSt_get]
  show (lastRec p w || (pstate C p w).ok) = true
  rw [ok_pstate]
  rcases h with h | h | h
  · rw [h]; rfl
  · rw [h]; simp
  · rw [h]; simp

/-- The node-local base is the base of the run of the branch. -/
theorem baseOf_branch (bb : ℕ → Fin 4) (p : Bool) (n : ℕ) :
    baseOf p (branchNode bb n) = base p (runOfBranch bb) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show baseOf p (branchNode bb n ++ [bb n]) = _
      rw [baseOf_append]
      by_cases h : recDir p (bb n) = true
      · rw [if_pos h, base_succ_of_hears (hears_runOfBranch.mpr h), pre_runOfBranch]
      · rw [Bool.not_eq_true] at h
        rw [if_neg (by simp [h]), ih,
          base_succ_of_not_hears (fun hc => by rw [hears_runOfBranch.mp hc] at h; exact absurd h (by simp))]

theorem baseCol_branch (bb : ℕ → Fin 4) (p : Bool) (n : ℕ) :
    baseCol C p (branchNode bb n) = C p (base p (runOfBranch bb) n) := by
  rw [baseCol, baseOf_branch]

theorem isBranch_nodeHist (bb : ℕ → Fin 4) :
    IsBranch (fun n => nodeHist (branchNode bb n)) := fun n =>
  ⟨dirLetter (bb n), by show nodeHist (branchNode bb n ++ [bb n]) = _; rw [nodeHist_append]⟩

theorem branchNode_prefix (bb : ℕ → Fin 4) {m n : ℕ} (h : m ≤ n) :
    nodeHist (branchNode bb m) <+: nodeHist (branchNode bb n) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  rw [branchNode_add, nodeHist_append_all]
  exact ⟨_, rfl⟩

theorem baseOf_const_of_silent {bb : ℕ → Fin 4} {p : Bool} {K : ℕ}
    (h : ∀ n, K ≤ n → recDir p (bb n) = false) {m : ℕ} (hm : K ≤ m) :
    baseOf p (branchNode bb m) = baseOf p (branchNode bb K) := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      show baseOf p (branchNode bb m ++ [bb m]) = _
      rw [baseOf_append, if_neg (by simp [h m hm]), ih]

/-- **The obligation recurs on every branch.**  Either the process hears again, or its check is not
required, or its bad set is finite and the branch seals it. -/
theorem disch_recurs_run (bb : ℕ → Fin 4) (p : Bool) (K : ℕ) :
    ∃ n, K ≤ n ∧ (runSt S C A (branchNode bb n)).disch p = true := by
  classical
  by_cases hrec : ∃ n, K ≤ n ∧ recDir p (bb n) = true
  · obtain ⟨n, hn, hr⟩ := hrec
    refine ⟨n + 1, by omega, disch_pstate S C A _ (Or.inl ?_)⟩
    show lastRec p (branchNode bb n ++ [bb n]) = true
    rw [lastRec_append]
    exact hr
  · have hsil : ∀ n, K ≤ n → recDir p (bb n) = false := by
      intro n hn
      by_contra hc
      exact hrec ⟨n, hn, by simpa using hc⟩
    by_cases hreq : reqOf C p (branchNode bb K) = true
    · have hfin : (Bad p C (baseOf p (branchNode bb K))
          (C p (baseOf p (branchNode bb K)))).Finite := of_decide_eq_true hreq
      obtain ⟨n, hn⟩ := (finite_iff_eventually_noBelow _).mp hfin
        (fun n => nodeHist (branchNode bb n)) rfl (isBranch_nodeHist bb)
      refine ⟨max n K, le_max_right _ _, disch_pstate S C A _ (Or.inr (Or.inr ?_))⟩
      rw [sealOf, baseCol, baseOf_const_of_silent hsil (le_max_right _ _), decide_eq_true_eq]
      exact noBelow_mono hn (branchNode_prefix bb (le_max_left _ _))
    · exact ⟨K, le_rfl, disch_pstate S C A _ (Or.inr (Or.inl (by simpa using hreq)))⟩

theorem heard_mono (bb : ℕ → Fin 4) (p : Bool) {m n : ℕ} (h : m ≤ n)
    (hm : heard p (branchNode bb m) = true) : heard p (branchNode bb n) = true := by
  induction n, h using Nat.le_induction with
  | base => exact hm
  | succ n hn ih =>
      show heard p (branchNode bb n ++ [bb n]) = true
      rw [heard_append, ih]
      rfl

theorem goodDone_mono (bb : ℕ → Fin 4) (p : Bool) {m n : ℕ} (h : m ≤ n)
    (hm : goodDone C p (branchNode bb m) = true) : goodDone C p (branchNode bb n) = true := by
  induction n, h using Nat.le_induction with
  | base => exact hm
  | succ n hn ih =>
      show goodDone C p (branchNode bb n ++ [bb n]) = true
      rw [goodDone_append, ih]
      rfl

/-- A good reception sets `goodDone` for good. -/
theorem goodDone_eventually {bb : ℕ → Fin 4} {p : Bool} {i : ℕ} {c : K}
    (hh : Hears p (runOfBranch bb) i) (hg : Good p C (pre (runOfBranch bb) i) c) :
    ∀ n, i + 1 ≤ n → goodDone C p (branchNode bb n) = true := by
  rw [pre_runOfBranch] at hg
  have hrec : recDir p (bb i) = true := hears_runOfBranch.mp hh
  have hgood : goodAt C p (branchNode bb i) = true := by
    rw [goodAt, decide_eq_true_eq, hg.1]
    exact hg
  have hbase : goodDone C p (branchNode bb (i + 1)) = true := by
    show goodDone C p (branchNode bb i ++ [bb i]) = true
    rw [goodDone_append, hgood, hrec]
    simp
  exact fun n hn => goodDone_mono C bb p hn hbase

/-- After the base has settled there is at most one further reception, so the run is eventually not
in a reception step. -/
theorem lastRec_eventually_false {bb : ℕ → Fin 4} {p : Bool} {b : Base} {n₀ : ℕ}
    (hb : ∀ n, n₀ ≤ n → base p (runOfBranch bb) n = b) :
    ∃ N, ∀ n, N ≤ n → lastRec p (branchNode bb n) = false := by
  classical
  have huniq : ∀ m n, n₀ ≤ m → n₀ ≤ n → recDir p (bb m) = true → recDir p (bb n) = true → m = n := by
    intro m n hm hn hrm hrn
    have h1 : base p (runOfBranch bb) (m + 1) = some (pre (runOfBranch bb) m) :=
      base_succ_of_hears (hears_runOfBranch.mpr hrm)
    have h2 : base p (runOfBranch bb) (n + 1) = some (pre (runOfBranch bb) n) :=
      base_succ_of_hears (hears_runOfBranch.mpr hrn)
    rw [hb _ (by omega)] at h1
    rw [hb _ (by omega)] at h2
    have h3 : pre (runOfBranch bb) m = pre (runOfBranch bb) n := by
      rw [← Option.some_inj, ← h1, ← h2]
    have := congrArg List.length h3
    simpa using this
  by_cases hex : ∃ m, n₀ ≤ m ∧ recDir p (bb m) = true
  · obtain ⟨m, hm, hrm⟩ := hex
    refine ⟨m + 2, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    show lastRec p (branchNode bb k ++ [bb k]) = false
    rw [lastRec_append]
    by_contra hc
    have hct : recDir p (bb k) = true := by simpa using hc
    have := huniq m k hm (by omega) hrm hct
    omega
  · refine ⟨n₀ + 1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    show lastRec p (branchNode bb k ++ [bb k]) = false
    rw [lastRec_append]
    by_contra hc
    exact hex ⟨k, by omega, by simpa using hc⟩

/-- The second case of the labelling's termination clause makes the run's `term` hold eventually:
the check is required because the bad set is finite, and the branch seals it. -/
theorem term_eventually_of_end {bb : ℕ → Fin 4} {p : Bool} {b : Base} {c : K} {n₀ : ℕ}
    (hb : ∀ n, n₀ ≤ n → base p (runOfBranch bb) n = b) (hend : End p C b c) :
    ∃ N, ∀ n, N ≤ n → (pstate C p (branchNode bb n)).term = true := by
  classical
  obtain ⟨N₁, hN₁⟩ := lastRec_eventually_false hb
  have hbase : ∀ n, n₀ ≤ n → baseOf p (branchNode bb n) = b := fun n hn => by
    rw [baseOf_branch]; exact hb n hn
  have hcol : ∀ n, n₀ ≤ n → baseCol C p (branchNode bb n) = c := fun n hn => by
    rw [baseCol, hbase n hn]; exact hend.1
  obtain ⟨n₂, hn₂⟩ := (finite_iff_eventually_noBelow _).mp hend.2
    (fun n => nodeHist (branchNode bb n)) rfl (isBranch_nodeHist bb)
  refine ⟨max (max n₀ N₁) n₂, fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : n₂ ≤ n := le_trans (le_max_right _ _) hn
  have hseal : sealOf C p (branchNode bb n) = true := by
    rw [sealOf, hbase n hn0, hcol n hn0, decide_eq_true_eq]
    exact noBelow_mono hn₂ (branchNode_prefix bb hn2)
  have hreq : reqOf C p (branchNode bb n) = true := by
    rw [reqOf, hbase n hn0, hcol n hn0, decide_eq_true_eq]
    exact hend.2
  show (goodDone C p (branchNode bb n) || (!lastRec p (branchNode bb n) &&
    (pstate C p (branchNode bb n)).sealedHere)) = true
  rw [hN₁ n hn1]
  show (goodDone C p (branchNode bb n) || (true &&
    (reqOf C p (branchNode bb n) && true && sealOf C p (branchNode bb n)))) = true
  rw [hreq, hseal]
  simp

/-- The base cannot change once the process has stopped hearing. -/
theorem base_const_of_silent {σ : ℕ → Event Bool} {p : Bool} {N : ℕ}
    (h : ∀ i, N ≤ i → ¬ Hears p σ i) {n : ℕ} (hn : N ≤ n) :
    base p σ n = base p σ N := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [base_succ_of_not_hears (h n hn), ih]

/-- A process whose root colour the spec rejects for a muted process must hear. -/
theorem heard_eventually {r : Bool → K} (hC : GenColouring S (advOf A) r C) {bb : ℕ → Fin 4}
    (hσ : runOfBranch bb ∈ advOf A) (p : Bool) (hne : S.deafOk p (r p) = false) :
    ∃ N, ∀ n, N ≤ n → heard p (branchNode bb n) = true := by
  classical
  have hnm : ¬ Muted p (runOfBranch bb) := by
    intro hm
    rw [hC.deaf _ hσ p hm] at hne
    exact Bool.noConfusion hne
  have hex : ∃ i, Hears p (runOfBranch bb) i := by
    by_contra hc
    exact hnm fun q hq => hc ⟨q, hq⟩
  obtain ⟨i, hi⟩ := hex
  have hbase : heard p (branchNode bb (i + 1)) = true := by
    show heard p (branchNode bb i ++ [bb i]) = true
    rw [heard_append, hears_runOfBranch.mp hi]
    simp
  exact ⟨i + 1, fun n hn => heard_mono bb p hn hbase⟩

/-- The termination clause of the labelling makes the run's `term` hold eventually. -/
theorem term_eventually {r : Bool → K} (hC : GenColouring S (advOf A) r C) {bb : ℕ → Fin 4}
    (hσ : runOfBranch bb ∈ advOf A) (p : Bool) :
    ∃ N, ∀ n, N ≤ n → (pstate C p (branchNode bb n)).term = true := by
  classical
  rcases hC.term _ hσ p with ⟨i, hh, hall⟩ | ⟨N, hsil, hfin⟩
  · have hg : Good p C (pre (runOfBranch bb) i) (C p (some (pre (runOfBranch bb) i))) :=
      good_iff_allCol.mpr ⟨rfl, hall⟩
    refine ⟨i + 1, fun n hn => ?_⟩
    show (goodDone C p (branchNode bb n) || _) = true
    rw [goodDone_eventually C hh hg n hn]
    rfl
  · have hb : ∀ n, N ≤ n → base p (runOfBranch bb) n = base p (runOfBranch bb) N :=
      fun n hn => base_const_of_silent hsil hn
    have hend : End p C (base p (runOfBranch bb) N)
        (C p (base p (runOfBranch bb) N)) :=
      ⟨rfl, (finite_iff_eventually_noBelow _).mpr hfin⟩
    exact term_eventually_of_end C hb hend

/-- The relation clause of the labelling holds of the two tracked base colours. -/
theorem rel_eventually {r : Bool → K} (hC : GenColouring S (advOf A) r C) {bb : ℕ → Fin 4}
    (hσ : runOfBranch bb ∈ advOf A) :
    ∃ N, ∀ n, N ≤ n →
      S.rel (baseCol C false (branchNode bb n)) (baseCol C true (branchNode bb n)) = true := by
  obtain ⟨n₀, hn₀⟩ := hC.rel _ hσ
  exact ⟨n₀, fun n hn => by rw [baseCol_branch, baseCol_branch]; exact hn₀ n hn⟩

/-- **The clauses hold eventually on every admissible branch.** -/
theorem phi_eventually (hC : GenColouring S (advOf A) (fun p => C p none) C) {bb : ℕ → Fin 4}
    (hσ : runOfBranch bb ∈ advOf A) :
    ∃ N, ∀ n, N ≤ n →
      (runSt S C A (branchNode bb n)).phi S (params C).r = true := by
  classical
  have hdeaf : ∀ p : Bool, ∃ N, ∀ n, N ≤ n →
      (S.deafOk p (C p none) || heard p (branchNode bb n)) = true := by
    intro p
    by_cases h : S.deafOk p (C p none) = true
    · exact ⟨0, fun n _ => by rw [h]; rfl⟩
    · obtain ⟨N, hN⟩ := heard_eventually S C A hC hσ p (by simpa using h)
      exact ⟨N, fun n hn => by rw [hN n hn]; simp⟩
  obtain ⟨N1, hN1⟩ := hdeaf false
  obtain ⟨N2, hN2⟩ := hdeaf true
  obtain ⟨N3, hN3⟩ := term_eventually S C A hC hσ false
  obtain ⟨N4, hN4⟩ := term_eventually S C A hC hσ true
  obtain ⟨N5, hN5⟩ := rel_eventually S C A hC hσ
  refine ⟨max (max N1 N2) (max (max N3 N4) N5), fun n hn => ?_⟩
  have h1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have h2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h3 : N3 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hn)
  have h4 : N4 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hn)
  have h5 : N5 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  rw [St.phi, runSt_pu, runSt_pv]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨hN1 n h1, hN2 n h2⟩, hN3 n h3⟩, hN4 n h4⟩, hN5 n h5⟩

/-- Every branch of the constructed run is winning. -/
theorem win_run (hC : GenColouring S (advOf A) (fun p => C p none) C) (bb : ℕ → Fin 4) :
    DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins
      (fun n => (automaton S A (params C)).priority (runSt S C A (branchNode bb n))) false := by
  refine win_of_branch (t := labTree C) (runSt_nil S C A) (run_mem_trans S C A) bb ?_ ?_
  · intro hadm
    refine phi_eventually S C A hC ?_
    show DistributedSynthesis.DecisionTasks.Source.FiniteParity.ColourWins
      (fun n => A.prio (advRun A (letter (runOfBranch bb)) n)) false
    have hq : (fun n => A.prio (runSt S C A (branchNode bb n)).q)
        = fun n => A.prio (advRun A (fun i => dirLetter (bb i)) n) :=
      funext fun n => by rw [run_q_eq (runSt_nil S C A) (run_mem_trans S C A) bb n]
    have hlet : (fun i => dirLetter (bb i)) = letter (runOfBranch bb) :=
      funext fun i => (letter_runOfBranch bb i).symm
    rw [hq, hlet] at hadm
    exact hadm
  · exact firedK_of_disch (run_mem_trans S C A) bb fun p K => disch_recurs_run S C A bb p K

/-- **A labelling yields an accepting run.**  This is the converse of `genColouring_of_accepts`. -/
theorem accepts_of_colouring (hC : GenColouring S (advOf A) (fun p => C p none) C) :
    (automaton S A (params C)).acceptsTree (labTree C) :=
  ⟨runSt S C A, ⟨runSt_nil S C A, run_mem_trans S C A⟩,
    fun b => (DistributedSynthesis.DecisionTasks.Source.FiniteParity.colourWins_false_iff _).mp
      (win_run S C A hC b)⟩

end Back

variable {K : Type} [Fintype K] [DecidableEq K]
variable {AdvQ : Type} [Fintype AdvQ] [DecidableEq AdvQ]

/-- **A labelling makes the automaton's language non-empty.** -/
theorem autSolvableAt_of_genColouring (S : Spec K) (A : Adv AdvQ) {r : Bool → K}
    {C : Bool → Base → K} (hC : GenColouring S (advOf A) r C) : AutSolvableAt S A r := by
  have hr : (fun p => C p none) = r := funext hC.root
  subst hr
  exact ⟨Back.params C, rfl, Back.labTree C, Back.accepts_of_colouring S C A hC⟩

/-- **The automaton decides the labelling problem**, at prescribed root colours. -/
theorem autSolvableAt_iff (S : Spec K) (A : Adv AdvQ) (r : Bool → K) :
    AutSolvableAt S A r ↔ ∃ C, GenColouring S (advOf A) r C :=
  ⟨genColouring_of_autSolvableAt A r, fun ⟨_, hC⟩ => autSolvableAt_of_genColouring S A hC⟩

end ColAut

end DistributedSynthesis.DecisionTasks.Source
