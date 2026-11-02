/- Decision-task excerpts from consensusLTL.
Source declarations and hashes are recorded in ../source-manifest.json. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Konig
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Parity

set_option linter.unusedSectionVars false

/- From Mso.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

/-- The history of the first `n` letters of a letter word. -/
def preW (w : ℕ → Letter) (n : ℕ) : List Letter := (List.range n).map w

theorem preW_succ (w : ℕ → Letter) (n : ℕ) : preW w (n + 1) = preW w n ++ [w n] := by
  simp [preW, List.range_succ]

theorem pre_eq_preW (σ : ℕ → Event Bool) (n : ℕ) : pre σ n = preW (letter σ) n := rfl

end DistributedSynthesis.DecisionTasks.Source

/- From NodeTransport.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

open DistributedSynthesis.DecisionTasks.Source.FiniteParity.TreeAutomaton

/-- The four letters, indexed. -/
def dirLetter : Fin 4 → Letter
  | 0 => (false, false)
  | 1 => (false, true)
  | 2 => (true, false)
  | 3 => (true, true)

/-- The inverse indexing. -/
def letterDir (a : Letter) : Fin 4 :=
  if a.1 then (if a.2 then 3 else 2) else (if a.2 then 1 else 0)

@[simp] theorem letterDir_dirLetter (i : Fin 4) : letterDir (dirLetter i) = i := by
  fin_cases i <;> rfl

@[simp] theorem dirLetter_letterDir (a : Letter) : dirLetter (letterDir a) = a := by
  obtain ⟨x, y⟩ := a
  cases x <;> cases y <;> rfl

/-- A node of the automaton's tree, read as a history. -/
def nodeHist (w : Node 4) : List Letter := w.map dirLetter

/-- A history, read as a node. -/
def histNode (h : List Letter) : Node 4 := h.map letterDir

@[simp] theorem nodeHist_histNode (h : List Letter) : nodeHist (histNode h) = h := by
  simp [nodeHist, histNode, List.map_map, Function.comp_def]

@[simp] theorem histNode_nodeHist (w : Node 4) : histNode (nodeHist w) = w := by
  simp [nodeHist, histNode, List.map_map, Function.comp_def]

@[simp] theorem nodeHist_nil : nodeHist [] = [] := rfl

@[simp] theorem nodeHist_append (w : Node 4) (i : Fin 4) :
    nodeHist (w ++ [i]) = nodeHist w ++ [dirLetter i] := by simp [nodeHist]

@[simp] theorem nodeHist_length (w : Node 4) : (nodeHist w).length = w.length := by
  simp [nodeHist]

theorem nodeHist_injective : Function.Injective nodeHist := by
  intro w w' h
  rw [← histNode_nodeHist w, ← histNode_nodeHist w', h]

@[simp] theorem nodeHist_append_all (w v : Node 4) :
    nodeHist (w ++ v) = nodeHist w ++ nodeHist v := by simp [nodeHist]

theorem nodeHist_prefix {w : Node 4} {j : List Letter} (h : nodeHist w <+: j) :
    ∃ v : Node 4, j = nodeHist (w ++ v) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨histNode s, ?_⟩
  rw [nodeHist_append_all, nodeHist_histNode, hs]

/-- The automaton's branch nodes are the histories of the corresponding letter word. -/
theorem branchNode_eq_preW (b : ℕ → Fin 4) (n : ℕ) :
    nodeHist (branchNode b n) = preW (fun i => dirLetter (b i)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [branchNode, nodeHist_append, ih, preW_succ]

/-- Every branch of histories comes from a branch of directions. -/
theorem exists_dirBranch {β : ℕ → List Letter} (h0 : β 0 = []) (hb : IsBranch β) :
    ∃ bb : ℕ → Fin 4, ∀ n, β n = nodeHist (branchNode bb n) := by
  classical
  choose a ha using hb
  refine ⟨fun n => letterDir (a n), fun n => ?_⟩
  induction n with
  | zero => rw [h0]; rfl
  | succ n ih =>
      rw [ha n, ih, branchNode, nodeHist_append, dirLetter_letterDir]

@[simp] theorem branchNode_length (bb : ℕ → Fin 4) (n : ℕ) : (branchNode bb n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [branchNode, List.length_append, ih]; rfl

/-- The letters a branch reads between two depths. -/
def segLetters (bb : ℕ → Fin 4) (L k : ℕ) : List Letter :=
  (List.range k).map fun i => dirLetter (bb (L + i))

theorem segLetters_succ (bb : ℕ → Fin 4) (L k : ℕ) :
    segLetters bb L (k + 1) = segLetters bb L k ++ [dirLetter (bb (L + k))] := by
  simp [segLetters, List.range_succ]

/-- A branch's history at a later depth is its history now followed by the letters it reads. -/
theorem nodeHist_branchNode_add (bb : ℕ → Fin 4) (L k : ℕ) :
    nodeHist (branchNode bb (L + k)) = nodeHist (branchNode bb L) ++ segLetters bb L k := by
  induction k with
  | zero => simp [segLetters]
  | succ k ih =>
      show nodeHist (branchNode bb (L + k) ++ [bb (L + k)]) = _
      rw [nodeHist_append, ih, segLetters_succ, List.append_assoc]

/-- The directions a branch takes between two depths. -/
def segDirs (bb : ℕ → Fin 4) (L k : ℕ) : Node 4 := (List.range k).map fun i => bb (L + i)

theorem branchNode_add (bb : ℕ → Fin 4) (L k : ℕ) :
    branchNode bb (L + k) = branchNode bb L ++ segDirs bb L k := by
  induction k with
  | zero => simp [segDirs]
  | succ k ih =>
      show branchNode bb (L + k) ++ [bb (L + k)] = _
      rw [ih, segDirs, segDirs, List.range_succ, List.map_append, List.append_assoc]
      rfl

theorem mem_segDirs {bb : ℕ → Fin 4} {L k : ℕ} {i : Fin 4} :
    i ∈ segDirs bb L k ↔ ∃ j, j < k ∧ bb (L + j) = i := by
  simp [segDirs]

theorem segLetters_cons (bb : ℕ → Fin 4) (L k : ℕ) :
    segLetters bb L (k + 1) = dirLetter (bb L) :: segLetters bb (L + 1) k := by
  simp only [segLetters, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ List.cons rfl ?_
  refine List.map_congr_left fun i _ => ?_
  show dirLetter (bb (L + (i + 1))) = dirLetter (bb (L + 1 + i))
  congr 2
  omega

theorem mem_segLetters {bb : ℕ → Fin 4} {L k : ℕ} {a : Letter} :
    a ∈ segLetters bb L k ↔ ∃ i, i < k ∧ dirLetter (bb (L + i)) = a := by
  simp [segLetters]

/-- Reading a run off a branch of directions. -/
def runOfBranch (b : ℕ → Fin 4) : ℕ → Event Bool := runOfWord fun i => dirLetter (b i)

theorem letter_runOfBranch (b : ℕ → Fin 4) (i : ℕ) :
    letter (runOfBranch b) i = dirLetter (b i) := letter_runOfWord _ i

theorem pre_runOfBranch (b : ℕ → Fin 4) (n : ℕ) :
    pre (runOfBranch b) n = nodeHist (branchNode b n) := by
  rw [branchNode_eq_preW, pre_eq_preW]
  exact congrArg (fun f => preW f n) (funext (letter_runOfBranch b))

end DistributedSynthesis.DecisionTasks.Source
