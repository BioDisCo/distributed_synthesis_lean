/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusConnected
import DistributedSynthesis.Formalizations.ComponentTrees.CanonicalAlphabet
import DistributedSynthesis.Formalizations.ComponentTrees.ConsensusBroadcaster
import DistributedSynthesis.Results.ComponentTrees

namespace Characterisation.ComponentTrees.Tests
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.HistoryGame

-- Acceptance is required only on live branches. Here every full branch
-- rejects, but the live history tree is empty, so its segment relation is
-- well founded. An accidental all-branches premise would break this test.
example : WellFounded (EdgeSegment (fun _ : List Bool => False) (fun _ => 1) 1) := by
  apply edgeSegment_wellFounded _ _ (fun _ _ _ h => h)
    (fun _ h => False.elim (h 0)) 1
  rintro ⟨k, eq⟩
  omega

-- Incoming-edge convention: priority 1 at the endpoint is counted;
-- priority 0 at the source is excluded from this one-edge segment.
example : EdgeSegment (fun _ : List Unit => True) List.length 1 [()] [] := by
  refine ⟨trivial, ⟨[()], rfl⟩, by decide, ?_, ⟨1, by decide, by decide, rfl⟩⟩
  intro n lo hi
  have eq : n = 1 := by simp only [List.length_nil, List.length_cons] at lo hi; omega
  subst n
  decide

-- Singleton application inputs are supported. Nontrivial fresh proposals
-- are supplied by Bool, independently of these input alphabets.
example {O₁ O₂ Q B G : Type} {D : Nat}
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (m : Move Unit Unit O₁ O₂ Q D) (K : Finset m.source.End)
    (label : m.source.End → B)
    (rep : participatingRoots m K → participatingRoots m K)
    (preserves : ∀ h, endpointTable m K label (rep h) = endpointTable m K label h)
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool),
      ComponentGames.Consensus.SolvesBy σ (Residual A u) D)
    (component : IsComponent M m K) (p : Proc) (e f : K)
    (same : currentView p (m.source.history e.val) = currentView p (m.source.history f.val)) :
    currentView p (m.source.history (endpointFold m K label rep preserves e).val) =
      currentView p (m.source.history (endpointFold m K label rep preserves f).val) :=
  endpointFold_views_of_consensus m K label rep preserves M A recognizes positive consensus component p e f same


-- A map between rounds 0 and 3: extension must not require equal depths.
private def emptyFamily : Unit → EnvHistory Unit Unit := fun _ => []
private def laterFamily : Unit → EnvHistory Unit Unit :=
  fun _ => List.replicate 3 ⟨(), (), .both, (), ()⟩
private noncomputable def differentRounds : ViewComplexMap emptyFamily laterFamily :=
  ViewComplexMap.ofEdge (fun _ => ()) (fun _ _ _ _ => rfl)

example (D : Nat) (w : BlockWord (RoundRecord Unit Unit Graph Unit Unit) D) :
    closingLayerHistory laterFamily D ((differentRounds.extend D).edge (wordScenario () w)) =
      List.replicate 3 ⟨(), (), .both, (), ()⟩ ++ w.val := by
  rw [differentRounds.extend_history, wordScenario_root, scenarioWord_wordScenario]
  rfl

-- A two-edge star may collapse to one edge. Neither view reflection nor
-- injectivity belongs in the reduction conditions.
private def starHistory (b : Bool) : EnvHistory Unit Bool := [⟨(), b, .right, (), ()⟩]
private noncomputable def collapseStar : Reduction starHistory (fun _ => ()) where
  map := ViewComplexMap.ofEdge (fun _ => false) (fun _ _ _ _ => rfl)
  idempotent _ := rfl
  states _ := rfl

example : (Finset.univ.image collapseStar.map.edge).card = 1 := by
  change (Finset.univ.image (fun _ : Bool => false)).card = 1
  simp

example : starHistory false ≠ starHistory true := by
  simp [starHistory]

-- The new broadcaster proof must keep fresh proposals independent of
-- application inputs, even for an arbitrary connected subgraph.
example (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (consensus : ∀ g, LivePrefix A g → ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool),
      ComponentGames.Consensus.SolvesBy σ (Residual A g) D)
    (r : Nat) (deep : D ≤ r) (C : Set (EnvHistory Unit Unit)) (nonempty : C.Nonempty)
    (lengths : ∀ h ∈ C, List.length h = r)
    (alive : ∀ h ∈ C, LivePrefix A (History.graphSequence h))
    (connected : ∀ e f : C, Relation.ReflTransGen
      (fun x y : C => ∃ p, currentView p x.val = currentView p y.val) e f) :
    ∃ p, ∀ h ∈ C, ∀ k ∈ C,
      currentView p (h.take (r-D)) = currentView p (k.take (r-D)) :=
  bounded_common_view A D positive consensus r deep C nonempty lengths alive connected

-- This endpoint needs no additional liveness or simulation hypothesis:
-- the paper's product automaton discharges it. Singleton inputs are allowed.
example {O₁ O₂ G : Type} [Fintype G] {D bound : Nat}
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (A : DetParityAutomaton (ContinuationLetter Unit Unit O₁ O₂))
    (hat : CompressedTree (blockAutomaton (jointRecognizer M) A D) M bound)
    (accepting : hat.Accepting) :
    ∃ tree : UncompressedTree (blockAutomaton (jointRecognizer M) A D) M,
      tree.Accepting :=
  block_compressed_to_uncompressed M A hat accepting

-- The implementation of vertex transport computes, even for a map that
-- collapses distinct edges. `decide` checks the finite search itself.
private def executableCollapse : ViewComplexMap starHistory starHistory :=
  ExecutableReverse.finiteViewMap starHistory starHistory (fun _ => false)
    (fun _ _ _ _ => rfl)

example : (executableCollapse.vertex Proc.one (viewEndpoint starHistory Proc.one true)).val =
    currentView Proc.one (starHistory false) := by decide

example : (executableCollapse.vertex Proc.two (viewEndpoint starHistory Proc.two true)).val =
    currentView Proc.two (starHistory false) := by decide

-- Exact manuscript-strength endpoint, including inputless applications.
-- Fresh Bool proposals are independent of singleton application inputs.
-- No coverage, rank, simulation, or extra automaton-liveness premise occurs.
example {O₁ O₂ G : Type} [Fintype G] {D : Nat}
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ h, LivePrefix A h → ∃ σ : StrategyPair Bool Bool (Option Bool) (Option Bool),
      ComponentGames.Consensus.SolvesBy σ (Residual A h) D)
    (specification : DetParityAutomaton (ContinuationLetter Unit Unit O₁ O₂)) :
    (∃ original : UncompressedTree (blockAutomaton (jointRecognizer M) specification D) M,
      original.Accepting) ↔
    ∃ compressed : CompressedTree (blockAutomaton (jointRecognizer M) specification D) M
      (reductionBound (blockAutomaton (jointRecognizer M) specification D)), compressed.Accepting :=
  block_bounded_representation M A recognizes positive consensus specification

-- All infinite words with live prefixes must be covered, including words
-- outside A. There is deliberately no membership-in-A premise here.
example {O₁ O₂ G : Type} {D : Nat}
    (B : DetParityAutomaton (BlockWord (ContinuationLetter Unit Unit O₁ O₂) D))
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (tree : UncompressedTree B M) (accepting : tree.Accepting)
    (word : Nat → BlockInput Unit Unit D)
    (live : ∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => B.priority (tree.stateOf (branchNode word n))) :=
  tree.stateOf_accepts accepting.1 accepting A recognizes word live

-- The equivalence still quantifies over every live block stream with
-- singleton inputs. No state-liveness certificate is supplied to this lemma.
example {O₁ O₂ G : Type} [Nonempty O₁] [Nonempty O₂] {D : Nat}
    (B : DetParityAutomaton (BlockWord (ContinuationLetter Unit Unit O₁ O₂) D))
    (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (initialLive : M.eval [] ∈ M.accept) (positive : 0 < D) :
    (∃ tree : UncompressedTree B M, tree.Accepting) ↔
      ∃ σ : StrategyPair Unit Unit O₁ O₂, ∀ word : Nat → BlockInput Unit Unit D,
        (∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) →
        NatSeqMinEvenParity (fun n => B.priority (strategyState σ B (branchNode word n))) :=
  uncompressed_strategy_iff B M A recognizes initialLive positive

-- No effectively given model or local parity certificate is a premise of
-- the finite-table MSO satisfiability theorem. The table numbering is data.
example (T : FiniteRunMSO.Tables (Fin 2) (Fin 3) (Fin 4)) :
    FiniteRunMSO.satisfiable T (Equiv.refl _) = true ↔
      ∃ tree, FiniteRunMSO.Accepting T tree :=
  FiniteRunMSO.satisfiable_correct T (Equiv.refl _)

-- An edge set cannot put an extra edge outside the selected branch.
example {m : Nat} (P : Fin m) (H : Fin 4 → Fin m)
    (tree : LabeledTree (Fin 2) (Fin 3))
    (sets : Fin m → Set (TreeNode (Fin 2)))
    (partition : MSO.Tree.Realize tree (FiniteRunMSO.partitionFormula P H) Fin.elim0 sets)
    (node : TreeNode (Fin 2)) (outside : node ∉ sets P) :
    ∀ e, node ∉ sets (H e) := by
  intro e member
  exact outside ((FiniteRunMSO.partitionFormula_correct P H tree sets).mp partition |>.2 node e member)

-- Numeric model labels are decoded by executable arithmetic, including
-- the singleton alphabet used by inputless specializations.
example : MSO.Tree.NumericModel.decodeLetter (a:=0) ⟨0,by decide⟩ = 0 := by decide
example : MSO.Tree.NumericModel.decodeLetter (a:=2) ⟨2,by decide⟩ = 2 := by decide

-- These endpoints must accept the original encoded problem alone, without
-- supplying a consensus bound, finite model, run certificate, or strategy.
example (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (ComponentGames.graphInput d.1).Accepts word})) :
    Effective.solve d promise = true ↔
      WithInputs.Realizable {word | (ComponentGames.graphInput d.1).Accepts word} d.2 :=
  Effective.solve_correct d alphabet promise

example (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (ComponentGames.graphInput d.1).Accepts word}))
    (σ : WithInputs.Strategies d.2) (found : Effective.synthesize d promise = some σ) :
    ∀ env, (ComponentGames.graphInput d.1).Accepts (fun n => (env n).graph) →
      LTL.Satisfies (EncodedNoDirect.interp d.2) (execution σ env) (EncodedFiniteLTL.decode d.2.formula) :=
  Effective.synthesize_sound d alphabet promise σ found

end Characterisation.ComponentTrees.Tests
