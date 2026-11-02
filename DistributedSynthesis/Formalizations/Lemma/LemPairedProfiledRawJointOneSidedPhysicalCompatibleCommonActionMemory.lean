/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleCommonAction
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy

/-!
# Finite common-action memory for the one-sided kernel

This file packages the exact positive object left by the common-action audit.
A memory cell represents a nonempty belief of compatible semantic sources at
one public linked code.  It chooses one complete linked move common to all of
them.  When a finite child-code tag is read, every represented source follows
the same chosen raw representative and belongs to the next belief.

Successor inclusion, rather than equality with one predecessor image, is the
correct closure law: a finite quotient may safely merge several successor
beliefs.  Public-code equality and common-move validity at the merged cell
still prevent semantic mosaics.

The construction has two conclusions.

* Any finite common-action certificate yields the existing augmented
  physical-compatible policy while retaining its memory literally.
* A winning strategy always yields the same certificate with exact semantic
  memory.  That memory contains the full source and need not be finite.

Thus the remaining theorem is now sharply isolated: find a finite,
locally reconstructible quotient of the exact certificate.  Legality,
successor closure, and forward parity do not remain additional assumptions.
-/

namespace DistributedSynthesis

universe u v x y s m

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
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev OneSidedState :=
  ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

/-! ## Observable finite-tag transition -/

/-- Raw direction chosen for a finite requested child-code tag.  The function
is proof-side and is exactly the representative used by
`sourceFreeBeliefFiniteCodeNext`. -/
noncomputable def profiledRawJointOneSidedPhysicalActualOfChildCode
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂))
    (childCode : LinkedCode A) :
    ActualDirection (In₁ := In₁) (In₂ := In₂) :=
  sourceFreeBeliefRawDirectionOfChildCode
    (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))
    publicCode move childCode

/-! ## The common-action memory certificate -/

/-- A closed observation refinement.  `Memory` is not assumed finite in the
definition, so the exact semantic construction below inhabits the same
interface as a prospective finite quotient. -/
structure ProfiledRawJointOneSidedPhysicalCommonActionMemoryCertificate
    (Memory : Type m)
    (initial : OneSidedState A strategy)
    (initialAnnotation : PhysicalAnnotation A) where
  initialMemory : Memory
  belief : Memory → OneSidedState A strategy → Prop
  publicCode : Memory → LinkedCode A
  move : Memory → LinkedMove A (In₁ := In₁) (In₂ := In₂)
  next : Memory → LinkedCode A → Memory
  initial_public :
    publicCode initialMemory = (initial.code A, initialAnnotation)
  initial_mem : belief initialMemory initial
  belief_at : ∀ memory,
    ProfiledRawJointOneSidedPhysicalBeliefAt A strategy (belief memory)
      (publicCode memory)
  common_move : ∀ memory,
    ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy hwin
      (belief memory) (publicCode memory).2 (move memory)
  next_public : ∀ memory childCode,
    publicCode (next memory childCode) =
      sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))
        (publicCode memory) (move memory) childCode
  successor_mem : ∀ memory childCode source,
    belief memory source →
      belief (next memory childCode)
        (source.step A
          (profiledRawJointOneSidedPhysicalActualOfChildCode A
            (publicCode memory) (move memory) childCode))

namespace ProfiledRawJointOneSidedPhysicalCommonActionMemoryCertificate

variable {Memory : Type m}
variable
  (initial : OneSidedState A strategy)
  (initialAnnotation : PhysicalAnnotation A)
variable
  (certificate :
    ProfiledRawJointOneSidedPhysicalCommonActionMemoryCertificate
      (Memory := Memory) A strategy hwin initial initialAnnotation)

/-! ## Finite semantic tree carried by the certificate -/

/-- The public semantic tree whose exact state is the proposed memory cell.
The source belief remains proof-only. -/
def semanticTree :
    SourceFreeBeliefSemanticTree
      (LinkedCode A)
      (LinkedMove A (In₁ := In₁) (In₂ := In₂))
      (LinkedCode A) where
  Semantic := Memory
  initial := certificate.initialMemory
  step := certificate.next
  code := certificate.publicCode
  move := certificate.move

/-- Simultaneously follow the finite memory and one honest semantic source.
Only the first projection is controller memory. -/
noncomputable def sourceStateAt (node : TreeNode (LinkedCode A)) :
    Memory × OneSidedState A strategy :=
  node.foldl
    (fun current childCode ↦
      let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
        (certificate.publicCode current.1) (certificate.move current.1)
          childCode
      (certificate.next current.1 childCode,
        current.2.step A actual))
    (certificate.initialMemory, initial)

@[simp] theorem sourceStateAt_nil :
    certificate.sourceStateAt A strategy hwin initial initialAnnotation [] =
      (certificate.initialMemory, initial) :=
  rfl

theorem sourceStateAt_append
    (node : TreeNode (LinkedCode A)) (childCode : LinkedCode A) :
    certificate.sourceStateAt A strategy hwin initial initialAnnotation
        (node ++ [childCode]) =
      let current := certificate.sourceStateAt A strategy hwin initial
        initialAnnotation node
      let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
        (certificate.publicCode current.1) (certificate.move current.1)
          childCode
      (certificate.next current.1 childCode,
        current.2.step A actual) := by
  simp [sourceStateAt, List.foldl_append]

/-- The first projection of the honest-source fold is exactly the finite
memory-tree state. -/
theorem sourceStateAt_fst (node : TreeNode (LinkedCode A)) :
    (certificate.sourceStateAt A strategy hwin initial initialAnnotation
      node).1 =
      certificate.semanticTree.stateAt node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node childCode ih =>
      rw [certificate.sourceStateAt_append A strategy hwin initial
          initialAnnotation node childCode,
        certificate.semanticTree.stateAt_append]
      change certificate.next
          (certificate.sourceStateAt A strategy hwin initial
            initialAnnotation node).1 childCode =
        certificate.next (certificate.semanticTree.stateAt node) childCode
      exact congrArg (fun memory ↦ certificate.next memory childCode) ih

/-- The followed honest source remains in the belief represented by the
finite memory cell at every prefix. -/
theorem sourceStateAt_mem (node : TreeNode (LinkedCode A)) :
    certificate.belief
        (certificate.sourceStateAt A strategy hwin initial initialAnnotation
          node).1
      (certificate.sourceStateAt A strategy hwin initial initialAnnotation
        node).2 := by
  induction node using List.reverseRecOn with
  | nil => exact certificate.initial_mem
  | append_singleton node childCode ih =>
      rw [certificate.sourceStateAt_append A strategy hwin initial
        initialAnnotation node childCode]
      exact certificate.successor_mem _ childCode _ ih

/-- Every carried source has the public incidence code of its memory cell. -/
theorem sourceStateAt_code (node : TreeNode (LinkedCode A)) :
    (certificate.sourceStateAt A strategy hwin initial initialAnnotation
      node).2.code A =
      (certificate.publicCode
        (certificate.sourceStateAt A strategy hwin initial initialAnnotation
          node).1).1 :=
  (certificate.belief_at _).2 _
    (certificate.sourceStateAt_mem A strategy hwin initial initialAnnotation
      node) |>.1

/-- Every carried source induces the complete linked move selected by its
memory cell. -/
theorem sourceStateAt_move (node : TreeNode (LinkedCode A)) :
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
        (certificate.sourceStateAt A strategy hwin initial initialAnnotation
          node).2
        (certificate.publicCode
          (certificate.sourceStateAt A strategy hwin initial initialAnnotation
            node).1).2 =
      certificate.move
        (certificate.sourceStateAt A strategy hwin initial initialAnnotation
          node).1 :=
  certificate.common_move _ _
    (certificate.sourceStateAt_mem A strategy hwin initial initialAnnotation
      node)

/-! ## Node-local legality -/

/-- Every memory cell supplies the full provenance and parent-link legality
required by the augmented policy. -/
theorem validAt (memory : Memory) :
    sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin)
      (certificate.publicCode memory) (certificate.move memory) := by
  have hbelief := certificate.belief_at memory
  rcases hbelief.1 with ⟨source, hsource⟩
  have hinduced := certificate.common_move memory source hsource
  have hrawMove : source.move A = (certificate.move memory).1 :=
    congrArg Prod.fst hinduced
  have hsourceData := hbelief.2 source hsource
  constructor
  · constructor
    · rw [← hsourceData.1, ← hrawMove]
      exact source.move_valid_of_winning A hwin
    · exact ⟨source, hsourceData.1, hrawMove⟩
  · exact
      profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_of_commonBelief
        A strategy hwin (certificate.belief memory)
          (certificate.publicCode memory) (certificate.move memory) hbelief
            (certificate.common_move memory)

/-! ## Parity transport -/

/-- Actual raw direction followed by the honest source along a finite-code
branch. -/
noncomputable def actualBranch
    (branch : Nat → LinkedCode A) :
    Nat → ActualDirection (In₁ := In₁) (In₂ := In₂) :=
  fun n ↦
    let memory := certificate.semanticTree.stateAt (branchNode branch n)
    profiledRawJointOneSidedPhysicalActualOfChildCode A
      (certificate.publicCode memory) (certificate.move memory) (branch n)

/-- The source projection of the paired fold is the literal one-sided
semantic execution driven by `actualBranch`. -/
theorem sourceStateAt_snd_branchNode
    (branch : Nat → LinkedCode A) : ∀ n,
    (certificate.sourceStateAt A strategy hwin initial initialAnnotation
      (branchNode branch n)).2 =
      (profiledRawJointOneSidedSemanticTree A initial).stateAt
        (branchNode (certificate.actualBranch A strategy hwin initial
          initialAnnotation branch) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        show branchNode (certificate.actualBranch A strategy hwin initial
            initialAnnotation branch) (n + 1) =
          branchNode (certificate.actualBranch A strategy hwin initial
            initialAnnotation branch) n ++
            [certificate.actualBranch A strategy hwin initial
              initialAnnotation branch n] from rfl,
        certificate.sourceStateAt_append A strategy hwin initial
          initialAnnotation,
        (profiledRawJointOneSidedSemanticTree A initial).stateAt_append]
      simp only [actualBranch]
      rw [certificate.sourceStateAt_fst A strategy hwin initial
        initialAnnotation, ih]
      rfl

/-- Erasing the installed annotations from the certificate's child-code word
gives the literal incidence-code word of the followed honest source. -/
theorem childCodeWord_fst_eq
    (branch : Nat → LinkedCode A) :
    OmegaWord.map Prod.fst (certificate.semanticTree.childCodeWord branch) =
      (profiledRawJointOneSidedSemanticTree A initial).childCodeWord
        (certificate.actualBranch A strategy hwin initial initialAnnotation
          branch) := by
  funext n
  change
    (certificate.publicCode
      (certificate.semanticTree.stateAt (branchNode branch (n + 1)))).1 =
      (profiledRawJointOneSidedSemanticTree A initial).code
        ((profiledRawJointOneSidedSemanticTree A initial).stateAt
          (branchNode (certificate.actualBranch A strategy hwin initial
            initialAnnotation branch) (n + 1)))
  rw [← certificate.sourceStateAt_fst A strategy hwin initial
    initialAnnotation]
  rw [← certificate.sourceStateAt_snd_branchNode A strategy hwin initial
    initialAnnotation branch (n + 1)]
  exact (certificate.sourceStateAt_code A strategy hwin initial
    initialAnnotation
    (branchNode branch (n + 1))).symm

/-! ## Certificate and finite-policy extraction -/

/-- The common-action memory tree satisfies the complete linked-code parity
certificate.  Forward parity follows from the one honest semantic source
that remains in every belief. -/
theorem codeParityCertificate :
    SourceFreeBeliefCodeParityCertificate
      (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := PhysicalAnnotation A)
        (profiledRawJointOneSidedCodeParityDPA A (initial.code A)))
      (initial.code A, initialAnnotation)
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointOneSidedProvenanceValid A strategy)
        (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
          hwin))
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A)))
      certificate.semanticTree := by
  refine {
    initial_code := certificate.initial_public
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact certificate.validAt A strategy hwin initial initialAnnotation _
  · intro node childCode
    exact certificate.next_public _ childCode
  · intro branch
    rw [sourceFreeBeliefParentLinkedCodeParityDPA,
      DetParityAutomaton.comap_accepts_iff,
      certificate.childCodeWord_fst_eq A strategy hwin initial
        initialAnnotation]
    exact profiledRawJointOneSidedSemanticTree_accepts A strategy hwin initial
      (certificate.actualBranch A strategy hwin initial initialAnnotation
        branch)

/-- A finite common-action certificate gives the augmented recurrent policy
without forgetting or re-positionalizing its memory coordinate. -/
noncomputable def toFiniteMemoryPolicy [Fintype Memory] :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
      (Memory := Memory) A strategy hwin certificate.initialMemory
        (initial.code A) initialAnnotation := by
  letI : Fintype certificate.semanticTree.Semantic := by
    change Fintype Memory
    infer_instance
  exact SourceFreeBeliefCodeParityCertificate.toFiniteMemoryPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A)))
    (initial.code A, initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A)))
    certificate.semanticTree
    (certificate.codeParityCertificate A strategy hwin initial
      initialAnnotation)

@[simp] theorem toFiniteMemoryPolicy_run_memory [Fintype Memory]
    (node : TreeNode (LinkedCode A)) :
    (certificate.toFiniteMemoryPolicy A strategy hwin initial
      initialAnnotation |>.run node).2 =
        certificate.semanticTree.stateAt node :=
  by
    simp [toFiniteMemoryPolicy,
      SourceFreeBeliefCodeParityCertificate.toFiniteMemoryPolicy]

end ProfiledRawJointOneSidedPhysicalCommonActionMemoryCertificate

/-! ## Exact semantic memory always exists -/

/-- Perfect-recall memory consisting of one exact compatible source and its
installed physical annotation. -/
abbrev ProfiledRawJointOneSidedPhysicalExactCommonActionMemory :=
  { pair : OneSidedState A strategy × PhysicalAnnotation A //
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy pair.1
      pair.2 }

/-- The winning strategy supplies a closed common-action certificate when the
full exact semantic source is retained.  No finiteness claim is made. -/
noncomputable def profiledRawJointOneSidedPhysicalExactCommonActionCertificate
    (initial : OneSidedState A strategy)
    (initialAnnotation : PhysicalAnnotation A)
    (hinitial : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      initial initialAnnotation) :
    ProfiledRawJointOneSidedPhysicalCommonActionMemoryCertificate
      (Memory :=
        ProfiledRawJointOneSidedPhysicalExactCommonActionMemory A strategy)
      A strategy hwin initial initialAnnotation where
  initialMemory := ⟨(initial, initialAnnotation), hinitial⟩
  belief := fun memory source ↦ source = memory.1.1
  publicCode := fun memory ↦
    (memory.1.1.code A, memory.1.2)
  move := fun memory ↦
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin memory.1.1
      memory.1.2
  next := fun memory childCode ↦
    let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
      (memory.1.1.code A, memory.1.2)
      (profiledRawJointOneSidedSemanticLinkedMove A strategy hwin memory.1.1
        memory.1.2)
      childCode
    let child := memory.1.1.step A actual
    let annotation :=
      profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
        memory.1.1 memory.1.2 actual
    ⟨(child, annotation),
      profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
        hwin memory.1.1 memory.1.2 actual⟩
  initial_public := rfl
  initial_mem := rfl
  belief_at := by
    intro memory
    constructor
    · exact ⟨memory.1.1, rfl⟩
    · intro source hsource
      subst source
      exact ⟨rfl, memory.2⟩
  common_move := by
    intro memory source hsource
    subst source
    rfl
  next_public := by
    intro memory childCode
    let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
      (memory.1.1.code A, memory.1.2)
      (profiledRawJointOneSidedSemanticLinkedMove A strategy hwin memory.1.1
        memory.1.2)
      childCode
    apply Prod.ext
    · change (memory.1.1.step A actual).code A = _
      rw [ProfiledRawJointOneSidedSemanticState.step_code]
      rfl
    · rfl
  successor_mem := by
    intro memory childCode source hsource
    subst source
    rfl

/-- Consequently all common-action, closure, and parity obligations have an
exact perfect-recall solution.  The sole unavailable instance needed for
finite-policy extraction is `Fintype` for this semantic memory. -/
theorem
    nonempty_profiledRawJointOneSidedPhysicalExactCommonActionCertificate
    (initial : OneSidedState A strategy)
    (initialAnnotation : PhysicalAnnotation A)
    (hinitial : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      initial initialAnnotation) :
    Nonempty
      (ProfiledRawJointOneSidedPhysicalCommonActionMemoryCertificate
        (Memory :=
          ProfiledRawJointOneSidedPhysicalExactCommonActionMemory A strategy)
        A strategy hwin initial initialAnnotation) :=
  ⟨profiledRawJointOneSidedPhysicalExactCommonActionCertificate A strategy
    hwin initial initialAnnotation hinitial⟩

end

end DetParityAutomaton

end DistributedSynthesis
