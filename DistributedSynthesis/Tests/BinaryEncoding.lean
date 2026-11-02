/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PaddingProjection
import DistributedSynthesis.Library.Distributed.BlockEmbedding
import DistributedSynthesis.Library.Logic.BinaryClock

/-! Small clients of the independent padding and block-logic APIs.
There is deliberately no binary-undecidability endpoint: composition is pending. -/

open DistributedSynthesis FullViewPath PaddingProjection

private def active : Nat → Bool := fun t ↦ decide (t % 5 = 0)

example : core active [.left, .both] = true := by decide
example : core active [.left, .right] = false := by decide
example : core active [.left, .right, .both, .both, .both, .left] = false := by decide
example : virtualDepth active 9 = 2 := by decide
example : project active (evaluate [.left, .both]).one =
    project (fun _ ↦ true) (evaluate [.left]).two := by decide

example {Output : Type*} (t : Nat) (label : Vertex → Output)
    (echo : ∀ h : List Graph, h.length = t → core active h = false →
      label (.inl (evaluate h).one) = label (.inr (evaluate h).two))
    {u v : Vertex} (hu : Reachable t u) (hv : Reachable t v)
    (hp : vertexProject active u = vertexProject active v) : label u = label v :=
  fiber_agreement active t label echo hu hv hp

example {t : Nat} {v : Vertex} (hv : Reachable t v) :
    ∃! u, Reachable (virtualDepth active t) u ∧ coordinate u = vertexProject active v :=
  unique_virtual_view active hv

example {Letter : Type*} (I : Proc → Letter → Prop) (w : OmegaWord Letter) (K : Nat)
    (hf : LTL.Satisfies I w (LTL.BinaryClock.frame .one .two K)) (t : Nat) :
    LTL.Satisfies I (w.drop t) (LTL.BinaryClock.marker .one) ↔
      ∃ n, t = (2*K+3)*n := LTL.BinaryClock.clock_exact I w .one .two K hf t

#guard_msgs (drop info) in
#check LTL.BlockTranslation.correct

example (h : List Graph) :
    BlockEmbedding.pairProject (BlockEmbedding.active 5) (BlockEmbedding.embed 5 h) =
      BlockEmbedding.pairProject (fun _ ↦ true) h :=
  BlockEmbedding.embed_projection 5 (by omega) (by decide) h

-- An even-length block has odd padding, so it does not restore owners.
example : BlockEmbedding.pairProject (BlockEmbedding.active 2)
    (BlockEmbedding.embed 2 [.right]) ≠ BlockEmbedding.pairProject (fun _ ↦ true) [.right] := by
  decide

example (K : Nat) (source : Nat → Graph) (n j : Nat) (hj : j < K) (u : Vertex) :
    (Reachable (n+1) u ∧ coordinate u = vertexProject (BlockEmbedding.active (2*K+3))
      (BlockEmbedding.endpoint
        (BlockEmbedding.graphPrefix (BlockEmbedding.stream (2*K+3) source)
          ((2*K+3)*n+1+(2*j+3))) .one)) ↔
      u = BlockEmbedding.endpoint (BlockEmbedding.graphPrefix source (n+1)) .two :=
  BlockEmbedding.binary_stream_data_view_iff K source n j hj .one u
