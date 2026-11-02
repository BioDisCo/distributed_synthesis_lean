/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefHistory

/-!
# Reflected ternary order of graph completions
-/

namespace DistributedSynthesis

/-- Replace one graph-completion word by the next ternary block, reflecting at odd positions. -/
def reflectedTernaryExpandOne (k : Nat) (word : List Graph) : List (List Graph) :=
  if k % 2 = 0 then
    [word ++ [.right], word ++ [.both], word ++ [.left]]
  else
    [word ++ [.left], word ++ [.both], word ++ [.right]]

/-- One reflected ternary expansion step over an oriented list of graph words. -/
def reflectedTernaryExpand (words : List (List Graph)) : List (List Graph) :=
  words.zipIdx.flatMap (fun pair => reflectedTernaryExpandOne pair.2 pair.1)

@[simp]
theorem reflectedTernaryExpandOne_length (k : Nat) (word : List Graph) :
    (reflectedTernaryExpandOne k word).length = 3 := by
  unfold reflectedTernaryExpandOne
  split <;> rfl

theorem reflectedTernaryExpandOne_even
    {k : Nat} (hk : k % 2 = 0) (word : List Graph) :
    reflectedTernaryExpandOne k word =
      [word ++ [.right], word ++ [.both], word ++ [.left]] := by
  simp [reflectedTernaryExpandOne, hk]

theorem reflectedTernaryExpandOne_odd
    {k : Nat} (hk : k % 2 ≠ 0) (word : List Graph) :
    reflectedTernaryExpandOne k word =
      [word ++ [.left], word ++ [.both], word ++ [.right]] := by
  simp [reflectedTernaryExpandOne, hk]

/--
Corollary `cor:reflectedorder`: the next oriented graph-word list is obtained
by replacing even-position words by `right,both,left` and odd-position words by
the reflected `left,both,right` block.
-/
theorem reflected_ternary_order_step (words : List (List Graph)) :
    reflectedTernaryExpand words =
      words.zipIdx.flatMap (fun pair => reflectedTernaryExpandOne pair.2 pair.1) := by
  rfl

end DistributedSynthesis
