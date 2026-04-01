import Huffman.Tree
import Mathlib.Data.List.Sort

namespace Huffman

/-- A forest is a list of trees. -/
abbrev Forest (α : Type) := List (Tree α)

/-- A forest is sorted when each tree's weight is ≤ all subsequent trees' weights. -/
abbrev Forest.Sorted (f : Forest α) : Prop := f.Pairwise (· ≤ ·)

/-- Build a sorted forest of leaf nodes from a frequency list. -/
def mkForest (freqs : List (α × Nat)) : Forest α :=
  freqs.foldl (fun acc (s, w) => acc.orderedInsert (· ≤ ·) (.leaf w s)) []

/--
Build a Huffman tree by repeatedly merging the two lightest nodes.
Returns `none` if the input frequency list is empty.
-/
def mkTree (freqs : List (α × Nat)) : Option (Tree α) :=
  let forest := mkForest freqs
  merge forest
where
  /-- Merge loop: combine the two lightest trees until one remains. -/
  merge : Forest α → Option (Tree α)
    | [] => none
    | [t] => some t
    | t₁ :: t₂ :: rest =>
      let merged := Tree.node (t₁.weight + t₂.weight) t₁ t₂
      merge (rest.orderedInsert (· ≤ ·) merged)
  termination_by l => l.length
  decreasing_by simp [List.orderedInsert_length]

end Huffman
