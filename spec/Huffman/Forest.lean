import Huffman.Tree

namespace Huffman

/-- A forest is a list of trees. -/
abbrev Forest (α : Type) := List (Tree α)

/-- Insert a tree into a forest sorted by weight (ascending). -/
def insertSorted (t : Tree α) : Forest α → Forest α
  | [] => [t]
  | h :: rest =>
    if t.weight ≤ h.weight then t :: h :: rest
    else h :: insertSorted t rest

theorem insertSorted_length (t : Tree α) (l : Forest α) :
    (insertSorted t l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertSorted]
  | cons h rest ih =>
    simp [insertSorted]
    split <;> simp [ih, Nat.add_comm]

/-- Build a sorted forest of leaf nodes from a frequency list. -/
def mkForest (freqs : List (α × Nat)) : Forest α :=
  freqs.foldl (fun acc (s, w) => insertSorted (.leaf w s) acc) []

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
      merge (insertSorted merged rest)
  termination_by l => l.length
  decreasing_by simp [insertSorted_length]

end Huffman
