import Huffman.Forest
import Mathlib.Data.List.Sort

namespace Huffman

/-- mkForest produces a sorted forest. -/
theorem mkForest_sorted (freqs : List (α × Nat)) :
    Forest.Sorted (mkForest freqs) := by
  simp [mkForest]
  suffices ∀ acc, Forest.Sorted acc →
    Forest.Sorted
      (freqs.foldl (fun acc (p : α × Nat) =>
        List.orderedInsert (· ≤ ·) (Tree.leaf p.2 p.1) acc) acc) from
    this [] List.Pairwise.nil
  induction freqs with
  | nil =>
    intro acc h
    exact h
  | cons hd tl ih =>
    intro acc h
    exact ih _ (List.Pairwise.orderedInsert _ _ h)

end Huffman
