import Huffman.Forest
import Mathlib.Data.List.Sort

namespace Huffman

/-- mkForest produces a sorted forest. -/
theorem mkForest_sorted (freqs : List (α × Nat)) :
    (mkForest (α := α) freqs).Pairwise (· ≤ ·) := by
  simp [mkForest]
  suffices ∀ acc, List.Pairwise (· ≤ ·) acc →
    List.Pairwise (· ≤ ·)
      (freqs.foldl (fun acc (p : α × Nat) =>
        List.orderedInsert (· ≤ ·) (Tree.leaf p.2 p.1) acc) acc) from
    this [] List.Pairwise.nil
  induction freqs with
  | nil => intro acc h; exact h
  | cons _ tl ih =>
    intro acc hacc
    exact ih _ (List.Pairwise.orderedInsert _ _ hacc)

end Huffman
