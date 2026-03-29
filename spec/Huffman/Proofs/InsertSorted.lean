import Huffman.Forest

namespace Huffman

/-- Comparison on trees by weight. -/
def Tree.le (t₁ t₂ : Tree α) : Prop := t₁.weight ≤ t₂.weight

instance : LE (Tree α) where
  le := Tree.le

/-- A forest is sorted by weight (ascending).
    Each element is ≤ all elements after it. -/
inductive Sorted : Forest α → Prop where
  | nil : Sorted []
  | cons (hd : Tree α) (tl : Forest α) :
      (∀ y ∈ tl, hd ≤ y) → Sorted tl → Sorted (hd :: tl)

theorem Sorted.tail {a : Tree α} {l : Forest α}
    (h : Sorted (a :: l)) : Sorted l := by
  cases h; assumption

theorem Sorted.forall_le {a : Tree α} {l : Forest α}
    (h : Sorted (a :: l)) : ∀ y ∈ l, a ≤ y := by
  cases h; assumption

/-- Membership in insertSorted is the original forest plus the inserted element. -/
theorem mem_insertSorted (t y : Tree α) (l : Forest α) :
    y ∈ insertSorted t l ↔ y = t ∨ y ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons hd tl ih =>
    simp only [insertSorted]
    constructor
    · split
      · intro h
        cases h with
        | head => left; rfl
        | tail _ h => right; exact h
      · intro h
        cases h with
        | head => right; exact List.Mem.head _
        | tail _ h =>
          cases ih.mp h with
          | inl heq => left; exact heq
          | inr hmem => right; exact List.Mem.tail _ hmem
    · split
      · intro h
        cases h with
        | inl heq => exact heq ▸ List.Mem.head _
        | inr hmem => exact List.Mem.tail _ hmem
      · intro h
        cases h with
        | inl heq =>
          exact List.Mem.tail _ (ih.mpr (Or.inl heq))
        | inr hmem =>
          cases hmem with
          | head => exact List.Mem.head _
          | tail _ h => exact List.Mem.tail _ (ih.mpr (Or.inr h))

/-- Inserting into a sorted forest preserves sortedness. -/
theorem insertSorted_sorted (t : Tree α) (l : Forest α)
    (h : Sorted l) : Sorted (insertSorted t l) := by
  induction l with
  | nil =>
    exact Sorted.cons t [] (fun _ h => nomatch h) Sorted.nil
  | cons hd tl ih =>
    simp only [insertSorted]
    split
    case isTrue hle =>
      apply Sorted.cons
      · intro y hy
        cases hy with
        | head => exact hle
        | tail _ hmem => exact Nat.le_trans hle (h.forall_le y hmem)
      · exact h
    case isFalse hgt =>
      have hle : hd ≤ t := Nat.le_of_not_le hgt
      apply Sorted.cons
      · intro y hy
        cases (mem_insertSorted t y tl).mp hy with
        | inl heq => exact heq ▸ hle
        | inr hmem => exact h.forall_le y hmem
      · exact ih h.tail

/-- mkForest produces a sorted forest. -/
theorem mkForest_sorted (freqs : List (α × Nat)) :
    Sorted (mkForest (α := α) freqs) := by
  simp [mkForest]
  suffices ∀ acc, Sorted acc →
    Sorted (freqs.foldl (fun acc (p : α × Nat) =>
      insertSorted (.leaf p.2 p.1) acc) acc) from
    this [] Sorted.nil
  induction freqs with
  | nil => intro acc h; exact h
  | cons _ tl ih =>
    intro acc hacc
    exact ih _ (insertSorted_sorted _ _ hacc)

end Huffman
