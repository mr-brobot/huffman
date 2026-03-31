import Mathlib.Data.List.Sort

namespace Huffman

/-- A Huffman tree over symbols of type `α`. -/
inductive Tree (α : Type) where
  | leaf (weight : Nat) (symbol : α)
  | node (weight : Nat) (left right : Tree α)
  deriving Repr, BEq

/-- Extract the weight of a tree. -/
def Tree.weight : Tree α → Nat
  | .leaf w _ => w
  | .node w _ _ => w

/-- Collect all symbols in a tree. -/
def Tree.symbols : Tree α → List α
  | .leaf _ s => [s]
  | .node _ l r => l.symbols ++ r.symbols

/-- Weight comparison on trees. -/
instance : LE (Tree α) where le t₁ t₂ := t₁.weight ≤ t₂.weight

instance : DecidableRel (α := Tree α) (· ≤ ·) :=
  fun t₁ t₂ => Nat.decLe t₁.weight t₂.weight

instance : Std.Total (α := Tree α) (· ≤ ·) where
  total t₁ t₂ := Nat.le_total t₁.weight t₂.weight

instance : IsTrans (Tree α) (· ≤ ·) where
  trans {a b c} (h₁ : a ≤ b) (h₂ : b ≤ c) :=
    show a ≤ c from Nat.le_trans h₁ h₂

end Huffman
