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

end Huffman
