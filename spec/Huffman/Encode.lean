import Huffman.Tree

namespace Huffman

/-- A binary code is a list of bools. -/
abbrev Code := List Bool

/-- A code table maps each symbol to its binary code. -/
abbrev CodeTable (α : Type) := List (α × Code)

/-- Build a code table by traversing the tree.
    Left edges are `false`, right edges are `true`. -/
def mkCodeTable : Tree α → CodeTable α
  | .leaf _ s => [(s, [])]
  | .node _ l r =>
    (mkCodeTable l).map (fun (s, c) => (s, false :: c)) ++
    (mkCodeTable r).map (fun (s, c) => (s, true :: c))

end Huffman
