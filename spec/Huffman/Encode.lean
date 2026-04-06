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

/-- Look up the code for a symbol in a code table. -/
def lookup [BEq α] (s : α) : CodeTable α → Option Code
  | [] => none
  | (s', c') :: rest => if s == s' then some c' else lookup s rest

/-- Encode a list of symbols into a bit stream using a code table. -/
def encode [BEq α] (table : CodeTable α) : List α → Option Code
  | [] => some []
  | s :: rest => do
    let c ← lookup s table
    let bits ← encode table rest
    pure (c ++ bits)

end Huffman
