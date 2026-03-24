namespace Huffman

/-- Increment the count for `a` in an association list, or append it with count 1. -/
def incCount [BEq α] (a : α) : List (α × Nat) → List (α × Nat)
  | [] => [(a, 1)]
  | (b, n) :: rest =>
    if a == b then (b, n + 1) :: rest
    else (b, n) :: incCount a rest

/-- Count the frequency of each symbol in a list. -/
def freqCount [BEq α] : List α → List (α × Nat)
  | [] => []
  | a :: rest => incCount a (freqCount rest)

end Huffman
