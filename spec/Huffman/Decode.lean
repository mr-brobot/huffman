import Huffman.Tree
import Huffman.Encode

namespace Huffman

/-- Decode a single symbol by walking the tree, consuming bits.
    Returns the decoded symbol and the remaining bits. -/
def decodeOne : Tree α → Code → Option (α × Code)
  | .leaf _ s, bits => some (s, bits)
  | .node _ _ _, [] => none
  | .node _ l _, false :: bits => decodeOne l bits
  | .node _ _ r, true :: bits => decodeOne r bits

/-- Decode a bit stream into a list of symbols by repeatedly decoding one symbol.
    Returns `none` if the bit stream is malformed or the tree is a bare leaf
    with remaining bits (no progress). -/
def decode (t : Tree α) : Code → Option (List α)
  | [] => some []
  | b :: bs => do
    let (s, rest) ← decodeOne t (b :: bs)
    if _h : rest.length < (b :: bs).length then
      let syms ← decode t rest
      pure (s :: syms)
    else none
  termination_by bits => bits.length

end Huffman
