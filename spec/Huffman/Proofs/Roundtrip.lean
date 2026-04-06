import Huffman.Encode
import Huffman.Decode
import Huffman.Proofs.PrefixFree

namespace Huffman

/-- Soundness: if `lookup` returns a code, that entry is in the table. -/
lemma lookup_mem_sound [BEq α] [LawfulBEq α] {s : α} {c : Code} {table : CodeTable α}
    (h : lookup s table = some c) : (s, c) ∈ table := by
  induction table with
  | nil =>
    unfold lookup at h
    exact Option.noConfusion rfl (heq_of_eq h)
  | cons p rest ih =>
    obtain ⟨s', c'⟩ := p
    simp only [lookup] at h
    split at h
    · have heq := eq_of_beq ‹_›
      subst heq
      injection h with h; symm at h;
      subst h
      exact List.Mem.head _
    · apply ih at h
      exact List.Mem.tail _ (h)

/-- Completeness: if a symbol has an entry in the table, `lookup` succeeds. -/
lemma lookup_mem_complete [BEq α] [LawfulBEq α] {s : α} {c : Code} {table : CodeTable α}
    (h : (s, c) ∈ table) : ∃ c', lookup s table = some c' := by
  induction table with
  | nil => 
    have habs := List.not_mem_nil h
    exact habs.elim
  | cons p rest ih =>
    obtain ⟨s', c'⟩ := p
    simp only [lookup]
    by_cases heq : s = s'
    · subst heq
      simp only [beq_self_eq_true, if_true]
      exact ⟨c', rfl⟩
    · have hbeq : (s == s') = false := by simp [heq]
      simp only [hbeq, Bool.false_eq_true, if_false]
      simp only [List.mem_cons] at h
      have hex := h.resolve_left (by rintro ⟨_, _⟩; exact heq rfl)
      exact ih hex

/-- Decoding one symbol from a known code followed by remaining bits. -/
lemma decodeOne_append {t : Tree α} {s : α} {c : Code}
    (hmem : (s, c) ∈ mkCodeTable t) (rest : Code) :
    decodeOne t (c ++ rest) = some (s, rest) := by
  induction t generalizing s c with
  | leaf w s' =>
    simp only [mkCodeTable, List.mem_singleton] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    rfl
  | node w l r ihl ihr =>
    simp only [mkCodeTable, List.mem_append, List.mem_map, Prod.mk.injEq] at hmem
    cases hmem with
    | inl h =>
      obtain ⟨⟨s', c'⟩, hc, rfl, rfl⟩ := h
      show decodeOne l (c' ++ rest) = some (s', rest)
      exact ihl hc
    | inr h =>
      obtain ⟨⟨s', c'⟩, hc, rfl, rfl⟩ := h
      show decodeOne r (c' ++ rest) = some (s', rest)
      exact ihr hc

/-- Decode steps correctly over one codeword prepended to remaining bits. -/
lemma decode_append_code {t : Tree α} {s : α} {c bits : Code} {syms : List α}
    (hdc : decodeOne t (c ++ bits) = some (s, bits))
    (hne : c ≠ [])
    (hdec : decode t bits = some syms) :
    decode t (c ++ bits) = some (s :: syms) := by
  cases c with
  | nil => exact absurd rfl hne
  | cons b cs =>
    have hdc' : decodeOne t (b :: (cs ++ bits)) = some (s, bits) := hdc
    have hlt : bits.length < (b :: (cs ++ bits)).length := by
      simp [List.length_cons, List.length_append]; omega
    unfold decode
    simp [hdc', hdec]; omega

/-- Roundtrip: decoding an encoded message recovers the original.
    Requires all codes to be non-empty (i.e., the tree is a node with ≥2 symbols). -/
theorem decode_encode [BEq α] [LawfulBEq α] (t : Tree α)
    (ht : ∀ s c, (s, c) ∈ mkCodeTable t → c ≠ [])
    (input : List α)
    (hsym : ∀ s ∈ input, s ∈ t.symbols) :
    ∃ bits, encode (mkCodeTable t) input = some bits ∧ decode t bits = some input := by
  induction input with
  | nil => exact ⟨[], rfl, by simp [decode]⟩
  | cons s rest ih =>
    have hs : s ∈ t.symbols := hsym s (List.Mem.head _)
    have hrest : ∀ s' ∈ rest, s' ∈ t.symbols := fun s' h => hsym s' (List.Mem.tail _ h)
    obtain ⟨bits, henc, hdec⟩ := ih hrest
    obtain ⟨c_full, hc_full⟩ := mkCodeTable_complete t s hs
    obtain ⟨c, hlookup⟩ := lookup_mem_complete hc_full
    have hc_mem := lookup_mem_sound hlookup
    refine ⟨c ++ bits, ?_, ?_⟩
    · -- encode (s :: rest) = some (c ++ bits)
      simp [encode, hlookup, henc]
    · -- decode (c ++ bits) = some (s :: rest)
      exact decode_append_code (decodeOne_append hc_mem bits) (ht s c hc_mem) hdec

end Huffman
