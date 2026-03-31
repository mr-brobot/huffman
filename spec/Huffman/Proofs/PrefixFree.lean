import Huffman.Encode

namespace Huffman

/-- A code table is prefix-free: if one code is a prefix of another, they are equal. -/
def IsPrefixFree (table : CodeTable α) : Prop :=
  ∀ s₁ c₁ s₂ c₂,
    (s₁, c₁) ∈ table → (s₂, c₂) ∈ table →
    c₁ <+: c₂ → c₁ = c₂

/-- The code table of any tree is prefix-free. -/
theorem mkCodeTable_prefixFree (t : Tree α) :
    IsPrefixFree (mkCodeTable t) := by
  induction t with
  | leaf w sym =>
    intro s₁ c₁ s₂ c₂ h₁ h₂ _
    simp [mkCodeTable] at h₁ h₂
    rw [h₁.2, h₂.2]
  | node w l r ihl ihr =>
    intro s₁ c₁ s₂ c₂ h₁ h₂ hpre
    simp only [mkCodeTable, List.mem_append, List.mem_map, Prod.mk.injEq] at h₁ h₂
    cases h₁ with
    | inl h₁ =>
      obtain ⟨⟨_, c₁'⟩, hc₁, rfl, rfl⟩ := h₁
      cases h₂ with
      | inl h₂ =>
        obtain ⟨⟨_, c₂'⟩, hc₂, rfl, rfl⟩ := h₂
        congr 1
        exact ihl _ c₁' _ c₂' hc₁ hc₂ (by simpa using hpre)
      | inr h₂ =>
        obtain ⟨⟨_, c₂'⟩, _, rfl, rfl⟩ := h₂
        simp at hpre
    | inr h₁ =>
      obtain ⟨⟨_, c₁'⟩, hc₁, rfl, rfl⟩ := h₁
      cases h₂ with
      | inl h₂ =>
        obtain ⟨⟨_, c₂'⟩, _, rfl, rfl⟩ := h₂
        simp at hpre
      | inr h₂ =>
        obtain ⟨⟨_, c₂'⟩, hc₂, rfl, rfl⟩ := h₂
        congr 1
        exact ihr _ c₁' _ c₂' hc₁ hc₂ (by simpa using hpre)

/-- Every symbol in the tree has a code in the table. -/
theorem mkCodeTable_complete (t : Tree α) (s : α) (hs : s ∈ t.symbols) :
    ∃ c, (s, c) ∈ mkCodeTable t := by
  induction t with
  | leaf w sym =>
    simp [Tree.symbols] at hs
    exact ⟨[], by simp [mkCodeTable, hs]⟩
  | node w l r ihl ihr =>
    simp [Tree.symbols] at hs
    cases hs with
    | inl hs =>
      obtain ⟨c, hc⟩ := ihl hs
      refine ⟨false :: c, ?_⟩
      unfold mkCodeTable
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨(s, c), hc, rfl⟩
    | inr hs =>
      obtain ⟨c, hc⟩ := ihr hs
      refine ⟨true :: c, ?_⟩
      unfold mkCodeTable
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨(s, c), hc, rfl⟩

end Huffman
