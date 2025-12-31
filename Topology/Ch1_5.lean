import Mathlib
open Set

namespace Ch1_5
-- Section 5, products of sets

section
-- Exercise 1 Let X ⊆ A, Y ⊆ B.
variable {A B : Type} (X : Set A) (Y : Set B)
-- Prove that C(X × Y) = A × C(Y) ∪ C(X) × B
theorem ex1 : (X ×ˢ Y)ᶜ = ((univ : Set A) ×ˢ Yᶜ) ∪ (Xᶜ ×ˢ (univ : Set B)) := by
  ext ⟨a, b⟩
  constructor
  · -- Show (a, b) ∈ (X × Y)ᶜ → (a, b) ∈ (A × Yᶜ) ∪ (Xᶜ × B)
    intro hab                                                 -- (a, b) ∈ (X × Y)ᶜ
    -- hab: (a, b) ∈ (X × Y)ᶜ means (a, b) ∉ (X × Y), so
    -- hab: a ∈ X → b ∉ Y or, equivalently, b ∈ Y → a ∉ X.
    simp only [mem_compl_iff, mem_prod, not_and] at hab       -- hab now: a ∈ X → b ∉ Y
    -- Goal: (a, b) ∈ (A × Yᶜ) ∪ (Xᶜ × B) means
    --       (a ∈ A ∧ b ∉ Y) ∨ (b ∈ B ∧ a ∉ X)
    -- But a ∈ A and b ∈ B are always true, so we can reduce this to
    --       (b ∉ Y) ∨ (a ∉ X)
    simp only [mem_union, mem_prod, mem_univ, mem_compl_iff, true_and, and_true]
    -- Either a ∈ X or it isn't
    by_cases ha : a ∈ X
    · left        -- If x ∈ X, we know b ∉ Y by hab
      exact hab ha
    · right       -- If x ∉ X
      exact ha
  · -- Show (a, b) ∈ (A × Yᶜ) ∪ (Xᶜ × B) → (a, b) ∈ (X × Y)ᶜ
    intro hab
    -- Show that if hab: (a, b) ∈ (A × Yᶜ) ∪ (Xᶜ × B),
    -- then (a, b) ∈ (X × Y)ᶜ
    -- That is, (a, b) ∉ (X × Y)
    simp only [mem_union, mem_prod, mem_univ, mem_compl_iff, true_and, and_true] at hab
    -- hab simplifies to (b ∉ Y) ∨ (a ∉ X) as before (a ∈ A and b ∈ B always)
    -- Obviously if b ∉ Y or a ∉ X then (a, b) ∉ (X × Y)
    simp only [mem_compl_iff, mem_prod, not_and]
    intro haX hbY
    -- So just show that a ∈ X and b ∈ Y can't both be true
    rcases hab with hbNotY | haNotX
    · exact hbNotY hbY
    · exact haNotX haX

-- This is basically DeMorgan's theorem and lean can just work it out algebraically:
theorem ex1' :
    (X ×ˢ Y)ᶜ =
      ((univ : Set A) ×ˢ Yᶜ) ∪ (Xᶜ ×ˢ (univ : Set B)) := by
  ext ⟨a,b⟩
  by_cases ha : a ∈ X <;>
    by_cases hb : b ∈ Y <;>
      simp_all
end

-- Exercise 2 (TODO)
-- Exercise 3 (TODO)

end Ch1_5
