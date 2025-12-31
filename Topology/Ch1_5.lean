import Mathlib
import Mathlib.Data.Set.Card
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

-- Exercise 2: Prove that if A has precisely n distinct elements and B has
-- precisely m distinct elements, where m and n are positive integers, then A ×
-- B has precisely mn distinct elements.

-- I realize this basically just invokes a library proof of the thing we're trying to
-- prove but I'm not sure how to do it more fundamentally...
theorem ex2
  {α β : Type _} (A : Set α) (B : Set β) {n m : ℕ} (hA : A.ncard = n) (hB : B.ncard = m) :
  (A ×ˢ B).ncard = n * m := by
    rw [← hA]
    rw [← hB]
    exact Set.ncard_prod

-- Exercise 3. Let A and B be sets, both of which have at least two distinct
-- members. Prove that there is a subset W ⊆ A × B that is not the Cartesian
-- product of a subset of A with a subset of B. [Thus, not every subset of a
-- Cartesian product is the Cartesian product of a pair of subsets.]
set_option linter.style.commandStart false
theorem ex3
    {α β : Type*} (A : Set α) (B : Set β)       -- Let A and B be sets
    (hA : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂)          -- Two distinct members in A
    (hB : ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂) :        -- Two distinct members in B
    ∃ W : Set (α × β), W ⊆ A ×ˢ B               -- There is a subset W ⊆ A × B
        ∧ ¬ ∃ A' : Set α, ∃ B' : Set β, W = A' ×ˢ B' := by    -- Where W is not A' × B'
    -- We can prove this by constructing an example:
    -- {(a1, b1), (a1, b2), (a2, b1), (a2, b2)} ⊆ A × B
    -- W = {(a1, b2), (a2, b1)}
    rcases hA with ⟨a1, ha1A, a2, ha2A, ha12⟩
    rcases hB with ⟨b1, hb1B, b2, hb2B, hb12⟩
    let W : Set (α × β) := {p | (p.1 = a1 ∧ p.2 = b2) ∨ (p.1 = a2 ∧ p.2 = b1)}
    use W
    constructor
    · -- Prove W ⊆ A × B
      intro x hx
      simp only [mem_setOf_eq, W] at hx -- hx is now an explicit list of what (x.1, x.2) could be
      simp only [mem_prod]              -- We must show x.1 ∈ A and x.2 ∈ B
      -- Match up all of the values x could take with the knowledge that they are ∈ A and ∈ B
      rcases hx with ⟨hx1a1, hx2b2⟩ | ⟨hx1a2, hx2b1⟩
      · simp [hx1a1, hx2b2, ha1A, hb2B]
      · simp [hx1a2, hx2b1, ha2A, hb1B]
    · -- Prove W is not a subset of A' × B' (subsets of A and B)
      simp only [not_exists]
      intro A' B' hW          -- Assume there is a product W = A' × B'
      -- Since (a1,b2) ∈ W and (a2,b1) ∈ W = A' × B
      -- we'd have a1 ∈ A'
      have ha1A' : a1 ∈ A' := by
        have h : (a1, b2) ∈ A' ×ˢ B' := by
          rw [← hW]
          simp [W]
        exact h.1
      -- And b1 ∈ B'
      have hb1B' : b1 ∈ B' := by
        have h : (a2, b1) ∈ A' ×ˢ B' := by
          rw [← hW]
          simp [W]
        exact h.2
      -- That would mean (a1, b1) is in A' × B'
      have ha1b1A'B' : ⟨a1, b1⟩ ∈ A' ×ˢ B' := by
        simp only [mem_prod]
        exact ⟨ha1A', hb1B'⟩
      -- ie, it is in W
      rw [← hW] at ha1b1A'B'
      -- But it is not
      simp [W, ha12, hb12] at ha1b1A'B'

end Ch1_5
