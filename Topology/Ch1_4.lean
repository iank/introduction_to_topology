import Mathlib

open Set

namespace Ch1_4

-- Section 4, indexed families of sets

section
-- Exercise 1. Let A_α, B_α (α ∈ I) be two indexed families of subsets of a set S.
variable {S I : Type}
variable {A B : I → Set S}

-- (a) For each β ∈ I, A_β ⊆ ⋃ α, A_α
theorem ex1a (β : I) : A β ⊆ ⋃ α, A α := by
  intro x hx                -- let x ∈ A_β, we must show x ∈ ⋃ A_α
  simp only [mem_iUnion]    -- transform the goal into ∃ i, x ∈ A_i
  use β                     -- let i = β

-- (b) For each β ∈ I, ⋂ A_α ⊆ A_β
theorem ex1b (β : I) : ⋂ α, A α ⊆ A β := by
  intro x hx                    -- x ∈ ⋂ A_α
  simp only [mem_iInter] at hx  -- transform hx into ∀ i, x ∈ A i
  exact hx β                    -- β ∈ I, so let i = β in hx

-- (c) ⋃ α, (A_α ∪ B_α) = (⋃ α, A_α) ∪ (⋃ α, B_α)
theorem ex1c : ⋃ α, (A α ∪ B α) = (⋃ α, A α) ∪ (⋃ α, B α) := by
  ext x                         -- Now we must prove x ∈ left ↔ x ∈ right
  constructor
  · -- Prove x ∈ ⋃ (A α ∪ B α) → x ∈ (⋃ A α) ∪ (⋃ B α)
    intro hx                                 -- x ∈ ⋃ (A α ∪ B α)
    simp only [mem_iUnion, mem_union] at hx  -- ∃ i, x ∈ A i ∨ x ∈ B i
    rcases hx with ⟨i, hi⟩                   -- For a given i we have x ∈ A i ∨ x ∈ B i
    simp only [mem_iUnion, mem_union]        -- Goal is now to show ∃ i, x ∈ A i OR ∃ i, x ∈ B i
    rcases hi with hAi | hBi                 -- Split up `hi` and match it with the goal
    · left
      use i
    · right
      use i
  · -- Prove x ∈ (⋃ A α) ∪ (⋃ B α) → x ∈ ⋃ (A α ∪ B α)
    intro hx
    simp only [mem_iUnion, mem_union] at hx
    simp only [mem_iUnion, mem_union]
    rcases hx with hA | hB
    · -- ∃ i, x ∈ A i
      rcases hA with ⟨i, hi⟩
      use i
      left
      exact hi
    · -- ∃ i, x ∈ B i
      rcases hB with ⟨i, hi⟩
      use i
      right
      exact hi


-- (d) ⋂ α, (A_α ∩ B_α) = (⋂ α, A_α) ∩ (⋂ α, B_α)
theorem ex1d : ⋂ α, (A α ∩ B α) = (⋂ α, A α) ∩ (⋂ α, B α) := by
  sorry

-- (e) TODO
-- (f) TODO

end

-- Exercise 2 (TODO)
-- Exercise 3 (TODO)
-- Exercise 4 (TODO)
-- Exercise 5 (TODO)

end Ch1_4
