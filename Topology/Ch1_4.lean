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
  sorry

-- (c) ⋃ α, (A_α ∪ B_α) = (⋃ α, A_α) ∪ (⋃ α, B_α)
theorem ex1c : ⋃ α, (A α ∪ B α) = (⋃ α, A α) ∪ (⋃ α, B α) := by
  sorry

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
