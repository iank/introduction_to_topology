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
  ext x
  constructor
  · -- Prove x ∈ ⋂ (A α ∩ B α) → x ∈ (⋂ A α) ∩ (⋂ B α)
    intro hx
    simp only [mem_iInter, mem_inter_iff] at hx
    simp only [mem_iInter, mem_inter_iff]
    -- Show ∀ i, x ∈ A i ∧ x ∈ B i
    constructor
    · intro i
      exact (hx i).left
    · intro i
      exact (hx i).right
  · -- Prove x ∈ (⋂ A α) ∩ (⋂ B α) → x ∈ ⋂ (A α ∩ B α)
    intro hx
    simp only [mem_iInter, mem_inter_iff] at hx
    simp only [mem_iInter, mem_inter_iff]
    rcases hx with ⟨hA, hB⟩
    intro i
    constructor
    · exact hA i  -- ∀ i, x ∈ A i
    · exact hB i  -- ∀ i, x ∈ B i

-- (e) If for each β ∈ I, A β ⊆ B β then
--     1) ⋃ A α ⊆ ⋃ B α
theorem ex1e_1 (hB_subset_A : ∀ (β : I), A β ⊆ B β) : (⋃ α, A α) ⊆ (⋃ α, B α) := by
  intro x hx                      -- x ∈ ⋃ A α
  simp only [mem_iUnion] at hx    -- ∃ i, x ∈ A i
  rcases hx with ⟨i, hAi⟩
  -- Unpack the goal
  simp only [mem_iUnion]
  use i
  -- Now the goal is to show x ∈ A i → x ∈ B i
  specialize hB_subset_A i        -- A i ⊆ B i,
  exact hB_subset_A hAi           -- and x ∈ A i. ∴ x ∈ B i

--     2) ⋂ A α ⊆ ⋂ B α
theorem ex1e_2 (hB_subset_A : ∀ (β : I), A β ⊆ B β) : (⋂ α, A α) ⊆ (⋂ α, B α) := by
  -- Need to show x ∈ ⋂ A α → x ∈ ⋂ B α
  intro x hx
  simp only [mem_iInter] at hx
  simp only [mem_iInter]
  -- Equivalent to showing ∀ i, x ∈ A i → ∀ i, x ∈ B i
  intro i
  specialize hx i
  specialize hB_subset_A i
  exact hB_subset_A hx

-- (f) Let D ⊆ S.
variable {D : Set S}
--     Then:
--     1) ⋃ (A α ∩ D) = (⋃ A α) ∩ D
theorem ex1f_1 : ⋃ α, (A α ∩ D) = (⋃ α, A α) ∩ D := by
  apply subset_antisymm
  · -- Show ⋃ (A α ∩ D) ⊆ (⋃ A α) ∩ D
    intro x hx
    -- Rewrite goal as: (∃ i, x ∈ A i) ∧ x ∈ D
    simp only [mem_inter_iff, mem_iUnion]
    -- Rewrite hx as:     ∃ i, x ∈ A i ∧ x ∈ D
    simp only [mem_iUnion, mem_inter_iff, exists_and_right] at hx
    exact hx
  · -- Show (⋃ A α) ∩ D ⊆ ⋃ (A α ∩ D)
    intro x hx
    simp only [mem_iUnion, mem_inter_iff, exists_and_right]
    simp only [mem_inter_iff, mem_iUnion] at hx
    exact hx

--     2) ⋂ (A α ∪ D) = (⋂ A α) ∪ D
theorem ex1f_2 : ⋂ α, (A α ∪ D) = (⋂ α, A α) ∪ D := by
  apply subset_antisymm
  · -- Show ⋂ (A α ∪ D) ⊆ (⋂ A α) ∪ D
    intro x hx
    simp only [mem_iInter, mem_union] at hx
    simp only [mem_union, mem_iInter]
    -- ∀ i, x ∈ A i ∨ x ∈ D
    by_cases hxD : x ∈ D
    case pos =>
      right
      exact hxD
    case neg =>
      left
      intro i
      specialize hx i
      exact Or.resolve_right hx hxD
  · -- Show (⋂ A α) ∪ D ⊆ ⋂ (A α ∪ D)
    sorry

end

-- Exercise 2 (TODO)
-- Exercise 3 (TODO)
-- Exercise 4 (TODO)
-- Exercise 5 (TODO)

end Ch1_4
