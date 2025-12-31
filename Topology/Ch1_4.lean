import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

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
    intro x hx
    simp only [mem_iInter, mem_union]
    simp only [mem_iInter, mem_union] at hx
    intro i
    rcases hx with hxAi | hxD
    · left
      exact hxAi i
    · right
      exact hxD
end

section
-- Exercise 2. Let A, B, D ⊆ S. Then prove:
variable {S : Type}
variable (A B D : Set S)
-- a) A ∩ (B ∪ D) = (A ∩ B) ∪ (A ∩ D)
theorem ex2a : A ∩ (B ∪ D) = (A ∩ B) ∪ (A ∩ D) := by
  apply subset_antisymm
  · intro x hx
    simp only [mem_inter_iff, mem_union] at hx    -- hx:   x ∈ A ∧ (x ∈ B ∨ x ∈ D)
    simp only [mem_inter_iff, mem_union]          -- goal: (x ∈ A ∧ x ∈ B) ∨ (x ∈ A ∧ x ∈ D)
    rcases hx with ⟨hxA, hxBorD⟩
    rcases hxBorD with hxB | hxD  -- x ∈ B or x ∈ D
    · left                        -- if x ∈ B, match left side of goal
      exact ⟨hxA, hxB⟩
    · right
      exact ⟨hxA, hxD⟩            -- if x ∈ D, match right
  · intro x hx
    simp only [mem_inter_iff, mem_union] at hx    -- hx:   x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ D
    simp only [mem_inter_iff, mem_union]          -- goal: x ∈ A ∧ (x ∈ B ∨ x ∈ D)
    -- Just unpack hx and construct the goal, as above
    rcases hx with ⟨hxA, hxB⟩ | ⟨hxA, hxD⟩
    · constructor
      · exact hxA
      · left
        exact hxB
    · constructor
      · exact hxA
      · right
        exact hxD

-- b) A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D)
theorem ex2b : A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by
  apply subset_antisymm
  · intro x hx
    simp only [mem_union, mem_inter_iff] at hx
    simp only [mem_union, mem_inter_iff]
    rcases hx with hxA | ⟨hxB, hxD⟩
    · constructor
      · left
        exact hxA
      · left
        exact hxA
    · constructor
      · right
        exact hxB
      · right
        exact hxD
  · intro x hx
    simp only [mem_union, mem_inter_iff] at hx
    simp only [mem_union, mem_inter_iff]
    -- hx:   (x ∈ A or x ∈ B), and (x ∈ A or x ∈ D)
    -- goal: Either x ∈ A, or (x ∈ B and x ∈ D)
    by_cases hxA: x ∈ A
    case pos =>       -- x ∈ A
      left
      exact hxA
    case neg =>       -- x ∉ A
      right
      simpa [hxA] using hx
end

section
-- Exercise 3. Let A_α (α ∈ I) be an indexed family of subsets of a set S. Let J ⊆ I,
variable {S I : Type}
variable {A : I → Set S}
variable {J : Set I}
-- Then: a) (⋂ α ∈ J, A α) ⊇ (⋂ α ∈ I, A α)
theorem ex3a : ⋂ α ∈ J, A α ⊇ ⋂ α, A α := by
  intro x hx                    -- We have: x ∈ ⋂ A α
  simp only [mem_iInter] at hx  --      ie: ∀ i, x ∈ A i
  simp only [mem_iInter]        -- We must show that ∀ j ∈ J, x ∈ A j
  intro j hxAj                  -- But we already know ∀ i, x ∈ A i
  specialize hx j               -- Which holds in particular for any j ∈ J, since J ⊆ I
  exact hx

--       b) (⋃ α ∈ J, A α) ⊆ (⋃ α ∈ I, A α)
theorem ex3b : ⋃ α ∈ J, A α ⊆ ⋃ α, A α := by
  -- Basically just show ∀ j ∈ J, j ∈ I
  intro x hx
  simp only [mem_iUnion, exists_prop] at hx
  simp only [mem_iUnion]
  rcases hx with ⟨j, hxAj⟩
  use j
  exact hxAj.right
end

section
-- Exercise 4.
-- Let A_α (α ∈ I) be an indexed family of subsets of a set S. Let B ⊆ S.
variable {S I : Type}
variable {A : I → Set S}
variable (B : Set S)
-- Prove that:
-- a) B ⊆ ⋂ A α IFF ∀ β ∈ I, B ⊆ A β
theorem ex4a : B ⊆ ⋂ α, A α ↔ ∀ (β : I), B ⊆ A β := by
  constructor
  · intro hB i x hx                   -- Goal: show x ∈ B → x ∈ A i
    have hxA : x ∈ ⋂ α, A α := hB hx  -- B ⊆ ⋂ A α, so x ∈ ⋂ A α
    simp only [mem_iInter] at hxA
    specialize hxA i
    exact hxA
  · intro hB x hxB                    -- Goal: Show x ∈ B → x ∈ ⋃ A α
    -- ∀ β, B ⊆ A β
    simp only [mem_iInter]
    intro i
    specialize hB i
    exact hB hxB


-- b) ⋃ A α ⊆ B IFF ∀ β ∈ I, A β ⊆ B
theorem ex4b : ⋃ α, A α ⊆ B ↔ ∀ (β : I), A β ⊆ B := by    -- This is basically iUnion_subset_iff
  constructor
  -- Forward case
  · intro h α x hx                -- Goal: show x ∈ A α → x ∈ B
    apply h                       -- h shows x ∈ B, if (new goal) x ∈ ⋃ A α
    simp only [mem_iUnion]        -- Equivalently, if ∃ i, x ∈ A i
    use α                         -- i = α
  -- Reverse case
  · intro h x hx                  -- Goal: show x ∈ ⋃ A α → x ∈ B
    simp only [mem_iUnion] at hx  -- ie, show ∃ i, x ∈ A i → x ∈ B
    rcases hx with ⟨i, hxAi⟩      -- Unpack i, x ∈ A i
    specialize h i                -- ∀ β, A β ⊆ B, so A i ⊆ B
    apply h                       -- Showing x ∈ A i will show x ∈ B
    exact hxAi

end

section
-- Exercise 5.
-- Let I be the set of real numbers that are greater than 0.
-- For each x ∈ I, let A_x be the open interval (0, x).
-- For each x ∈ I, let B_x be the closed interval [0, x].
abbrev I := {x : ℝ // 0 < x}
def A (x : I) : Set ℝ := {y : ℝ | 0 < y ∧ y < (x : ℝ)}
def B (x : I) : Set ℝ := {y : ℝ | 0 ≤ y ∧ y ≤ (x : ℝ)}

-- Prove that:
-- i)   ⋂ A_x = ∅
theorem ex5_i : (⋂ x : I, A x) = (∅ : Set ℝ) := by
  apply subset_antisymm
  ·         -- Show ⋂ A x ⊆ ∅
    intro y hy
    simp only [mem_iInter] at hy    -- hy: ∀ (i : I), y ∈ A i
    -- Show that hy is false by constructing a counterexample
    -- For any given y ∈ I there is an A i where i < y, so y ∉ A i
    let i : I := ⟨1, by simp⟩
    have hy_i := hy i                     -- If y ∈ every A i, it must be in A i
    rcases hy_i with ⟨hy_pos, hy_lt_i⟩    -- This means y is positive and less than i
    let j : I := ⟨y/2, by simp [hy_pos]⟩  -- Now let j = y/2
    have hy_j := hy j                     -- If y ∈ every A i, it must also be in A j
    rcases hy_j with ⟨hy_pos2, hy_lt_j⟩   -- This means y is also less than j
    simp only [j] at hy_lt_j              -- We have y < y / 2
    have j_lt_y : (↑j : ℝ) < y := by      -- Now show y / 2 < y
      simp only [j]
      exact half_lt_self hy_pos           -- 0 < a → a / 2 < a
    exact lt_asymm hy_lt_j j_lt_y         -- Since y < y / 2 and y / 2 < y, y ∈ ∅
  · simp    -- Trivial: ∅ ⊆ ⋂ A x

-- ii)  ⋃ A_x = I
theorem ex5_ii : (⋃ x : I, A x) = {y : ℝ | 0 < y} := by
  apply subset_antisymm
  ·                                   -- Goal: prove ⋃ A x ⊆ I
    intro n hn                        -- Let n ∈ ⋃ A x
    simp only [mem_iUnion] at hn      -- ∃ i, n ∈ A i
    simp only [mem_setOf_eq]          -- Showing n ∈ I is equivalent to showing n > 0
    rcases hn with ⟨i, hnAi⟩          -- Unpack i and n ∈ A i
    rcases hnAi with ⟨hnpos, hn_lt_i⟩ -- n ∈ A i → 0 < n and n < i, by definition of A i
    exact hnpos
  ·                                   -- Goal: prove I ⊆ ⋃ A x
    intro n hn                        -- Let n ∈ I
    simp only [mem_setOf_eq] at hn    -- n ∈ I → n > 0
    simp only [mem_iUnion]            -- Goal: prove ∃ i, n ∈ A i
    -- ie, the goal is ⟨i, proof that n ∈ A i⟩
    let i : I := ⟨n + 1, by linarith⟩
    refine ⟨i, ?_⟩
    -- Now prove n ∈ A i
    constructor   -- ie, prove n is positive and < i
    · exact hn    -- n > 0
    · linarith    -- n < i + 1

-- iii) ⋂ B_x = {0}
theorem ex5_iii : (⋂ x : I, B x) = ({0} : Set ℝ) := by
  apply subset_antisymm
  ·         -- Show ⋂ B x ⊆ 0
    intro y hy
    simp only [mem_iInter] at hy        -- hy: ∀ i, y ∈ B i
    simp only [mem_singleton_iff]       -- Goal: prove y = 0
    by_contra h                         -- Suppose y ≠ 0
    -- As an aside, I need to show that this means y > 0
    have hyge : y ≥ 0 := by
      let i0 : I := ⟨1, by simp⟩
      have hyIn := hy i0
      simp only [B] at hyIn
      exact hyIn.1
    have hypos : 0 < y := lt_of_le_of_ne hyge (ne_comm.mp h)
    -- Now proceed with the argument
    let j : I := ⟨y/2, by simp [hypos]⟩ -- Let j = y/2
    have hy_j := hy j                   -- ∀ i, y ∈ B i → y ∈ B j
    rcases hy_j with ⟨hy_ge_0, hy_le_j⟩ -- y ≤ j by definition of B
    simp only [j] at hy_le_j            -- ie, y ≤ y / 2
    linarith [hy_le_j, hypos]           -- But y > 0, contradiction.
  ·         -- Show {0} ⊆ ⋂ B
    intro y hy
    simp only [mem_singleton_iff] at hy
    simp only [mem_iInter]              -- ie, show y = 0 → ∀ i, y ∈ B i
    intro i                             -- For any given i
    constructor                         -- B i is [0,i], so we must show that y ≥ 0 and y ≤ i
    · linarith                          -- 0 ≤ 0
    · rw [hy]                           -- 0 ≤ i. i ∈ I, so i > 0 by definition.
      exact le_of_lt i.property         -- i.property : 0 < i → 0 ≤ i

-- iv)  ⋃ B_x = I ∪ {0}
theorem ex5_iv : (⋃ x : I, B x) = ({y : ℝ | 0 < y} ∪ {0}) := by
  apply subset_antisymm
  ·         -- Show ⋃ B_x ⊆ I ∪ {0}
    intro n hn
    simp only [mem_iUnion] at hn        -- ∃ i, n ∈ B i
    rcases hn with ⟨i, hnBi⟩            -- Unpack i and n ∈ B i
    rcases hnBi with ⟨hn_gt_0, hn_lt_i⟩ -- n ∈ A i → 0 ≤ n and n ≥ i, by definition of B i
    simp only [union_singleton, mem_insert_iff, mem_setOf_eq]   -- n ∈ I ∪ {0} → n = 0 ∨ 0 < n
    have hn' := lt_or_eq_of_le hn_gt_0  -- 0 ≤ n → 0 < n ∨ 0 = n
    simpa [or_comm, eq_comm] using hn'  -- rearrange to match the goal
  ·         -- Show I ∪ {0} ⊆ ⋃ B_x
    intro n hn
    simp only [mem_iUnion]
    simp only [union_singleton, mem_insert_iff, mem_setOf_eq] at hn
    -- If n = 0 or 0 < n, show ∃ i, n ∈ B i
    -- First some mechanical stuff to prove that n + 1 > 0
    have hn0 : 0 ≤ n := by
      rcases hn with rfl | hpos
      · exact le_rfl
      · exact le_of_lt hpos
    -- Now let i = n + 1
    let i : I := ⟨n + 1, add_pos_of_nonneg_of_pos hn0 zero_lt_one⟩
    refine ⟨i, ?_⟩
    -- Prove than n ∈ B i
    constructor   -- B i = [0, i] = [0, n + 1]
    · exact hn0   -- 0 ≤ n
    · linarith    -- n ≤ n + 1
end

end Ch1_4
