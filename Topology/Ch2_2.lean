import Mathlib

namespace Ch2_2

-- Section 2, Metric spaces
structure IsMetric {X : Type*} (d : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  eq_zero_iff : ∀ x y, d x y = 0 ↔ x = y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

namespace ex1
-- Let (X, d) be a metric space. Let k be a positive real number and set dₖ(x, y) = k·d(x, y).
-- Prove that (X, dₖ) is a metric space.
theorem ex1a {X : Type*} (k : NNReal) (hk : 0 < k) (d : X → X → ℝ) (hd : IsMetric d) :
    IsMetric (fun x y => k * d x y) where
  nonneg := by
    intro x y
    exact mul_nonneg k.coe_nonneg (hd.nonneg x y)
  eq_zero_iff := by
    intro x y
    rw [mul_eq_zero]
    simp only [NNReal.coe_eq_zero]
    rw [or_iff_right (ne_of_gt hk)]
    exact hd.eq_zero_iff x y
  symm := by
    intro x y
    simp only [mul_eq_mul_left_iff, NNReal.coe_eq_zero]
    rw [or_iff_left (ne_of_gt hk)]
    exact hd.symm x y
  triangle := by
    intro x y z
    rw [← mul_add]
    rw [← NNReal.coe_pos] at hk
    rw [mul_le_mul_iff_of_pos_left hk]
    exact hd.triangle x y z
end ex1

namespace ex2
-- a) Prove that (ℝⁿ, d'') is a metric space, where the function d'' is defined by the
--     correspondence d''(x, y) = Σ|xᵢ - yᵢ|, for x = (x₁, x₂, ..., xₙ) and
--     y = (y₁, y₂, ..., yₙ) ∈ ℝⁿ.

def Rn (n : ℕ+) := Fin n → ℝ

def d'' (n : ℕ+) : Rn n → Rn n → ℝ :=
  fun x y => ∑ i, |x i - y i|

theorem ex2a {n : ℕ+} : IsMetric (d'' n) where
  nonneg := by
    simp only [d'']
    intro x y
    refine Fintype.sum_nonneg ?_
    intro i
    simp only [Pi.zero_apply, abs_nonneg]
  eq_zero_iff := by
    simp only [d'']
    intro x y
    rw [Fintype.sum_eq_zero_iff_of_nonneg ?f_nonneg]
    · rw [funext_iff]
      simp only [Pi.zero_apply, abs_eq_zero]
      constructor
      · intro h
        funext i
        have hi := h i
        rw [sub_eq_zero] at hi
        exact hi
      · intro heq i
        exact sub_eq_zero_of_eq (congrFun heq i)
    · intro i
      simp only [Pi.zero_apply, abs_nonneg]
  symm := by
    simp only [d'']
    intro x y
    rw [Fintype.sum_congr]
    intro i
    exact abs_sub_comm (x i) (y i)
  triangle := by
    simp only [d'']
    intro x y z
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact abs_sub_le (x i) (y i) (z i)

-- b) In (ℝ², d'') determine the shape and position of the set of points x such that d''(x, a) ≤ 1
-- for a point a ∈ ℝ².

-- Answer: It's a 45-degree rotated square centered on a. Maybe this is a
-- failure of imagination but I think any theorem formalizing this would just
-- end up being a trivially true restatement of the function d''.
end ex2

namespace ex3
-- Exercise 3:
def Rn (n : ℕ+) := Fin n → ℝ

-- Let d be the distance function defined on ℝⁿ by using Theorem 2.3
-- d(x, y) = max i ∈ Fin n, |x i - y i|
def d (n : ℕ+) : Rn n → Rn n → ℝ :=
  fun x y => Finset.sup' Finset.univ (Finset.univ_nonempty) (fun i => |x i - y i|)

-- Let d' be the Euclidean distance function
noncomputable
def d' (n : ℕ+) : Rn n → Rn n → ℝ :=
  fun x y => √(∑ i, (x i - y i)^2)

-- And let d'' be the distance function defined in Problem 2 above.
def d'' (n : ℕ+) : Rn n → Rn n → ℝ :=
  fun x y => ∑ i, |x i - y i|

-- Prove that for each pair of points x, y ∈ ℝⁿ,
-- a) d(x, y) ≤ d'(x, y)  ≤ √n · d(x, y)
theorem ex3a_i {n : ℕ+} (x y : Rn n) : d n x y ≤ d' n x y := by
  -- Show that the maximum abs difference (index j) is ≤ the euclidean distance
  -- by using that term in the euclidean distance sum as a lower bound for the whole sum.
  unfold d d'
  -- Let j = argmax i |x_i - y_i|, we can replace d(x, y) with |x_j - y_j|.
  apply Finset.sup'_le
  intro j hj
  rw [← Real.sqrt_sq_eq_abs] -- Get rid of the abs since sqrt(x^2) = |x|
  apply Real.sqrt_le_sqrt    -- Get rid of the √s
  -- Since the function being summed is nonnegative, any single instance of the function
  -- in the sum is a lower bound on the sum.
  apply Finset.single_le_sum (f := fun i => (x i - y i) ^ 2)
  · intro i hi
    exact sq_nonneg (x i - y i)
  · exact hj

theorem ex3a_ii {n : ℕ+} (x y : Rn n) : d' n x y ≤ √n * d n x y := by
  -- Rewrite so the LHS is just a sum
  rw [show d n x y = √((d n x y)^2) from (Real.sqrt_sq (?d_nonneg)).symm]
  · rw [← Real.sqrt_mul ?n_nonneg]
    · unfold d'
      apply Real.sqrt_le_sqrt
      -- goal now: ∑ i, (x i - y i) ^ 2 ≤ ↑↑n * d n x y ^ 2
      -- But since d(x, y)^2 is equal to max j, |x j - y j|^2, and there are n terms in the sum,
      -- the sum is at most n * d(x, y)^2.
      convert Finset.sum_le_card_nsmul Finset.univ (fun i => (x i - y i)^2) (d n x y ^ 2) ?term_max
      · -- proof about the size of the sum w/r/t n
        ext x
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      · -- show that (x j - y j)^2 ≤ (max |x i - y i|)^2 for all j.
        intro j
        simp only [Finset.mem_univ, forall_const, d]
        rw [← sq_abs]
        gcongr
        · exact Finset.le_sup' (fun i => |x i - y i|) (Finset.mem_univ j)
    · -- n is nonnegative
      positivity
  · -- d is nonnegative
    unfold d
    simp only [Finset.le_sup'_iff, Finset.mem_univ, abs_nonneg, and_self, exists_const]

-- b) d(x, y) ≤ d''(x, y) ≤ n · d(x, y)

theorem ex3b_i {n : ℕ+} (x y : Rn n) : d n x y ≤ d'' n x y := by
  -- Trivial, max i, |x i - y i| < sum i, |x i - y i|
  unfold d d''
  simp only [Finset.sup'_le_iff, Finset.mem_univ, forall_const]
  intro j
  apply Finset.single_le_sum (f := fun i => |x i - y i|)
  · intro i hi
    exact abs_nonneg _
  · exact Finset.mem_univ j

theorem ex3b_ii {n : ℕ+} (x y : Rn n) : d'' n x y ≤ n * d n x y := by
  -- Similar reasoning to ex3a_ii, n*max >= n*(sum of n terms less than or equal to max)
  unfold d''
  convert Finset.sum_le_card_nsmul Finset.univ (fun i => |x i - y i|) (d n x y) ?term_max
  · ext x
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro j hj
    simp only [d, Finset.le_sup'_iff, Finset.mem_univ, true_and]
    use j

end ex3

namespace ex4
-- TODO
end ex4

namespace ex5
-- TODO
end ex5

namespace ex6
-- TODO
end ex6

namespace ex7
-- TODO
end ex7

namespace ex8
-- TODO
end ex8

end Ch2_2
