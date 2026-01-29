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
    sorry
  symm := by
    sorry
  triangle := by
    sorry

-- b) In (ℝ², d'') determine the shape and position of the set of points x such that d''(x, a) ≤ 1
-- for a point a ∈ ℝ².
-- TODO
end ex2

namespace ex3
-- TODO
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
