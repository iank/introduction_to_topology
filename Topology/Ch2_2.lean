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
-- Let X be the set of all continuous functions f:[a, b] → ℝ.
-- For f, g ∈ X, define d(f, g) = ∫_a^b |f(t) - g(t)| dt.
-- Prove that (X, d) is a metric space.

noncomputable def d_int (a b : ℝ) (hab : a < b) :
    C(Set.Icc a b, ℝ) → C(Set.Icc a b, ℝ) → ℝ :=
  fun f g => ∫ x in Set.Icc a b, ‖Set.IccExtend hab.le f x - Set.IccExtend hab.le g x‖

theorem ex4a {a b : ℝ} (hab : a < b) : IsMetric (d_int a b hab) where
  nonneg := by
    intro f g
    unfold d_int
    apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
    intro x _
    positivity
  eq_zero_iff := by
    intro f g
    constructor
    · intro h
      unfold d_int at h
      -- integrad is nonnegative
      have hf : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)]
          fun x => ‖Set.IccExtend hab.le f x - Set.IccExtend hab.le g x‖ :=
        Filter.Eventually.of_forall (fun x => norm_nonneg _)
      -- integrand is integrable
      have hfi : MeasureTheory.IntegrableOn
          (fun x => ‖Set.IccExtend hab.le f x - Set.IccExtend hab.le g x‖)
          (Set.Icc a b) MeasureTheory.volume := by
        apply Continuous.integrableOn_Icc
        exact ((Continuous.Icc_extend' f.continuous).sub
               (Continuous.Icc_extend' g.continuous)).norm
      -- integral of nonneg function = 0 → function is ae zero
      have h_ae : (fun x => ‖Set.IccExtend hab.le f x - Set.IccExtend hab.le g x‖)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)] 0 :=
        (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae hf hfi).mp h
      -- |f - g| ae 0 implies f ae g
      have h_ae_fg : Set.IccExtend hab.le f
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)] Set.IccExtend hab.le g := by
        refine h_ae.mono ?_
        intro x hx
        exact sub_eq_zero.mp (norm_eq_zero.mp hx)
      -- continuous functions that are ae equal on Icc are equal everywhere on Icc
      have h_eqOn : Set.EqOn (Set.IccExtend hab.le f) (Set.IccExtend hab.le g) (Set.Icc a b) :=
        MeasureTheory.Measure.eqOn_Icc_of_ae_eq (μ := MeasureTheory.volume) (ne_of_lt hab) h_ae_fg
          (Continuous.Icc_extend' f.continuous).continuousOn
          (Continuous.Icc_extend' g.continuous).continuousOn
      ext ⟨x, hx⟩
      have := h_eqOn hx
      simp only [Set.IccExtend_of_mem _ _ hx] at this
      exact this
    · intro h
      subst h
      simp [d_int]
  symm := by
    intro f g
    unfold d_int
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro x hx
    simp only [Real.norm_eq_abs]
    exact abs_sub_comm (Set.IccExtend (LT.lt.le hab) (⇑f) x) (Set.IccExtend (LT.lt.le hab) (⇑g) x)
  triangle := by
    intro f g h
    unfold d_int
    simp only [Real.norm_eq_abs]
    -- Abbreviations for the extended functions and their continuity
    let F := Set.IccExtend hab.le (⇑f)
    let G := Set.IccExtend hab.le (⇑g)
    let H := Set.IccExtend hab.le (⇑h)
    have hF : Continuous F := Continuous.Icc_extend' f.continuous
    have hG : Continuous G := Continuous.Icc_extend' g.continuous
    have hH : Continuous H := Continuous.Icc_extend' h.continuous
    -- Convenience: continuity of |F - G|, |G - H|
    have hcont_fg : Continuous fun x => |F x - G x| := (hF.sub hG).abs
    have hcont_gh : Continuous fun x => |G x - H x| := (hG.sub hH).abs
    -- Integrability of |(F-G)+(G-H)| on [a,b]
    have hcont_fgh : MeasureTheory.IntegrableOn
        (fun x => |(F x - G x) + (G x - H x)|) (Set.Icc a b) MeasureTheory.volume := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact ((hF.sub hG).add (hG.sub hH)).abs.continuousOn
    -- ∫|F-H| = ∫|(F-G)+(G-H)| ≤ ∫(|F-G|+|G-H|) = ∫|F-G| + ∫|G-H|
    calc ∫ (x : ℝ) in Set.Icc a b, |F x - H x|
        = ∫ (x : ℝ) in Set.Icc a b, |(F x - G x) + (G x - H x)| := by
            congr; ext; ring_nf
        _ ≤ ∫ (x : ℝ) in Set.Icc a b, (|F x - G x| + |G x - H x|) := by
            apply MeasureTheory.setIntegral_mono_on
            · exact hcont_fgh
            · exact (hcont_fg.add hcont_gh).integrableOn_Icc
            · exact measurableSet_Icc
            · intro x _; exact abs_add_le _ _
        _ = (∫ (x : ℝ) in Set.Icc a b, |F x - G x|) +
             ∫ (x : ℝ) in Set.Icc a b, |G x - H x| := by
            rw [MeasureTheory.integral_add]
            · exact hcont_fg.integrableOn_Icc
            · exact hcont_gh.integrableOn_Icc

end ex4

namespace ex5
-- Let X' be the set of all bounded functions f:[a, b] → ℝ.
-- For f, g ∈ X', define d'(f, g) = sup {|f(x) - g(x)| : x ∈ [a, b]}.
-- Prove that (X', d') is a metric space.

-- A bounded function on [a, b]
@[ext]
structure BoundedFun (a b : ℝ) (hab : a ≤ b) where
  toFun : Set.Icc a b → ℝ
  bound : ∃ K : ℝ, ∀ x, |toFun x| ≤ K

instance (a b : ℝ) (hab : a ≤ b) : CoeFun (BoundedFun a b hab) (fun _ => Set.Icc a b → ℝ) :=
  ⟨BoundedFun.toFun⟩

-- The sup metric on bounded functions
noncomputable def d' (a b : ℝ) (hab : a ≤ b) :
    BoundedFun a b hab → BoundedFun a b hab → ℝ :=
  fun f g => ⨆ x : Set.Icc a b, |f x - g x|

-- Helper: |f x - g x| is bounded above
lemma bddAbove_abs_sub (hab : a ≤ b) (f g : BoundedFun a b hab) :
    BddAbove (Set.range (fun x => |f x - g x|)) := by
  unfold BoundedFun.toFun
  obtain ⟨K₁, hK₁⟩ := f.bound
  obtain ⟨K₂, hK₂⟩ := g.bound
  use K₁ + K₂
  rintro _ ⟨x, rfl⟩
  calc |f.1 x - g.1 x| ≤ |f.1 x| + |g.1 x| := abs_sub _ _
    _ ≤ K₁ + K₂ := add_le_add (hK₁ x) (hK₂ x)

theorem ex5a {a b : ℝ} (hab : a ≤ b) : IsMetric (d' a b hab) where
  nonneg := by
    intro x y
    -- Supremum of nonnegative function is nonnegative
    exact Real.iSup_nonneg (fun i => abs_nonneg _)
  eq_zero_iff := by
    intro x y
    unfold d'
    constructor
    · -- Forward case: ⊔ |x - y| = 0 → x = y
      intro h
      -- ⊔ = 0 → ⊔ ≤ 0
      have hsup_nonpos : ⨆ i, |x.toFun i - y.toFun i| ≤ 0 := by
        exact ge_of_eq (id (Eq.symm h))
      -- since ⊔ d' ≤ 0 and d' is nonnegative, d' is 0 everywhere
      have hd_zero : ∀ i, x.toFun i - y.toFun i = 0 := by
        intro i
        have hi := le_trans (le_ciSup (bddAbove_abs_sub hab x y) i) hsup_nonpos
        exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
      -- x - y = 0 everywhere → x = y everywhere.
      ext i
      exact sub_eq_zero.mp (hd_zero i)
    · -- Reverse case: x = y → ⊔ |x - y| = 0
      intro h
      subst h
      -- ie, show ⊔ |x - x| = 0
      simp only [sub_self, abs_zero]
      -- ie, show ⊔ 0 = 0
      exact Real.iSup_const_zero
  symm := by
    intro x y
    unfold d'
    refine iSup_congr ?_
    intro i
    exact abs_sub_comm (x.toFun i) (y.toFun i)
  triangle := by
    intro x y z
    unfold d'
    unfold BoundedFun.toFun
    haveI : Nonempty (Set.Icc a b) := ⟨⟨a, le_refl a, hab⟩⟩
    have hxy_bd := bddAbove_abs_sub hab x y
    have hyz_bd := bddAbove_abs_sub hab y z
    calc ⨆ t, |x.1 t - z.1 t| ≤ ⨆ t, (|x.1 t - y.1 t| + |y.1 t - z.1 t|) := by
          apply ciSup_mono
          · exact BddAbove.range_add hxy_bd hyz_bd
          · exact fun t ↦ abs_sub_le (x.toFun t) (y.toFun t) (z.toFun t)
        _ ≤ (⨆ t, |x.1 t - y.1 t|) + ⨆ t, |y.1 t - z.1 t| := by
          apply ciSup_le
          intro t
          exact add_le_add (le_ciSup hxy_bd t) (le_ciSup hyz_bd t)

end ex5

namespace ex6
-- TODO
end ex6

namespace ex7
-- Let X be a set. For x, y ∈ X define the function d by:
--     d(x, x) = 0
-- and
--     d(x, y) = 1
-- if x ≠ y. Prove that (X, d) is a metric space.

variable (X : Type*) [DecidableEq X]

noncomputable def d (x y : X) : ℝ := if x = y then 0 else 1

theorem ex7a : IsMetric (d (X := X)) where
  nonneg := by
    intro x y
    unfold d
    positivity
  eq_zero_iff := by
    intro x y
    unfold d
    simp only [ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not]
  symm := by
    intro x y
    unfold d
    refine ite_cond_congr ?_
    simp only [eq_iff_iff]
    exact eq_comm
  triangle := by
    intro x y z
    unfold d
    -- Either LHS is 0 (simple) or LHS is 1 (simple after we work through some cases)
    by_cases hlhs : x = z
    · simp only [hlhs]
      positivity
    · simp only [hlhs]
      by_cases hrhs : y = z
      · simp only [↓reduceIte, hrhs, hlhs, add_zero, le_refl]
      · simp only [↓reduceIte, hrhs, le_add_iff_nonneg_left]
        positivity
end ex7

namespace ex8
-- TODO
end ex8

end Ch2_2
