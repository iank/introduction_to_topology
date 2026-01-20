import Mathlib

namespace Ch1_9

-- Section 9, Inverse functions, extensions, and restrictions

namespace ex1
-- Exercise 1
-- Let A be the set of all functions f:[a, b] → ℝ that are continuous on [a, b]
variable (a b : ℝ)
def A : Type := { f : ℝ → ℝ // ContinuousOn f (Set.Icc a b) }

-- Let B be the subset of A consisting of all functions possessing a continuous
-- derivative on [a, b].
def B : Type := { f : A a b // DifferentiableOn ℝ f.val (Set.Icc a b) ∧
                  ContinuousOn (deriv f.val) (Set.Icc a b) }

-- Let C be the subset of B consisting of all functions whose value at a is 0.
def C : Type := { f : B a b // f.val.val a = 0 }

-- Let d: B → A be the correspondence that associates with each function in B its derivative.
noncomputable
def d (f : B a b) : A a b := ⟨deriv f.val.val, f.prop.2⟩

-- a) Is the function d: B → A invertible?
-- In general no, since functions differing by a constant will have the same derivative
-- We'll use two examples, f and g. Since B is a somewhat complicated subtype
-- it's useful to define them here

-- f(x) = x
def ex1a_f : B a b := ⟨
  ⟨fun x => x, continuousOn_id⟩,
  ⟨differentiableOn_id, by simp only [deriv_id'']; exact continuousOn_const⟩
⟩

-- g(x) = x + 1
def ex1a_g : B a b := ⟨
  ⟨fun x => x + 1, continuousOn_id.add continuousOn_const⟩,
  ⟨differentiableOn_id.add (differentiableOn_const (1 : ℝ)),
   by simp only [deriv_add_const', deriv_id'']; exact continuousOn_const⟩
⟩

theorem ex1a : ¬ Function.Bijective (d a b) := by
  by_contra hd
  obtain ⟨hinj, hsurj⟩ := hd
  -- It's enough to show d is not injective.
  -- First, show that f ≠ g
  have hne : ex1a_f a b ≠ ex1a_g a b := by
    intro h
    -- Show that f = g → f(0) = g(0) → 0 = 1 by unpacking the definition of f and g
    have : ((ex1a_f a b).val.val : ℝ → ℝ) = (ex1a_g a b).val.val := by rw [h]
    simp only [ex1a_f, ex1a_g] at this
    have : (0 : ℝ) = 0 + 1 := congrFun this 0
    simp at this
  -- Now show that d(f) = d(g)
  have heq : d a b (ex1a_f a b) = d a b (ex1a_g a b) := by
    simp [d, ex1a_f, ex1a_g]
  exact hne (hinj heq)

-- b)
-- To each f ∈ A, let h(f) be the function defined by
-- (h(f))(x) = integral from a to x: f(t)dt,
-- for each x ∈ [a, b].
noncomputable def h (f : A a b) : ℝ → ℝ :=
  fun x => ∫ t in a..x, f.val t

-- Verify that h: A → C.
-- ie, verify that h really maps to C by proving it is:
--   i) continuous on [a, b]
lemma h_continuousOn (hab : a ≤ b) (f : A a b) : ContinuousOn (h a b f) (Set.Icc a b) := by
  unfold h
  sorry

--   ii) differentiable on [a, b]
lemma h_differentiableOn (f : A a b) : DifferentiableOn ℝ (h a b f) (Set.Icc a b) := by
  sorry

--   iii) continuous derivative on [a, b]
lemma h_deriv_continuousOn (f : A a b) : ContinuousOn (deriv (h a b f)) (Set.Icc a b) := by
  sorry

--   iv) evaluates to 0 at a
lemma h_eval_a (f : A a b) : h a b f a = 0 := by
  simp [h]

noncomputable def h' (hab : a ≤ b) (f : A a b) : C a b :=
  ⟨⟨⟨h a b f, h_continuousOn a b hab f⟩, h_differentiableOn a b f, h_deriv_continuousOn a b f⟩, 
   h_eval_a a b f⟩

theorem ex1b (hab : a ≤ b) (f : A a b) : h' a b hab f ∈ Set.univ := by
  trivial

-- c) Find the function g: C → A such that these two functions are inverse functions.
noncomputable def g (f : C a b) : A a b :=
  sorry

theorem ex1c_right_inverse (hab : a ≤ b) (f : A a b) : g a b (h' a b hab f) = f := by
  sorry

theorem ex1c_left_inverse (hab : a ≤ b) (f : C a b) : h' a b hab (g a b f) = f := by
  sorry

end ex1

namespace ex2
-- Exercise 2
-- Let ℝ be the real numbers and ∞ an object not in ℝ. Define a set ℝ* = ℝ∪{∞}.

inductive RStar where
  | ofReal : ℝ → RStar
  | infinity : RStar

namespace RStar
-- Let a, b, c, d be real numbers. Let f : ℝ* → ℝ* be a function defined by
--   f(x) = (ax + b)/(cx + d) when x ≠ -d/c, ∞, while f(-d/c) = ∞ and f(∞) = a/c.
--   [In the event that c=0, f is linear and f(x) = (ax + b)/d when x ≠ ∞ and f(∞) = ∞]
noncomputable def f (a b c d : ℝ) : RStar → RStar
  | ofReal x => if c = 0 then
                  ofReal ((a * x + b) / d)
                else if x = -d / c then
                  infinity
                else
                  ofReal ((a * x + b) / (c * x + d))
  | infinity => if c = 0 then infinity else ofReal (a / c)

-- Prove that f has an inverse provided ad - bc ≠ 0.
-- x = (ay + b)/(cy + d)
-- cyx + dx = ay + b
-- dx - b = ay - cyx
-- dx - b = y(a - cx)
-- (dx - b)/(a - cx) = y
theorem f_has_inverse (a b c d : ℝ) (h : a * d - b * c ≠ 0) :
    ∃ g : RStar → RStar, Function.LeftInverse g (f a b c d) ∧ 
                          Function.RightInverse g (f a b c d) := by
    use f d (-b) (-c) a
    constructor
    · -- Left inverse: ∀ x, g(f(x)) = x
      intro x
      cases x with
      | ofReal r =>
        simp only [f]
        by_cases cz : c = 0
        case pos =>
          simp [cz]
          ring_nf
          -- by h and cz, a ≠ 0 and d ≠ 0
          simp [cz] at h
          field_simp [h]
          ring
        case neg =>
          simp only [cz, ↓reduceIte, neg_eq_zero, neg_div_neg_eq, neg_mul]
          by_cases hr : r = -d/c
          case pos =>
            simp [hr]
            field_simp
          case neg =>
            simp only [hr, ↓reduceIte]
            split_ifs with h'
            case pos =>
              -- c * r + d ≠ 0 (because r ≠ -d/c)
              have hdenom : c * r + d ≠ 0 := by
                intro hzero
                apply hr
                field_simp [cz]
                linarith
              -- (a * r + b) * c = a * (c * r + d)
              have hmul := (div_eq_div_iff hdenom (by exact cz)).1 h'
              -- have : b * c = a * d := by
              have : b * c = a * d := by
                ring_nf at hmul
                linarith
              have : a * d - b * c = 0 := by linarith
              -- exact h this
              exact h this
            case neg =>
              simp only [ofReal.injEq]
              have crd_ne : r * c + d ≠ 0 := by
                intro hzero
                apply hr
                field_simp [cz]
                linarith
              have denom_ne : -((a * r + b) * c) + a * (r * c + d) ≠ 0 := by
                ring_nf
                exact h
              field_simp [crd_ne, denom_ne]
              ring
      | infinity =>
        simp only [f]
        by_cases cz : c = 0 <;> simp [cz]
    · -- Right inverse: ∀ x, f(g(x)) = x
      intro x
      cases x with
      | ofReal r =>
        simp only [f]
        by_cases cz : c = 0
        case pos =>
          simp only [cz, neg_zero, ↓reduceIte, ofReal.injEq]
          simp [cz] at h
          field_simp [h]
          ring
        case neg =>
          simp only [neg_eq_zero, cz, ↓reduceIte, neg_div_neg_eq, neg_mul]
          split_ifs with hr
          case pos =>
            simp only [ofReal.injEq]
            exact hr.symm
          case neg =>
            simp only
            split_ifs with h'
            case pos =>
              -- -cr + a ≠ 0
              have hdenom : -(c * r) + a ≠ 0 := by
                intro hzero
                apply hr
                field_simp [cz]
                linarith
              -- so (dr - b) * c = dcr - a
              have hmul := (div_eq_div_iff hdenom (by exact cz)).1 h'
              -- dr - b = -da/c + dr
              -- so b = da/c, or da = bc
              have : b * c = a * d := by
                ring_nf at hmul
                linarith
              -- contradicts h
              have : a * d - b * c = 0 := by linarith
              exact h this
            case neg =>
              simp only [ofReal.injEq]
              have cra_ne : -(r * c) + a ≠ 0 := by
                intro hzero
                apply hr
                field_simp [cz]
                linarith
              field_simp [h, cra_ne]
              ring_nf
              field_simp [h]
      | infinity =>
        simp only [f]
        by_cases cz : c = 0 <;> simp [cz]
        field_simp

end RStar
end ex2

namespace ex3
-- TODO: exercise 3
end ex3

namespace ex4
-- TODO: exercise 4
end ex4

end Ch1_9
