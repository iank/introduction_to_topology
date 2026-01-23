import Mathlib

namespace Ch1_9

-- Section 9, Inverse functions, extensions, and restrictions

namespace ex1
-- TODO
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
-- Exercise 3

-- Let A ⊆ B ⊆ X. Let f: A → Y, g: B → Y, and F: X → Y. Prove that if g is an
-- extension of f to B and F is an extension of g to X, then F is an extension
-- of f to X.
variable {X Y : Type*}
theorem extension_trans' {A B : Set X} (hAB : A ⊆ B)
    (f : A → Y) (g : B → Y) (F : X → Y)
    (hfg : ∀ a : A, f a = g ⟨a.val, hAB a.property⟩)
    (hgF : ∀ b : B, g b = F b) :
    ∀ x : A, f x = F x := by
  intro x
  specialize hfg x
  specialize hgF ⟨x.val, hAB x.property⟩
  rw [hfg]
  rw [hgF]
end ex3

namespace ex4
-- Exercise 4
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

-- Let m, n be positive integers. Let X be a set with m distinct elements and Y
-- a set with n distinct elements.

-- a) How many distinct functions are there from X to Y?
theorem num_functions (hX : Fintype.card X = m) (hY : Fintype.card Y = n) :
    Fintype.card (X → Y) = n ^ m := by
  rw [← hX]
  rw [← hY]
  -- Proved something like this explicitly in Ch1.6, ex3 so I'm comfortable just
  -- using Fintype.card_fun here.
  exact Fintype.card_fun (α := X) (β := Y)

-- b) Let A be a subset of X with r distinct elements, 0 ≤ r < m, and
-- f: A → Y. How many distinct extensions of f to X are there?
theorem num_extensions {A : Set X} [DecidablePred (· ∈ A)] [Fintype A]
    (f : A → Y)
--  (hr : r < m)
    (hA : Fintype.card A = r)
    (hX : Fintype.card X = m)
    (hY : Fintype.card Y = n) :
    Fintype.card { F : X → Y // ∀ a : A, F a = f a } = n ^ (m - r) := by
  -- f is given, so I think the number of distinct extensions should be defined
  -- by the number of distinct inclusion mappings. The inclusion mappings can
  -- differ only in X \ A, the cardinality of which is (m - r)
  have hXcompl := Fintype.card_compl_set A
  rw [hA] at hXcompl
  rw [hX] at hXcompl
  -- So the cardinality of the Aᶜ → Y is n ^ (m - r)
  have hXcomplY := Fintype.card_fun (α := ↑Aᶜ) (β := Y)
  rw [hXcompl] at hXcomplY
  rw [hY] at hXcomplY
  -- Establish the equivalence between the set of extensions F and Aᶜ → Y
  let e : { F : X → Y // ∀ a : A, F a = f a } ≃ (↑Aᶜ → Y) := {
    toFun := fun ⟨F, hF⟩ => fun x => F x
    invFun := fun g => ⟨fun x => if h : x ∈ A then f ⟨x, h⟩ else g ⟨x, h⟩, ?invFun_proof⟩
    left_inv := ?left_inv_proof
    right_inv := ?right_inv_proof
  }
  case invFun_proof =>
    -- Just need to show this satisfies the extension predicate, ie F a = f a
    -- Since the piecewise function we defined is f(a) when a ∈ A, this is trivial
    intro a
    simp [a.property]
  case left_inv_proof =>
    -- Show that invFun(toFun(x)) = x
    intro ⟨F, hF⟩
    simp only [Subtype.mk.injEq]
    funext x
    split_ifs with h
    case pos => exact (hF ⟨x, h⟩).symm
    case neg => rfl
  case right_inv_proof =>
    -- Show that toFun(invFun(x)) = x
    intro g
    funext x
    simp only [Subtype.coe_eta, dite_eq_right_iff]
    intro h
    exact absurd h x.property
  -- Use this equivalence to rewrite hXcomplY (our expression for the
  -- cardinality of Aᶜ → Y) in terms of the goal, ie the cardinality of the
  -- extensions F : X → Y
  have := Fintype.card_congr e
  rw [← this] at hXcomplY
  exact hXcomplY
end ex4

end Ch1_9
