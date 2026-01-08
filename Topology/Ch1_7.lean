import Mathlib

namespace Ch1_7

-- Section 7, Relations
section ex1

/- Exercise 1
Let P be a subset of the real numbers ℝ such that
i) 1 ∈ P,
ii) if a, b ∈ P then a + b ∈ P, and
iii) for each x ∈ R, one and only one of the three statements,
     x ∈ P, x = 0, or −x ∈ P is true.
Define Q = { (a, b) | (a, b) ∈ ℝ × ℝ and a − b ∈ P }
Prove that Q is a transitive relation.
-/

def exactlyOne (a b c : Prop) : Prop :=
  (a ∧ ¬ b ∧ ¬ c) ∨
  (¬ a ∧ b ∧ ¬ c) ∨
  (¬ a ∧ ¬ b ∧ c)

variable (P : Set ℝ)

def Q (a b : ℝ) : Prop := a - b ∈ P

set_option linter.unusedVariables false
theorem ex1
  (h1 : (1 : ℝ) ∈ P)
  (h2 : ∀ {a b : ℝ}, a ∈ P → b ∈ P → a + b ∈ P)
  (h3 : ∀ x : ℝ, exactlyOne (x ∈ P) (x = 0) (-x ∈ P))
: Transitive (Q P) := by
  intro a b c       -- Arbitrary a, b, c
  simp only [Q]     -- Rewrite Q -> a - b ∈ P
  intro aQb bQc
  -- By h2, since a - b ∈ P and b - c ∈ P, a - b + b - c ∈ P, ie a - c ∈ P
  have habbc : (a - b) + (b - c) ∈ P := h2 aQb bQc
  simpa only [sub_add_sub_cancel] using habbc
set_option linter.unusedVariables true

end ex1

section ex2
-- Exercise 2
-- Let f : X → Y be a function from a set X onto a set Y.

variable {X Y : Type _}
variable (f : X → Y)

-- Let R be the subset of X × X consisting of those pairs (x, x') such that f(x) = f(x').
def R (x x' : X) : Prop := f x = f x'

-- Prove that R is an equivalence relation.
theorem ex2a : Equivalence (R f) := by
  -- Need to show R is reflexive, symmetric, and transitive
  constructor
  case refl =>
    -- xRx → f(x) = f(x), which is true for all x ∈ X
    intro x
    simp only [R]
  case symm =>
    intro x x'
    simp only [R]
    -- Show xRx' → x'Rx, ie f(x) = f(x') → f(x') = f(x)
    intro hfx
    simp only [hfx]
  case trans =>
    -- Show aRb, bRc → aRc
    intro a b c
    simp only [R]
    intro hab hbc
    rw [hbc] at hab
    exact hab

-- Let π : X → X/R be the projection.
def π : X → Quot (R f) := Quot.mk (R f)

--   Verify that if α ∈ X/R is an equivalence class,
--   to define F(α) = f(a) whenever α = π(a), establishes a well-defined function
--   F : X/R → Y which is one-one and onto.

def F : Quot (R f) → Y :=
  -- Define F(α) = f(a) and prove that it is well-defined
  Quot.lift f (by
    intro a b hab
    simpa [R] using hab)

-- Show F is one-one and onto
theorem ex2b (hf: Function.Surjective f) : Function.Injective (F f) ∧ Function.Surjective (F f) := by
  constructor
  · -- Show one-one
    intro α α' hα
    induction α using Quot.ind
    case mk a =>
      induction α' using Quot.ind
      case mk b =>
        apply Quot.sound
        simp [R]
        simpa [F] using hα
  · -- Show onto
    intro y       -- For an arbitrary y ∈ Y, we must show ∃ a, F(f(a)) = y
    obtain ⟨x, hx⟩ := hf y
    use Quot.mk (R f) x
    simp only [F]
    exact hx
end ex2


-- Exercise 3: TODO
-- Exercise 4: TODO
-- Exercise 5: TODO

end Ch1_7
