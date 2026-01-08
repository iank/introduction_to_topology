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

section ex3
/- Exercise 3

Let f : X → X be a one-one function of a set X into itself.
Define a sequence of functions f⁰, f¹, f², …, fⁿ, … : X → X
by letting f⁰ be the identity, f¹ = f, and inductively fⁿ(x) = f(fⁿ⁻¹(x)).

Prove that each of these functions is one-one.

Let R be the subset of X × X consisting of those pairs (a, b) such that
b = fᵏ(a) for some integer k or a = fʲ(b) for some integer j.

Prove that R is an equivalence relation. -/

-- TODO
end ex3

section ex4
/- Exercise 4

Let X be the set of functions from the real numbers into the real numbers
possessing continuous derivatives.

Let R be the subset of X × X consisting of those pairs (f, g) such that
Df = Dg where D maps a function into its derivative.

Prove that R is an equivalence relation and describe an equivalence set π(f). -/

-- TODO
end ex4

section ex5
/- Exercise 5

Let E be the set of all functions from a set X into a set Y.
Let b ∈ X and let R be the subset of E × E consisting of those pairs (f, g)
such that f(b) = g(b).

Prove that R is an equivalence relation.

Define a one-one onto function e_b : E/R → Y. -/
-- TODO
end ex5

end Ch1_7
