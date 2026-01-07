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

end Ch1_7
