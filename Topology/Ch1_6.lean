import Mathlib
open Set

namespace Ch1_6
-- Section 6, Functions

section
-- Exercise 1. Let f : A → B be given. Prove the following:
variable {A B : Type*}

-- a) For each subset X ⊆ A, X ⊆ f⁻¹(f(X))
-- (notation: f ⁻¹' is the preimage over a set, f '' is the image over a set)
theorem ex1a (f : A → B) (X : Set A) : X ⊆ f ⁻¹' (f '' X) := by
  intro x hx
  -- We're showing x ∈ f ⁻¹' (f '' X)
  -- Definition of preimage: x ∈ f ⁻¹' S means f(x) ∈ S
  -- So we can equivalently write: f(x) ∈ f '' X
  simp only [mem_preimage]
  -- Definition of image: y ∈ f '' S means ∃ s ∈ S s.t. f(x) = y
  -- So we can simplify our goal to:
  -- ∃ x1 ∈ X, f(x1) = f(x)
  simp only [mem_image]
  -- The obvious choice for x1 is x
  use x

-- b) For each subset Y ∈ B, Y ⊇ f(f⁻¹(Y))
theorem ex1b (f : A → B) (Y : Set B) : Y ⊇ f '' (f ⁻¹' Y) := by
  intro y hy
  -- Given hy: y ∈ f '' (f ⁻¹' Y)), show: y ∈ y
  -- Definition of image: y ∈ f '' S means ∃ s ∈ S s.t. f(s) = y
  -- ie, hy: ∃ x ∈ f ⁻¹' Y s.t. f(x) = y
  simp only [mem_image] at hy
  -- Definition of preimage: x ∈ f ⁻¹' S means f(x) ∈ S
  -- Rewrite hy: ∃ x, f(x) ∈ Y ∧ f x = y
  simp only [mem_preimage] at hy
  rcases hy with ⟨x, hfxY, hfxy⟩
  -- We have f(x) ∈ Y and f(x) = y, so y ∈ Y
  rewrite [hfxy] at hfxY
  exact hfxY

-- c) TODO
-- d) TODO
end

-- Exercise 2: TODO
-- Exercise 3: TODO
-- Exercise 4: TODO
-- Exercise 5: TODO
-- Exercise 6: TODO
-- Exercise 7: TODO
-- Exercise 8: TODO

end Ch1_6
