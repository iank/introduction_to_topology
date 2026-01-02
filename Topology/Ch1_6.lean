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

-- c) If f : A → B is one-one, then for each subset X ∈ A, f⁻¹(f(X)) = X
theorem ex1c (f : A → B) (X : Set A) (hf : Function.Injective f) : f ⁻¹' (f '' X) = X := by
  -- We could use simp [hf, preimage_image_eq] but that's cheating at this point...
  ext x
  constructor
  · -- Show x ∈ f⁻¹(f(X)) → x ∈ X
    suffices f x ∈ f '' X → x ∈ X by simpa [mem_preimage]
    suffices (∃ x' ∈ X, f x' = f x) → x ∈ X by simpa [mem_image]
    -- Since f is injective, if f x' = f x then x' = x
    intro hx
    rcases hx with ⟨x', hx'X, hfx'x⟩
    have : x' = x := hf hfx'x
    -- And x' ∈ X so x ∈ X
    rw [← this]
    exact hx'X
  · -- Show x ∈ X → x ∈ f⁻¹(f(X))
    -- This is simpler.
    intro hx
    use x

-- d) If f : A → B is onto, then for each subset Y ⊆ B, f(f⁻¹(Y)) = Y
theorem ex1d (f : A → B) (Y : Set B) (hf : Function.Surjective f) : f '' (f ⁻¹' Y) = Y := by
  -- Again, we could use simp [hf, image_preimage_eq]..
  ext y
  constructor
  · -- Show y ∈ f(f⁻¹(Y)) → y ∈ Y
    intro hy
    -- y ∈ f(f⁻¹(Y)) means ∃ x ∈ X s.t. f(x) ∈ Y and f(x) = y
    simp only [mem_image, mem_preimage] at hy
    rcases hy with ⟨x, hfxY, hfxy⟩
    -- f(x) = y and f(x) ∈ Y,
    rw [hfxy] at hfxY
    -- so y ∈ Y
    exact hfxY
  · -- Show y ∈ Y → y ∈ f(f⁻¹(Y))
    intro hy
    -- ie, ∃ x ∈ f ⁻¹' Y, f x = y
    -- ie, ∃ x, f x ∈ Y ∧ f x = y
    simp only [mem_image, mem_preimage]
    -- f is surjective so ∃ a, f a = y
    rcases hf y with ⟨a, hfay⟩
    -- let x = a, so f(a) = y
    use a
    rw [hfay]
    exact ⟨hy, rfl⟩
end

-- Exercise 2: TODO
-- Exercise 3: TODO
-- Exercise 4: TODO
-- Exercise 5: TODO
-- Exercise 6: TODO
-- Exercise 7: TODO
-- Exercise 8: TODO

end Ch1_6
