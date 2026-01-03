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

section
-- Exercise 2: Let A = {a₁, a₂} and B = {b₁,b₂} be two sets, each having
-- precisely two distinct elements. Let f : A → B be the constant function such
-- that f(a) = b₁ for each a ∈ A.
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
variable (a1 a2 : A) (b1 b2 : B)

def Aset : Set A := {a1, a2}
def Bset : Set B := {b1, b2}

-- a) Prove that f⁻¹(f({a₁})) ≠ {a₁}
theorem ex2a
    (hAne : a1 ≠ a2)
    (hAeq : Aset a1 a2 = (Set.univ : Set A))
    (f : A → B)
    (h_const : ∀ a : A, f a = b1) :
    f ⁻¹' (f '' ({a1} : Set A)) ≠ ({a1} : Set A) := by
  -- First, Rewrite f '' {a₁} as f(a₁)
  simp only [image_singleton, ne_eq]
  -- f(a₁) = b₁ by definition
  have himage : f a1 = b1 := h_const a1
  rw [himage]
  -- Show that f⁻¹({b1}) ≠ {a1}
  have hpreimage : f ⁻¹' {b1} = {a1, a2} := by
    ext x
    simp only [mem_preimage, h_const, mem_singleton_iff, mem_insert_iff, true_iff]
    change x ∈ Aset a1 a2
    simp [hAeq]
  -- f⁻¹({b1}) = {a1, a2}, so goal is now to show that {a1, a2} ≠ {a1}
  rw [hpreimage]
  -- First, assume {a1, a2} = {a1}
  intro h
  -- This equality a2 ∈ {a1}, since a2 ∈ {a1, a2}
  have : a2 ∈ ({a1, a2} : Set A) := by simp
  have : a2 ∈ ({a1} : Set A) := by simpa [h] using this
  -- That would mean a2 = a1
  have : a2 = a1 := by simpa using this
  -- But it is not since a1 and a2 are defined to be distinct
  exact hAne this.symm

-- (b) Prove that f(f⁻¹(B)) ≠ B
theorem ex2b 
    (a1 a2 : A) (b1 b2 : B)
    (hAne : a1 ≠ a2) (hBne : b1 ≠ b2)
    (hAeq : Aset a1 a2 = (Set.univ : Set A))
    (hBeq : Bset b1 b2 = (Set.univ : Set B))
    (f : A → B)
    (h_const : ∀ a : A, f a = b1) : f '' (f ⁻¹' (Bset b1 b2)) ≠ (Bset b1 b2) := by
  -- First, the preimage of B is A ({a1 a2}) as before
  -- But the image f '' A is {b1}, which != B
  sorry

-- (c) Prove that f({a₁} ∩ {a₂}) ≠ f({a₁}) ∩ f({a₂})
theorem ex2c :
  f '' (({a1} : Set A) ∩ ({a2} : Set A)) ≠ (f '' ({a1} : Set A)) ∩ (f '' ({a2} : Set A)) := by
  sorry

end

-- Exercise 3: TODO
-- Exercise 4: TODO
-- Exercise 5: TODO
-- Exercise 6: TODO
-- Exercise 7: TODO
-- Exercise 8: TODO

end Ch1_6
