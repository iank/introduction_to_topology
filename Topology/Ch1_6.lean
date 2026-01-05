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
  -- This equality says a2 ∈ {a1}, since a2 ∈ {a1, a2}
  have : a2 ∈ ({a1, a2} : Set A) := by simp
  have : a2 ∈ ({a1} : Set A) := by simpa [h] using this
  -- That would mean a2 = a1
  have : a2 = a1 := by simpa using this
  -- But it is not since a1 and a2 are defined to be distinct
  exact hAne this.symm

-- (b) Prove that f(f⁻¹(B)) ≠ B
theorem ex2b 
    (a1 a2 : A) (b1 b2 : B)
    (hBne : b1 ≠ b2)
    (hAeq : Aset a1 a2 = (Set.univ : Set A))
    (f : A → B)
    (h_const : ∀ a : A, f a = b1) : f '' (f ⁻¹' ({b1, b2} : Set B)) ≠ ({b1, b2} : Set B) := by
  -- First, the preimage of B is A ({a1 a2}) as before
  have hpreimage : f ⁻¹' {b1, b2} = {a1, a2} := by
    ext x
    simp only [mem_preimage, h_const, mem_insert_iff, mem_singleton_iff, true_or, true_iff]
    change x ∈ Aset a1 a2
    simp [hAeq]
  rw [hpreimage]
  -- But the image f '' A is {b1}, which != B
  have himage : f '' {a1, a2} = {b1} := by
    ext y
    simp [h_const]
  rw [himage]
  -- Now show {b1} ≠ {b1, b2} as in ex2a
  intro h
  -- This equality says b2 ∈ {b1}, since b2 ∈ {b1, b2}
  have : b2 ∈ ({b1} : Set B) := by simp [h]
  -- That would mean b2 = b1
  have : b2 = b1 := by simpa using this
  -- But it is not since b1 and b2 are defined to be distinct
  exact hBne this.symm

-- (c) Prove that f({a₁} ∩ {a₂}) ≠ f({a₁}) ∩ f({a₂})
theorem ex2c
    (a1 a2 : A) (b1 : B)
    (hAne : a1 ≠ a2)
    (f : A → B)
    (h_const : ∀ a : A, f a = b1) :
    f '' (({a1} ∩ {a2}: Set A)) ≠ (f '' ({a1} : Set A)) ∩ (f '' ({a2} : Set A)) := by
      intro hx
      have hfa1 : f '' {a1} = {b1} := by
        ext y
        simp [h_const]
      have hfa2 : f '' {a2} = {b1} := by
        ext y
        simp [h_const]
      have haInter : ({a1} ∩ {a2} : Set A) = ∅ := by
        ext x
        constructor
        · intro hxa
          rcases hxa with ⟨hxa1, hxa2⟩
          have : a1 = a2 := by
            have hxa1' : x = a1 := by simpa using hxa1
            have hxa2' : x = a2 := by simpa using hxa2
            rw [← hxa1']
            rw [← hxa2']
          exact (hAne this).elim
        · intro hxa
          cases hxa
      rw [hfa1] at hx
      rw [hfa2] at hx
      rw [haInter] at hx
      simp at hx
end

section
-- Exercise 3: Let f : A → B be given and let {X_a}, a∈I be an indexed family
-- of subsets of A. Prove:
variable {A B I : Type}
variable {X : I → Set A}
-- a) f(⋃ X α) = ⋃ f(X α).
theorem ex3a (f : A → B) : f '' (⋃ α, X α) = ⋃ α, f '' X α := by
  ext y
  constructor
  · -- y ∈ f(⋃ X α), prove y ∈ ⋃ f(X α)
    simp only [mem_image, mem_iUnion, forall_exists_index, and_imp]
    intro x i hxXi hfxy
    use i
    use x
  · -- y ∈ ⋃ f(X α), prove y ∈ f(⋃ X α)
    simp only [mem_iUnion, mem_image, forall_exists_index, and_imp]
    intro i x hxXi hfxy
    use x
    constructor
    · use i
    · exact hfxy

-- b) f(⋂ X α) ⊆ ⋂ f(X α).
theorem ex3b (f : A → B) : f '' (⋂ α, X α) ⊆ ⋂ α, f '' X α := by
  simp only [subset_iInter_iff, image_subset_iff]
  intro i x hx
  simp only [mem_preimage, mem_image]
  use x
  constructor
  · simp only [mem_iInter] at hx
    specialize hx i
    exact hx
  · rfl

-- c) If f: A → B is one-one, then f(⋂ X α) = ⋂ f(X α)
-- The problem doesn't state I is non-empty but I think we have to assume it.
theorem ex3c (f : A → B) (hf : Function.Injective f) (hI : Nonempty I) : f '' (⋂ α, X α) = ⋂ α, f '' X α := by
  ext y
  constructor
  · simp only [mem_image, mem_iInter, forall_exists_index, and_imp]
    intro x hx hfxy i
    use x
    constructor
    · specialize hx i
      exact hx
    · exact hfxy
  · intro hy
    simp only [mem_image, mem_iInter]
    simp only [mem_iInter, mem_image] at hy
    have ⟨i0⟩ := hI
    have hi0 := hy i0
    rcases hi0 with ⟨x0, hxi0, hfx0y⟩
    use x0
    constructor
    · intro i
      have hi := hy i
      -- f x0 = y, but also f x = y, and by injectivity x = x0
      rcases hi with ⟨xi, hxi, hfxy⟩
      have : x0 = xi := by
        rw [← hfxy] at hfx0y
        apply hf hfx0y
      rw [this]
      exact hxi
    · exact hfx0y
end

section
-- Exercise 4: Let f : A → B be given and let {Y_a}, a∈I be an indexed family
-- of subsets of B. Prove:
variable {A B I : Type}
variable {Y : I → Set B}

-- a) f⁻¹(⋃ Y_a) = ⋃ f⁻¹(Y_a)
theorem ex4a (f : A → B) : f ⁻¹' (⋃ α, Y α) = ⋃ α, f ⁻¹' Y α := by
  -- `simp only [preimage_iUnion]` is sufficient here but that's the theorem we're
  -- proving so I won't use it
  ext x
  constructor <;>   -- Comments below are for the forward case but the reverse is similar.
  · -- Show x ∈ f ⁻¹' ⋃ α, Y α → x ∈ ⋃ α, f ⁻¹' Y α
    simp only [mem_iUnion]
    -- ie, show x ∈ f ⁻¹' ⋃ α, Y α → ∃ i, x ∈ f ⁻¹' Y i
    simp only [mem_preimage]
    -- ie, show f x ∈ ⋃ α, Y α → ∃ i, f x ∈ Y i
    simp only [mem_iUnion]
    -- ie, show (∃ i, f x ∈ Y i) → ∃ i, f x ∈ Y i
    intro hi
    exact hi

-- b) f⁻¹(⋂ Y_a) = ⋂ f⁻¹(Y_a)
theorem ex4b (f : A → B) : f ⁻¹' (⋂ α, Y α) = ⋂ α, f ⁻¹' Y α := by
  -- Similary to ex4a using iUnion, preimage, and imp_self.
  ext x
  constructor <;> simp

-- c) If X is a subset of B then f⁻¹(C(X)) = C(f⁻¹(X)).
-- TODO
-- d) If X is a subset of A, and Y is a subset of B, then f(X ∩ f⁻¹(Y)) = f(X) ∩ Y.
-- TODO
end

-- Exercise 5: TODO
-- Exercise 6: TODO
-- Exercise 7: TODO
-- Exercise 8: TODO

end Ch1_6
