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
theorem ex4c (f : A → B) (X : Set B) : f ⁻¹' Xᶜ = (f ⁻¹' X)ᶜ := by
  -- Again, this is `preimage_compl` so `simp` could just handle this but we'll avoid it
  ext x
  constructor <;>
  -- Comments here for the forward case, reverse is similar.
  · -- Show x ∈ f ⁻¹' Xᶜ → x ∈ (f ⁻¹' X)ᶜ
    simp only [mem_preimage]
    -- ie, show f x ∈ Xᶜ → x ∈ (f ⁻¹' X)ᶜ
    simp only [mem_compl_iff]
    -- ie, show f x ∉ X → x ∉ f ⁻¹' X
    simp only [mem_preimage]
    -- ie, show f x ∉ X → f x ∉ X
    intro hx
    exact hx

-- d) If X is a subset of A, and Y is a subset of B, then f(X ∩ f⁻¹(Y)) = f(X) ∩ Y.
theorem ex4d (f : A → B) (X : Set A) (Y : Set B) : f '' (X ∩ f ⁻¹' Y) = f '' X ∩ Y := by
  ext y
  constructor
  · -- Show y ∈ f '' (X ∩ f ⁻¹' Y) → y ∈ f '' X ∩ Y
    simp only [mem_image]
    -- ie, show (∃ x ∈ X ∩ f ⁻¹' Y, f x = y) → y ∈ f '' X ∩ Y
    intro h
    rcases h with ⟨x, hx, hfx⟩        -- x, x ∈ X ∩ f⁻¹(Y), f(x) = y
    rcases hx with ⟨hxX, hxfY⟩        -- x ∈ X, x ∈ f⁻¹(Y)
    simp only [mem_preimage] at hxfY  -- Now we have f(x) = y, x ∈ X, f(x) ∈ Y
    -- And we must show y ∈ f(X) ∩ Y
    simp only [mem_inter_iff, mem_image]
    -- ie, (∃ x ∈ X, f x = y) ∧ y ∈ Y
    constructor
    · use x     -- We already have x ∈ X and f(x) = y
    · rw [hfx] at hxfY
      exact hxfY
  · -- Show y ∈ f '' X ∩ Y → y ∈ f '' (X ∩ f ⁻¹' Y)
    simp only [mem_image]
    -- ie, show y ∈ f '' X ∩ Y → ∃ x ∈ X ∩ f ⁻¹' Y, f x = y
    intro h
    rcases h with ⟨hyfX, hyY⟩
    simp only [mem_image] at hyfX
    -- ie, show y ∈ Y, ∃ x ∈ X, f(x) = y → ∃ x ∈ X ∩ f ⁻¹' Y, f x = y
    rcases hyfX with ⟨x, hxX, hfxy⟩   -- Unpack: x, x ∈ X, f(x) = y
    use x
    constructor
    · -- Show x ∈ X ∩ f⁻¹(Y)
      simp only [mem_inter_iff, mem_preimage]
      -- ie, show x ∈ X ∧ f(x) ∈ Y
      rw [← hfxy] at hyY  -- We know f(x) = y and f(x) ∈ Y so we know f(x) ∈ Y
      exact ⟨hxX, hyY⟩    -- And we know x ∈ X
    · -- Show f(x) = y
      exact hfxy
end

section
-- Exercise 5: Let A and B be sets.
variable {A B : Type*}

-- The correspondence that associates with
--   each element (a, b) ∈ A × B the element p₁(a, b) = a
--   is a function called the first projection.
def p1 : A × B → A := fun x => x.1

-- The correspondence that associates with
--   each element (a, b) ∈ A × B the element p₂(a, b) = b
--   is a function called the second projection.
def p2 : A × B → B := fun x => x.2

-- Prove that:
-- a) if B ≠ ∅, then p₁: A × B → A is onto
theorem ex5a (hB : Nonempty B) : Function.Surjective (p1 (A:=A) (B:=B)) := by
  -- Onto means ∀ a ∈ A, ∃ (a, b) s.t. p₁(a, b) = a
  intro a
  rcases hB with ⟨b⟩  -- B ≠ ∅ means ∃ b ∈ B
  use ⟨a, b⟩          -- So for any a we can construct an (a, b) that maps to a.
  rfl


-- b) if A ≠ ∅, then p₂: A × B → B is onto
theorem ex5b (hA : Nonempty A) : Function.Surjective (p2 (A:=A) (B:=B)) := by
  intro b
  rcases hA with ⟨a⟩
  use ⟨a, b⟩
  rfl

-- c) Under what circumstances in p₁ or p₂ one-one?
theorem ex5c (hA : Nonempty A): Function.Injective (p1 (A:=A) (B:=B)) ↔ Subsingleton B := by
  classical
  -- p₁ is Injective iff B has at most one distinct element
  constructor
  · intro hp  -- p₁ is one-one → B has at most one distinct element
    rw [subsingleton_iff] -- So, show that ∀ x y : B, x = y
    intro b1 b2
    by_contra h           -- Assume b1 ≠ b2
    obtain ⟨a⟩ := hA      -- For some a
    -- p₁(a, b1) = p₂(a, b2) by definition (both = a)
    have heq : p1 ⟨a, b1⟩ = p1 ⟨a, b2⟩ := by
      simp [p1]
    -- But injectivity means p₁(a, b1) = p₁(a, b2) → (a, b1) = (a, b2)
    have hbeq : (⟨a, b1⟩ : A × B) = ⟨a, b2⟩ := hp heq
    -- So b1 = b2
    have hb : b1 = b2 := congrArg Prod.snd hbeq
    -- Contradiction
    exact h hb
  · intro h   -- B has at most one element → p₁ is one-one
    rw [subsingleton_iff] at h   -- We know ∀ x y : B, x = y
    intro ⟨a1, b1⟩ ⟨a2, b2⟩ hp   -- We must show that p1(a1, b1) = p1(a2, b2) → (a1, b1) = (a2, b2)
    simp only [p1] at hp         -- This means a1 = a2 (by definition of p1)
    have hb : b1 = b2 := h b1 b2 -- But b1 = b2 also, because B has at most one distinct element
    cases hp                     -- So rewrite a2 -> a1
    cases hb                     -- And rewrite b2 -> b1
    rfl                          -- (a1, b1) = (a2, b2)

-- d) What is p₁⁻¹({a}) for an element a ∈ A?
theorem ex5d (a : A) : p1 ⁻¹' {a} = {ab : A × B | ab.1 = a} := by
  -- p₁¹({a}) = All the (x, y) ∈ A × B s.t. x = a
  ext ⟨x, y⟩
  constructor
  · intro ha          -- (x, y) ∈ p₁⁻¹({a})
    simp only [mem_preimage, p1, mem_singleton_iff] at ha   -- Therefore x = a
    simp only [mem_setOf_eq]
    exact ha
  · intro hab
    simp only [mem_setOf_eq] at hab
    simp only [mem_preimage, p1, mem_singleton_iff]
    exact hab
end

section
-- Exercise 6: Let A and B be sets, with B ≠ ∅.
variable {A B : Type*}
-- (Since the theorems below take a parameter b I implicitly have B ≠ ∅)

-- For each b ∈ B the correspondence that associates
-- with each element a ∈ A the element j_b(a) = (a, b) ∈ A × B is a function.
def j (b : B) : (a : A) → (A × B) := fun x => ⟨x, b⟩

-- a) Prove that for each b ∈ B, j_b : A → A × B is one-one.
theorem ex6a (b : B) : Function.Injective (j (b) (A:=A)) := by
  -- Prove that j_b(a1) = j_b(a2) → a1 = a2
  intro a1 a2 hjb
  -- j_b(a1) = j_b(a2) means (a1, b) = (a2, b), ie a1 = a2
  simp only [j, Prod.mk.injEq, and_true] at hjb
  exact hjb

-- b) What is j_b⁻¹(W) for a subset W ⊆ A × B?
-- Preimage is all the elements in A s.t. j_b(a) ∈ W
-- So {a : A | ⟨a, b⟩ ∈ W}
theorem ex6b (W : Set (A × B)) (b : B) :
    (j (b) (A:=A)) ⁻¹' W = {a : A | ⟨a, b⟩ ∈ W} := by
  ext a
  simp only [mem_preimage, j, mem_setOf_eq]
end

section
-- Exercise 7: Let A be a set and E ⊆ A.
variable {A : Type*}

-- The function χ_E : A → {0, 1} defined by:
--   χ_E(x) = 1 if x ∈ E and χ_E(x) = 0 if x ∉ E
-- is called the characteristic function of E.
noncomputable
def chi (E : Set A) : A → ℕ := Set.indicator E (fun _ => 1)

-- Let E and F be subsets of A, show:
-- a) χ_(E ∩ F) = χ_E · χ_F, where χ_E·χ_F(x) = χ_E(x)χ_F(x);

theorem ex7a (E F : Set A) : chi (E ∩ F) = fun x => (chi E x) * (chi F x) := by
  -- Show χ_(E ∩ F)(a) = χ_E(a)χ_F(a)
  ext a
  -- Basically just compute the truth table
  by_cases haE : a ∈ E <;>
  by_cases haF : a ∈ F <;>
  simp [chi, haE, haF]

-- b) χ_(E ∪ F) = χ_E + χ_F - χ_(E ∩ F)
theorem ex7b (E F : Set A) : chi (E ∪ F) = fun x => (chi E x) + (chi F x) - (chi (E ∩ F) x) := by
  ext a
  -- simp [ex7a E F]
  by_cases haE : a ∈ E <;>
  by_cases haF : a ∈ F <;>
  simp [chi, haE, haF]

-- c) Find a similar expression for χ_(E ∪ F ∪ G)
theorem ex7c (E F G : Set A) : chi (E ∪ F ∪ G) =
    fun x => (chi E x) + (chi F x) + (chi G x)
             - ((chi (E ∩ F) x) + (chi (E ∩ G) x) + (chi (F ∩ G) x))
             + (chi (E ∩ F ∩ G) x)
  := by
    ext a
    by_cases haE : a ∈ E <;>
    by_cases haF : a ∈ F <;>
    by_cases haG : a ∈ G <;>
    simp [chi, haE, haF, haG]
end

section
-- Exercise 8: Let A be a set to which there belong precisely n distinct objects.
-- Prove that there are precisely 2ⁿ distinct objects that belong to 2ᴬ.
variable {A : Type*}

-- Outline:
-- 1) Every subset E ⊆ A defines a function χ_E : A → {0, 1}
-- 2) For every function f : A → {0, 1} we can define E = {x ∈ A | f(x) = 1}
-- 3) Prove that this is a bijection
-- 4) If |A| = n, a function A -> {0, 1} is a choice of two options for each of the n elements,
--      so there are 2^n such functions.
-- 5) By the bijection above, that means there are 2^n distinct subsets of A.

-- Proof:

-- 1) Every distinct subset E ⊆ A uniquely defines a function χ_E : A → {0, 1}
noncomputable
def chi_bool (E : Set A) : A → Bool :=
  E.indicator (fun _ => true)

-- 2) For every function f : A → {0, 1}, we can define the set E where it is 1.
def subsetOfFun (f : A → Bool) : Set A := {x | f x = true}

-- 3) Prove that this is a bijection
-- In other words, that chi_bool and subsetOfFun are in bijection
-- This will give us that (E : Set A) and (f: A → Bool) have the same cardinality

-- 3a) We need the left inverse, ie ∀ a, inv(to(a)) = a
lemma subsetOfFun_chi (E : Set A) : subsetOfFun (chi_bool E) = E := by
  ext x
  constructor <;> simp [subsetOfFun, chi_bool]

-- 3b) Also the right inverse, ie ∀ b, to(inv(b)) = b
lemma chi_subsetOfFun (f : A → Bool) : chi_bool (subsetOfFun f) = f := by
  ext x
  simp [subsetOfFun, chi_bool]
  cases h : f x <;> simp [h];
  rfl

-- 3c) Then we can show the equivalence
noncomputable
def subsetsEquivBoolFun : Set A ≃ (A → Bool) := by
  refine
  { toFun := chi_bool
    invFun := subsetOfFun
    left_inv := subsetOfFun_chi
    right_inv := chi_subsetOfFun }

-- 4) If |A| = n, |f : A -> {0, 1}| = 2^n, so there are 2^n such functions.
--    By the bijection above, there are then 2^n distinct subsets of A.
theorem ex8 (A : Type*) [Fintype A] : Fintype.card (Set A) = 2 ^ Fintype.card A := by
  classical
  -- Using the bijection between distinct subsets of A and functions : A → {0, 1},
  have h1 := Fintype.card_congr (subsetsEquivBoolFun : Set A ≃ (A → Bool))
  -- We can show there are 2^n functions A → {0, 1}
  have h2 : Fintype.card (A → Bool) = 2 ^ Fintype.card A := by
      have hBool : Fintype.card Bool = 2 := by decide             -- Bool has 2 elements
      have h := Fintype.card_fun (α := A) (β := Bool)
      simp only [hBool, h]
  -- So there are 2^n distinct subsets of A
  rw [← h1] at h2
  exact h2
end

end Ch1_6
