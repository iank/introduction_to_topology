import Mathlib

namespace Ch1_8

-- Section 8, Composition of Functions and Diagrams
namespace ex1
/-  Exercise 1: Using the functions defined by the correspondences
      g(x) = x² and h(x) = √(x), x ≥ 0,
    construct an example of a commutative diagram similar to diagram (8.3)
-/

def A := { x : ℝ // 0 ≤ x }
def g : A → ℝ := fun x => x.val ^ 2

noncomputable
def h : ℝ → A := fun x => ⟨Real.sqrt x, Real.sqrt_nonneg x⟩

-- i is the identity on A
def i : A → A := id

/- The diagram is:

  A --- i --> A
   \         ^
    \g     h/
     \     /
      > ℝ /
-/

/- "The diagram is commutative if for each X and Y in the diagram that represent sets,
   and for any two paths in the diagram beginning at X and ending in Y, the two functions
   from X to Y so represented are equal."

   i.e., if ∀ x ∈ A, (hg)(x) = i(x)   -/
theorem ex1_commutative (x : A) : (h ∘ g) x = i x := by
  simp only [Function.comp_apply, h, g, NNReal.val_eq_coe, NNReal.zero_le_coe, Real.sqrt_sq]
  rfl
end ex1

namespace ex2
/- Exercise 2:

Let f: ℝ × ℝ → ℝ be the function defined by the correspondence f(x, y) = x² + y² and
let g : ℝ × ℝ → ℝ be the function defined by the correspondence g(x, y) = x + y.
Let h : ℝ → ℝ be the function defined by the correspondence h(x) = x². -/

def f : ℝ × ℝ → ℝ := fun ⟨x, y⟩ => x^2 + y^2
def g : ℝ × ℝ → ℝ := fun ⟨x, y⟩ => x + y
def h : ℝ → ℝ := fun x => x^2

/-
Is the diagram below commutative?

      ℝ×ℝ ---f-→ ℝ
        \       ↗
        g\     /h
          ↘   /
            ℝ
-/
theorem ex2_not_commutative : ¬ ∀ x y : ℝ, (h ∘ g) ⟨x, y⟩ = f ⟨x, y⟩ := by
  simp only [Function.comp_apply, h, g, f, not_forall]
  use 2, 2
  ring_nf
  simp

end ex2

namespace ex3
/- Exercise 3:

Let i: A → A be the identity function. Let the diagram

      A ---i--→ A
       \      ↗
       f\    /g
          ↘ /
           B

be commutative. -/

-- a) Prove that g: B → A is onto
theorem ex3_a {A B : Type*} (f : A → B) (g : B → A) (i : A → A)
    (hi : i = id) (hcomm : g ∘ f = i) : Function.Surjective g := by
  -- For arbitrary a, show ∃ b ∈ B s.t. g(b) = a
  intro a
  -- Use b = f(a) to satisfy this.
  use f a
  change (g ∘ f) a = id a
  rw [hcomm, hi]

-- b) Prove that f: A → B is one-one.
theorem ex3_b {A B : Type*} (f : A → B) (g : B → A) (i : A → A)
    (hi : i = id) (hcomm : g ∘ f = i) : Function.Injective f := by
  -- For arbitrary a a', show f(a) = f(a') → a = a'
  intro a a' hfeq
  -- g(f(a)) = g(f(a')) because f(a) = f(a') and g is a function
  have h : (g ∘ f) a = (g ∘ f) a' := congrArg g hfeq
  -- By commutivity we know that g(f(a)) = a and g(f(a')) = a'
  rw [hcomm, hi, id, id] at h
  -- so a = a'.
  exact h
end ex3

namespace ex4
/- Exercise 4:

Let f: A → B, g: B → C.

Prove that for Z ⊆ C, (g ∘ f)⁻¹(Z) = f⁻¹(g⁻¹(Z))
-/
theorem ex4_comp_preimage {A B C : Type*} (f : A → B) (g : B → C) (Z : Set C) :
    (g ∘ f) ⁻¹' Z = f ⁻¹' (g ⁻¹' Z) := by
  ext a
  -- Both sides are definitionally equal.
  -- a ∈ (g ∘ f)⁻¹(Z) means that g(f(a)) ∈ Z.
  -- and a ∈ f⁻¹(g⁻¹(Z)) means that f(a) ∈ g⁻¹(Z), ie, g(f(a)) ∈ Z.
  constructor <;> simp

end ex4

end Ch1_8
