import Mathlib

namespace Ch1_10

-- Section 10, Arbitrary products

namespace ex1
-- Exercise 1:
-- Let A be a set. For each α ∈ I, let X_α = A.

universe u
variable (I : Type*)
variable (A : Type u)
def X (_i : I) : Type u := A

-- a) Verify that the product ∏_{α ∈ I} X_α is the set of all functions from the
-- set I to the set A. This set of functions is denoted by Aᴵ.
def ex1a : (∀ i : I, X I A i) ≃ (I → A) :=
  -- This is just definitionally true.
  -- The product here "consists of all functions x with domain the indexing set I
  -- having the property that for each a ∈ I, x(a) ∈ Xₐ"
  -- Here, since Xₐ = A, this product consists of all functions from I such that
  -- ∀ a ∈ I, x(a) ∈ A.
  Equiv.refl _

-- b): Suppose A = {0, 1}. If I is finite how many elements are there in Aᴵ?
theorem ex1b [Fintype I] [DecidableEq I] : Fintype.card (I → Bool) = 2 ^ Fintype.card I := by
  have h := Fintype.card_fun (α := I) (β := Bool)
  simp only [Fintype.card_bool] at h
  exact h

-- c) Verify that Aᴵ in this case is the set of all characteristic functions defined on I.
-- Recall the characteristic function χ_S(i), for S ⊆ I, is a function I → A
-- which equals 1 if i ∈ S and 0 if i ∉ S.

-- This is shown in Ch 1.6, exercise 8 and I won't repeat it here.
end ex1

namespace ex2
-- Exercise 2:

-- Let {X_α}_{α ∈ I}, {Y_α}_{α ∈ I} be two indexed families of sets with the
-- same indexing set I.

-- For each α ∈ I let f_α : X_α → Y_α.

variable {I : Type*}
variable {X Y Z : I → Type*}

-- a) Prove that there is a unique function f : ∏ X_α → ∏ Y_α such that
-- p_α ∘ f = f_α ∘ p_α for each α ∈ I, where p_α is the appropriate projection
-- map. This function f is denoted ∏_{α ∈ I} f_α.

/- Recall the projection map p_α : ∏ X_α → X_α.
   In other words, the argument to p_α is a function x : I → ⋃ X_i where ∀ i, x(i) ∈ X_i,
   and the result is x(α) ∈ X_α.

   So the definition of p_α is just the function evaluation x(α).
   Analogously we can think of x as a "point" in ∏ X_α consisting of |I|
   components and p_α is the α'th component.
-/
def p (α : I) (x : ∀ i, X i) : X α := x α

/- So we're given a family of functions f_α : X_α → Y_α and asked to prove that there is
   a unique function f = ∏ f_α satisfying the above composition w/ the projection map. -/
-- Define such a function:
def Pi_map (f : ∀ α, X α → Y α) : (∀ α, X α) → (∀ α, Y α) :=
  -- Recall that a point x is a function : I → ⋃ X_i where x(a) ∈ X_a.
  -- So Pi_map returns a function : I → ⋃ Y_i where y(a) ∈ Y_a.
  fun x => fun a => f a (p a x)

-- Now show it satisfies the composition equality
theorem ex2a_condition (f : ∀ α, X α → Y α) (α : I) :
    p α ∘ Pi_map f = f α ∘ p α := by
  ext x
  simp only [Function.comp_apply, p, Pi_map]

-- And that it is unique
theorem ex2a_unique (f : ∀ α, X α → Y α) (g : (∀ α, X α) → (∀ α, Y α))
    (hg : ∀ α, p α ∘ g = f α ∘ p α) : g = Pi_map f := by
  ext x α
  simp only [Pi_map]
  have h : (p α ∘ g) x = (f α ∘ p α) x := congr_fun (hg α) x
  simp only [Function.comp_apply, p] at h
  simp only [p]
  exact h

-- b) Given a third indexed family {Z_α} and functions g_α : Y_α → Z_α for each α ∈ I,
-- show that ∏ g_α ∘ ∏ f_α = ∏ (g_α ∘ f_α).
theorem ex2b (f : ∀ α, X α → Y α) (g : ∀ α, Y α → Z α) :
    Pi_map g ∘ Pi_map f = Pi_map (fun α => g α ∘ f α) :=
  sorry

-- c) Suppose that each f_α has an inverse k_α. Prove that ∏ f_α has the inverse ∏ k_α.
theorem ex2c (f : ∀ α, X α → Y α) (k : ∀ α, Y α → X α)
    (hk : ∀ α, Function.LeftInverse (k α) (f α) ∧ Function.RightInverse (k α) (f α)) :
    Function.LeftInverse (Pi_map k) (Pi_map f) ∧ Function.RightInverse (Pi_map k) (Pi_map f) :=
  sorry

end ex2

namespace ex3
-- TODO
end ex3

namespace ex4
-- TODO
end ex4

end Ch1_10
