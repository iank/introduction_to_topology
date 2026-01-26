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
-- TODO
end ex2

namespace ex3
-- TODO
end ex3

namespace ex4
-- TODO
end ex4

end Ch1_10
