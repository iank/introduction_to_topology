import Mathlib

open Set

section
-- Exercise 1. Let A ⊆ S, B ⊆ S.
variable {S : Type}
variable (A B : Set S)

-- Prove:
-- a) A ⊆ B if and only if A ∪ B = B.
theorem ex1a : A ⊆ B ↔ A ∪ B = B := by
  constructor -- Split the IFF into two proofs
  ·           -- A ⊆ B → A ∪ B = B
    intro h
    apply subset_antisymm       -- Prove A ∪ B = B
    · intro x hx                -- 1) Show A ∪ B ⊆ B
      rcases hx with hxA | hxB  -- x is either in A or B (union). Show in both cases it is in B.
      · exact h hxA             -- First, x ∈ A → x ∈ B because A ⊆ B
      · exact hxB               -- Second, x ∈ B
    · intro x hx                -- 2) Show B ⊆ A ∪ B
      exact Or.inr hx           -- x ∈ B → x ∈ right side of (A ∪ B)
  ·           -- A ∪ B = B → A ⊆ B
    intro h x hxA                        -- Prove that x ∈ A → x ∈ B
    have hxAB : x ∈ A ∪ B := Or.inl hxA  -- x ∈ A ∪ B because x ∈ A
    simp only [h] at hxAB                -- But A ∪ B = B
    exact hxAB                           -- So x ∈ B

-- b) A ⊆ B if and only if A ∩ B = A
theorem ex1b : A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro h         -- Show A ⊆ B → A ∩ B = A
    apply subset_antisymm     -- Prove A ∩ B = A by showing that A ∩ B ⊆ A and A ⊆ A ∩ B
    · intro x hx              -- Show that x ∈ A ∩ B → x ∈ A
      exact hx.left           -- x ∈ A ∩ B → x ∈ A ∧ x ∈ B → x ∈ A
    · intro x hxA             -- Now show that x ∈ A → x ∈ A ∧ B
      have hxB : x ∈ B := h hxA -- x ∈ B by x ∈ A and A ⊆ B
      exact And.intro hxA hxB   -- x ∈ A, x ∈ B → x ∈ A ∩ B
  · intro h x hxA   -- Show A ∩ B = A → A ⊆ B by showing x ∈ A → x ∈ B
    have hxAB : x ∈ A ∩ B := by -- Prove x ∈ A ∩ B
      rw [← h] at hxA           -- trivial by rewriting x ∈ A with h (A ∩ B = A)
      exact hxA
    exact hxAB.right            -- Since x ∈ A ∩ B, x ∈ A and x ∈ B

-- c) A ⊆ Bᶜ iff A ∩ B = ∅
theorem ex1c : A ⊆ Bᶜ ↔ A ∩ B = ∅ := by
  constructor
  · intro h       -- Show A ⊆ Bᶜ → A ∩ B = ∅
    apply subset_antisymm     -- Prove that A ∩ B = ∅ by showing that A ∩ B ⊆ ∅ and ∅ ⊆ A ∩ B
    · intro x hx              -- Prove that if x ∈ A ∩ B → x ∈ ∅
      rcases hx with ⟨hxA, hxB⟩   -- x is in A and B
      have hxBc : x ∈ Bᶜ := h hxA -- x is also in Bᶜ because A ⊆ Bᶜ
      exact hxBc hxB              -- x ∈ Bᶜ, x ∈ B → False (ie x ∈ ∅)
    · intro x hx              -- Prove that if x ∈ ∅ → x ∈ A ∩ B
      cases hx                -- x ∈ ∅ is definitionally equivalent to False, nothing to do
  · intro h x hxA -- Now show A ∩ B = ∅ → A ⊆ Bᶜ by showing that x ∈ A → x ∈ Bᶜ
    have hxBc : x ∈ Bᶜ := by
      intro hxB                           -- Assume x ∈ B
      have hxAB : x ∈ A ∩ B := ⟨hxA, hxB⟩ -- Then x ∈ A ∩ B because x ∈ A and x ∈ B
      rw [h] at hxAB                      -- But A ∩ B = ∅, so x ∈ A ∩ B → x ∈ ∅
      simp at hxAB                        -- False, so x ∈ Bᶜ, not x ∈ B
    exact hxBc

-- d) Aᶜ ⊆ B iff A ∪ B = S
theorem ex1d : Aᶜ ⊆ B ↔ A ∪ B = univ := by
  constructor
  · intro h         -- Show that Aᶜ ⊆ B → A ∪ B = S
    apply subset_antisymm   -- Show A ∪ B ⊆ S and S ⊆ A ∪ B
    · simp                  -- A ∪ B ⊆ S is trivial (S is universe)
    · intro x hx            -- S ⊆ A ∪ B. x ∈ S → x ∈ A OR x ∈ B
      by_cases hxA : x ∈ A
      case pos =>           -- x ∈ A is trivial
        left
        exact hxA
      case neg =>           -- x ∉ A → x ∈ B
        right
        have hxB : x ∈ B := h hxA
        exact hxB
  · intro h x hxAc  -- Show that A ∪ B = S → Aᶜ ⊆ B
    -- First, since x ∈ S and A ∪ B = S, x ∈ A ∪ B
    have hxUniv : x ∈ univ := by trivial
    rewrite [← h] at hxUniv
    -- Now show x ∈ B
    rcases hxUniv with hxA | hxB
    · exact False.elim (hxAc hxA)   -- x ∈ A cannot be the case
    · exact hxB                     -- so x ∈ B

-- e) A ⊆ B iff Bᶜ ⊆ Aᶜ
theorem ex1e : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  constructor
  -- Show that A ⊆ B → Bᶜ ⊆ Aᶜ
  · intro h x hx hxA          -- For x ∈ Bᶜ, prove x ∈ Aᶜ
    have hxB : x ∈ B := h hxA -- Assume x ∈ A. Then x ∈ B because A ⊆ B
    apply hx hxB              -- But x ∈ Bᶜ. contradiction
  -- Show that Bᶜ ⊆ Aᶜ → A ⊆ B
  · intro h x hxA             -- For x ∈ A, prove x ∈ B
    by_contra hxNotB                  -- Assume x ∈ Bᶜ
    have hxNotA : x ∈ Aᶜ := h hxNotB  -- Then x ∈ Aᶜ, because Bᶜ ⊆ Aᶜ
    exact hxNotA hxA                  -- But x ∈ A. contradiction

-- f) A ⊆ Bᶜ iff B ⊆ Aᶜ
theorem ex1f : A ⊆ Bᶜ ↔ B ⊆ Aᶜ := by
  constructor
  -- Show that A ⊆ Bᶜ → B ⊆ Aᶜ
  · intro h x hxB hxA             -- Assume x ∈ B and x ∈ A
    have hxBc : x ∈ Bᶜ := h hxA   -- Then x ∈ Bᶜ by A ⊆ Bᶜ
    exact hxBc hxB                -- Contradiction. Therefore x ∈ Aᶜ
  -- Show that B ⊆ Aᶜ → A ⊆ Bᶜ by the same argument
  · intro h x hxA hxB
    have hxAc : x ∈ Aᶜ := h hxB
    exact hxAc hxA

end

section
-- Exercise 2. Let X ⊆ Y ⊆ Z
variable {S : Type}
variable (X Y Z : Set S)

-- a) C_Y(X) ⊆ C_Z(X)
theorem ex2a (hYZ : Y ⊆ Z) : Y \ X ⊆ Z \ X := by
  intro x hx      -- x ∈ Y - X
  rcases hx with ⟨hxY, hxNotX⟩ -- so x ∈ Y and x ∉ X
  -- But Y ⊆ Z so x ∈ Z
  have hxZ : x ∈ Z := hYZ hxY
  exact ⟨hxZ, hxNotX⟩

-- b) Z - (Y - X) = X ∪ (Z - Y)
theorem ex2b (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : Z \ (Y \ X) = X ∪ (Z \ Y) := by
  apply subset_antisymm
  -- Show x ∈ Z - (Y - X) → x ∈ X ∪ (Z - Y)
  · intro x hx
    -- If x is in Z and not (Y \ X) then x is in Z \ Y or X
    by_cases hX : x ∈ X
    case pos => exact Or.inl hX   -- If x ∈ X then it's trivially in X ∪ (Z \ Y)
    case neg =>                   -- If x ∉ X, show that it must be in Z \ Y
      rcases hx with ⟨hxZ, hxNotYX⟩   -- x ∈ Z \ (Y \ X) so x ∈ Z and x ∉ Y \ X
      have hxNotY : x ∉ Y := by       -- Now show x ∉ Y by contradiction
        intro hxY                               -- if x ∈ Y
        have hxYNotX : x ∈ (Y \ X) := ⟨hxY, hX⟩ -- then x ∈ Y \ X (because x ∈ Y and x ∉ X)
        exact hxNotYX hxYNotX                   -- but x ∈ Y \ X contradicts x ∉ Y \ X
      -- Now we know x ∈ Z and x ∉ Y and x ∉ X
      have hxZNotY : x ∈ Z \ Y := ⟨hxZ, hxNotY⟩
      exact Or.inr hxZNotY
  -- Now show x ∈ X ∪ Z \ Y → x ∈ Z \ (Y \ X)
  · intro x hx
    -- Either x ∈ X or x ∈ Z \ Y
    rcases hx with hX | hxZNotY
    ·             -- x ∈ X, show that x ∈ Z \ (Y \ X)
      constructor
      ·           -- x ∈ Z
        have hxY : x ∈ Y := hXY hX
        have hxZ : x ∈ Z := hYZ hxY
        exact hxZ
      ·           -- x ∉ Y \ X by contradiction
        intro hxYNotX   -- if x ∈ Y \ X
        rcases hxYNotX with ⟨hxY, hxNotX⟩
        exact hxNotX hX
    ·             -- x ∈ Z \ Y, show that x ∈ Z \ (Y \ X)
      constructor
      ·           -- Show that x ∈ Z
        exact hxZNotY.1   -- x ∈ Z \ Y → ⟨x ∈ Z, x ∉ Y⟩
      ·           -- Show that x ∉ Y \ X
        rcases hxZNotY with ⟨hxZ, hxNotY⟩
        intro hxYNotX           -- x ∈ Y \ X would imply x ∈ Y (ie, hxYNotX.1)
        exact hxNotY hxYNotX.1  -- This contradicts x ∉ Y
end
