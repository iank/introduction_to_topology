import Mathlib

open Set

-- Ch 1.2, exercise 2. If A ⊆ B and B ⊆ C, prove that A ⊆ C
theorem _subset_trans {α : Type} {A B C : Set α}
  (hAB : A ⊆ B) (hBC : B ⊆ C) :
    A ⊆ C := by
      intro x hx                              -- Let x be some element x ∈ A
      have hxB : x ∈ B := hAB hx              -- Since x ∈ A, then x ∈ B because A ⊆ B
      have hxC : x ∈ C := hBC hxB             -- Since x ∈ B, then x ∈ C because B ⊆ C
      exact hxC

-- Ch 1.2, exercise 3. Let A₁ .. Aₙ be sets. Prove that if A₁ ⊆ A₂, A₂ ⊆ A₃,
-- Aₙ₋₁ ⊆ Aₙ, and Aₙ ⊆ A₁, then A₁ = A₂ = .. = Aₙ.

-- We can use subset_antisymm, ie A ⊆ B and B ⊆ A → A = B

-- Prove it for 3 sets first
theorem cycle3_equal {α} {A₁ A₂ A₃ : Set α}
  (h12 : A₁ ⊆ A₂)
  (h23 : A₂ ⊆ A₃)
  (h31 : A₃ ⊆ A₁) :
    A₁ = A₂ ∧ A₂ = A₃ := by
      -- Basically show that ∀ i j, Aᵢ ⊆ Aⱼ
      -- Then use subset_antisymm to show that Aᵢ ⊆ Aⱼ and Aⱼ ⊆ Aᵢ → Aⱼ = Aᵢ
      have h13 : A₁ ⊆ A₃ := subset_trans h12 h23            -- A₁ ⊆ A₃
      have hA1_eq_A3 : A₁ = A₃ := subset_antisymm h13 h31   -- A₁ = A₃
      have h21 : A₂ ⊆ A₁ := subset_trans h23 h31            -- A₂ ⊆ A₁
      have hA1_eq_A2 : A₁ = A₂ := subset_antisymm h12 h21   -- A₁ = A₂
      have h32 : A₃ ⊆ A₂ := subset_trans h31 h12            -- A₃ ⊆ A₂
      have hA2_eq_A3 : A₂ = A₃ := subset_antisymm h23 h32   -- A₂ = A₃
      -- Now we have A₁ = A₂ and A₂ = A₃, so construct A₁ = A₂ ∧ A₂ = A₃
      constructor
      · exact hA1_eq_A2
      · exact hA2_eq_A3

-- Now for n sets
theorem cycle_equal
  {α : Type} {n : ℕ}
  (A : Fin (n + 1) → Set α)
  (hstep : ∀ i : Fin n, A i.castSucc ⊆ A i.succ)   -- Aᵢ ⊆ Aᵢ₊₁
  (hwrap : A (Fin.last n) ⊆ A 0) :                 -- Aₙ ⊆ A₀
  ∀ i : Fin (n+1), A i = A 0 := by
    -- First show that A_p ⊆ A_q for all p ≤ q
    have forward :
      ∀ (p q : Fin (n+1)), p ≤ q → A p ⊆ A q :=
    by
      intro p q hpq
      induction q using Fin.induction with
      -- Base: If q = 0 then A p ⊆ A q trivially, because p = 0
      | zero =>
        -- Prove Aₚ ⊆ A₀. Trivial since p ≤ 0
        have hp_eq_0 : p = 0 := le_antisymm hpq (Fin.zero_le p)   -- p ≤ 0 and 0 ≤ p so p = 0
        rw [hp_eq_0]                                              -- Aₚ ⊆ A₀ since p = 0

      -- Induction step: Assuming p ≤ q → A p ⊆ A q, now show A p ⊆ A q+1
      | succ q ih =>
        by_cases h : p = q.succ
        -- First, if p = q+1 then A p ⊆ A q+1 trivially
        case pos =>
          subst h
          exact subset_rfl
        -- If ¬p = q+1 then p < q+1 → p ≤ q, so induction hypothesis applies
        -- Then use subset_trans to prove A p ⊆ A q+1
        --   Because A p ⊆ A q (induction hypothesis)
        --   And A q ⊆ A q+1   (hstep)
        case neg =>
          have hpq' : p < q.succ ∨ p = q.succ :=
            lt_or_eq_of_le hpq
          cases hpq' with
          | inr heq =>
            exact (h heq).elim
          | inl hlt =>
            have hle : p ≤ q.castSucc := (Fin.le_castSucc_iff).2 hlt
            have h1 : A p ⊆ A q.castSucc := ih hle
            have h2 : A q.castSucc ⊆ A q.succ := hstep q
            exact subset_trans h1 h2
    -- Now that we know for p ≤ q, A_p ⊆ A_q We can show that:
    --   ∀ i, A₀ ⊆ Aᵢ (because 0 ≤ i), and
    --        Aᵢ ⊆ A₀ (because 0 ≤ n and Aₙ ⊆ A₀)
    intro i
    -- Show A₀ ⊆ Aᵢ
    have h0i : A 0 ⊆ A i := forward 0 i (Fin.zero_le i)
    -- Show Aᵢ ⊆ A₀
    have hi0 : A i ⊆ A 0 := by
      have hin : A i ⊆ A (Fin.last n) :=        -- Because Aᵢ ⊆ Aₙ (by `forward`)
        forward i (Fin.last n) (Fin.le_last i)
      exact subset_trans hin hwrap              -- And Aₙ ⊆ A₀ (by `hwrap`)
    -- Therefore Aᵢ = A₀
    apply subset_antisymm hi0 h0i
