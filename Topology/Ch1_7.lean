import Mathlib

namespace Ch1_7

-- Section 7, Relations
namespace ex1

/- Exercise 1
Let P be a subset of the real numbers ℝ such that
i) 1 ∈ P,
ii) if a, b ∈ P then a + b ∈ P, and
iii) for each x ∈ R, one and only one of the three statements,
     x ∈ P, x = 0, or −x ∈ P is true.
Define Q = { (a, b) | (a, b) ∈ ℝ × ℝ and a − b ∈ P }
Prove that Q is a transitive relation.
-/

def exactlyOne (a b c : Prop) : Prop :=
  (a ∧ ¬ b ∧ ¬ c) ∨
  (¬ a ∧ b ∧ ¬ c) ∨
  (¬ a ∧ ¬ b ∧ c)

variable (P : Set ℝ)

def Q (a b : ℝ) : Prop := a - b ∈ P

set_option linter.unusedVariables false
theorem ex1
  (h1 : (1 : ℝ) ∈ P)
  (h2 : ∀ {a b : ℝ}, a ∈ P → b ∈ P → a + b ∈ P)
  (h3 : ∀ x : ℝ, exactlyOne (x ∈ P) (x = 0) (-x ∈ P))
: Transitive (Q P) := by
  intro a b c       -- Arbitrary a, b, c
  simp only [Q]     -- Rewrite Q -> a - b ∈ P
  intro aQb bQc
  -- By h2, since a - b ∈ P and b - c ∈ P, a - b + b - c ∈ P, ie a - c ∈ P
  have habbc : (a - b) + (b - c) ∈ P := h2 aQb bQc
  simpa only [sub_add_sub_cancel] using habbc
set_option linter.unusedVariables true

end ex1

namespace ex2
-- Exercise 2
-- Let f : X → Y be a function from a set X onto a set Y.

variable {X Y : Type _}
variable (f : X → Y)

-- Let R be the subset of X × X consisting of those pairs (x, x') such that f(x) = f(x').
def R (x x' : X) : Prop := f x = f x'

-- Prove that R is an equivalence relation.
theorem ex2a : Equivalence (R f) := by
  -- Need to show R is reflexive, symmetric, and transitive
  constructor
  case refl =>
    -- xRx → f(x) = f(x), which is true for all x ∈ X
    intro x
    simp only [R]
  case symm =>
    intro x x'
    simp only [R]
    -- Show xRx' → x'Rx, ie f(x) = f(x') → f(x') = f(x)
    intro hfx
    simp only [hfx]
  case trans =>
    -- Show aRb, bRc → aRc
    intro a b c
    simp only [R]
    intro hab hbc
    rw [hbc] at hab
    exact hab

-- Let π : X → X/R be the projection.
def π : X → Quot (R f) := Quot.mk (R f)

--   Verify that if α ∈ X/R is an equivalence class,
--   to define F(α) = f(a) whenever α = π(a), establishes a well-defined function
--   F : X/R → Y which is one-one and onto.

def F : Quot (R f) → Y :=
  -- Define F(α) = f(a) and prove that it is well-defined
  Quot.lift f (by
    intro a b hab
    simpa [R] using hab)

-- Show F is one-one and onto
theorem ex2b (hf: Function.Surjective f) : Function.Injective (F f) ∧ Function.Surjective (F f) := by
  constructor
  · -- Show one-one
    intro α α' hα
    induction α using Quot.ind
    case mk a =>
      induction α' using Quot.ind
      case mk b =>
        apply Quot.sound
        simp [R]
        simpa [F] using hα
  · -- Show onto
    intro y       -- For an arbitrary y ∈ Y, we must show ∃ a, F(f(a)) = y
    obtain ⟨x, hx⟩ := hf y
    use Quot.mk (R f) x
    simp only [F]
    exact hx
end ex2

namespace ex3
-- Exercise 3
-- Let f : X → X be a one-one function of a set X into itself.

variable (X : Type*) (f : X → X) (hf : Function.Injective f)

-- Define a sequence of functions f⁰, f¹, f², …, fⁿ, … : X → X
-- by letting f⁰ be the identity, f¹ = f, and inductively fⁿ(x) = f(fⁿ⁻¹(x)).

def f_iter : ℕ → (X → X)
  | 0 => id
  | n + 1 => f ∘ (f_iter n)

-- a) Prove that each of these functions is one-one.
theorem ex3a (n : ℕ) (hf : Function.Injective f) : Function.Injective (f_iter X f n) := by
  -- Must show fⁿ(x) = fⁿ(x') → x = x'
  induction n with
  -- Show f⁰(x) = f⁰(x') → x = x'
  | zero =>
    intro x x'
    simp only [f_iter, id_eq, imp_self]
  -- If fⁿ is injective, show fⁿ⁺¹ is injective
  | succ n ih =>
    intro x x' hfx
    -- we'll use the fact that f is injective,
    -- and that fⁿ is injective,
    -- and that fⁿ⁺¹(x) = f ∘ fⁿ(x)
    simp only [f_iter, Function.comp_apply] at hfx
    apply ih (hf hfx)

-- Let R be the subset of X × X consisting of those pairs (a, b) such that
-- b = fᵏ(a) for some integer k or a = fʲ(b) for some integer j.

def R : X → X → Prop :=
  fun a b => (∃ k : ℕ, b = f_iter X f k a) ∨ (∃ j : ℕ, a = f_iter X f j b)

-- b) Prove that R is an equivalence relation.

theorem R_refl : Reflexive (R X f) := by
  -- aRb means ∃ k, b = fᵏ(a) or ∃ k, a = fᵏ(b)
  intro x
  -- xRx means ∃ k, x = fᵏ(x)
  simp only [R, or_self]
  -- Let k = 0
  use 0
  -- f⁰(x) = id(x) = x
  simp [f_iter]

theorem R_symm : Symmetric (R X f) := by
  intro a b haRb
  -- Show aRb → bRa
  simp only [R] at haRb
  simp only [R]
  -- aRb means either b = fᵏ(a) or a = fʲ(b) for some k or j
  -- bRa means either a = fᵏ(b) or b = fʲ(a) for some k or j
  -- So we just apply whichever case is true to the opposite case in the goal.
  rcases haRb with ⟨k, hb⟩ | ⟨j, ha⟩
  · -- Suppose b = fᵏ(a)
    right
    use k
  · -- Suppose a = fʲ(b)
    left
    use j

-- We'll use fᵏ(fʲ(x)) = f⁽ᵏ⁺ʲ⁾(x) below
lemma f_iter_add (k j : ℕ) (a : X) : f_iter X f (k + j) a = f_iter X f j (f_iter X f k a) := by
  induction j with
  | zero =>
    rfl
  | succ n ih =>
    simp only [f_iter, Nat.add_eq, Function.comp_apply]
    rw [ih]

-- f⁽ᵏ⁻ʲ⁾(fʲ(b)) = fᵏ(b)
lemma f_iter_sub (j k : ℕ) (h : j < k) (b : X) :
  f_iter X f (k - j) (f_iter X f j b) = f_iter X f k b := by
    have hk : k = j + (k - j) := (Nat.add_sub_cancel' (Nat.le_of_lt h)).symm
    nth_rw 2 [hk]
    rw [← f_iter_add]

-- fʲ(b) = fᵏ(a) means that either b = fᵐ(a) or a = fᵐ(b), depending on whether j' > k
lemma f_iter_eq_implies_R (hf : Function.Injective f) (k j : ℕ) (a b : X) :
  f_iter X f j b = f_iter X f k a → (∃ m, b = f_iter X f m a) ∨ (∃ n, a = f_iter X f n b) := by
  intro h
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · -- j < k
    left
    use k - j
    have hj := ex3a X f j hf
    apply hj
    have hk : (k - j) + j = k := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    have hadd := f_iter_add X f (k - j) j a
    rw [hk] at hadd
    rw [← h] at hadd
    exact hadd
  · -- k = j
    left
    use 0
    subst heq
    have hj := ex3a X f j hf
    have hba : b = a := hj h
    simp [hba, f_iter]
  · -- k < j
    right
    use j - k
    have hk := ex3a X f k hf
    apply hk
    have hj : (j - k) + k = j := Nat.sub_add_cancel (Nat.le_of_lt hgt)
    have hadd := f_iter_add X f (j - k) k b
    rw [hj] at hadd
    rw [h] at hadd
    exact hadd

theorem R_trans (hf : Function.Injective f) : Transitive (R X f) := by
  intro a b c haRb hbRc
  -- Show aRb and bRc → aRc
  -- have:
  --   aRb (ie,  either b = fᵏ(a) or a = fʲ(b) for some k or j)
  --   bRc (ie,  either c = fᵏ(b) or b = fʲ(c) for some k or j)
  -- goal:
  --   aRc (ie,  either c = fᵏ(a) or a = fʲ(c) for some k or j)
  simp only [R] at haRb
  rcases haRb with ⟨k, hb⟩ | ⟨j, ha⟩
  · rcases hbRc with ⟨k', hckb⟩ | ⟨j', hbjc⟩
    · -- i) c = fᵏ'(b) and b = fᵏ(a), therefore
      --    c = fᵏ'(fᵏ(a)) = f⁽ᵏ' ⁺ ᵏ⁾(a)
      -- So aRc.
      rw [hb] at hckb
      rw [← f_iter_add] at hckb
      simp only [R]
      left
      use k + k'
    · -- ii) b = fʲ'(c) and b = fᵏ(a), therefore
      --     fʲ'(c) = fᵏ(a)
      --     This means that either c = fᵐ(a) or a = fᵐ(c), depending on whether j' > k
      -- The goal, aRc, is either one of those statements.
      rw [hb] at hbjc
      have h := f_iter_eq_implies_R X f hf j' k c a hbjc
      simp only [R]
      exact h.symm
  · rcases hbRc with ⟨k', hckb⟩ | ⟨j', hbjc⟩
    · -- iii) c = fᵏ'(b) and a = fʲ(b)
      --      Either k' = j, so c = a
      --      Or k' > j, so c = f^(k' - j)(fʲ(b)) = f^(k' - j)(a)
      --      Or j > k', so a = f^(j - k')(fᵏ'(b)) = f^(j - k')(c)
      rcases Nat.lt_trichotomy j k' with hlt | heq | hgt
      · -- j < k'
        simp only [R]
        left
        use k' - j
        have h := f_iter_sub X f j k' hlt b
        rw [← h] at hckb
        rw [← ha] at hckb
        exact hckb
      · -- j = k'
        rw [heq] at ha
        rw [← hckb] at ha
        rw [ha]
        apply R_refl
      · -- k' < j
        simp only [R]
        right
        use j - k'
        have h := f_iter_sub X f k' j hgt b
        rw [← h] at ha
        rw [← hckb] at ha
        exact ha
    · -- iv) b = fʲ'(c) and a = fʲ(b), therefore
      --     a = fʲ(fʲ'(c)) = f⁽ʲ ⁺ ʲ'⁾(c)
      -- So aRc, like case i)
      rw [hbjc] at ha
      rw [← f_iter_add] at ha
      simp only [R]
      right
      use j' + j

theorem R_equivalence (hf : Function.Injective f): Equivalence (R X f) := by
  constructor
  case refl => apply R_refl
  case symm => apply R_symm
  case trans => apply R_trans X f hf

-- This one really blew up for a couple of reasons.
-- I guess we reimplemented parts of Function.iterate, iterate_add, and
-- iterate_injective.
-- Defining fⁿ on ℤ instead of ℕ might have made it simpler too.
end ex3

namespace ex4
-- Exercise 4

-- Let X be the set of functions from the real numbers into the real numbers
-- possessing continuous derivatives.
def X : Set (ℝ → ℝ) := {f | ContDiff ℝ 1 f}

-- Let R be the subset of X × X consisting of those pairs (f, g) such that
-- Df = Dg where D maps a function into its derivative.
noncomputable
def D (f : ℝ → ℝ) : ℝ → ℝ := deriv f
def R : Set (X × X) := {p | D p.1.val = D p.2.val}

-- Prove that R is an equivalence relation and describe an equivalence set π(f).
theorem R_refl : ∀ f : X, (f, f) ∈ R := by
  intro f
  rfl

theorem R_symm : ∀ f g : X, (f, g) ∈ R → (g, f) ∈ R := by
  intro f g hfRg
  simp only [R, Set.mem_setOf_eq]
  simp only [R, Set.mem_setOf_eq] at hfRg
  exact hfRg.symm

theorem R_trans : ∀ f g h : X, (f, g) ∈ R → (g, h) ∈ R → (f, h) ∈ R := by
  -- Have fRg and gRh, show this implies fRh
  intro f g h
  simp only [R, Set.mem_setOf_eq]
  intro hfRg hgRh
  rw [hfRg]
  exact hgRh

theorem R_equivalence : Equivalence (fun (f g : X) => (f, g) ∈ R) := by
  constructor
  case refl => apply R_refl
  case symm => apply R_symm
  case trans => apply R_trans

def equiv_class (f : X) : Set X := {g | (f, g) ∈ R}

-- Describe the equivalence class: two functions are equivalent iff they differ by a constant
theorem equiv_class_characterization (f : X) :
  ∀ g : X, g ∈ equiv_class f ↔ ∃ c : ℝ, ∀ x : ℝ, g.val x = f.val x + c := by
  intro g
  constructor
  · -- g ∈ π(f) → g(x) = f(x) + c
    intro hequiv
    -- g ∈ π(f) means D f = D g
    simp only [equiv_class, R, D, Set.mem_setOf_eq] at hequiv
    -- We'll need the differentiability of f and g to move forward
    have hf_diff : Differentiable ℝ f.val := (Set.mem_setOf.mp f.property).differentiable le_rfl
    have hg_diff : Differentiable ℝ g.val := (Set.mem_setOf.mp g.property).differentiable le_rfl
    -- We know D (g - f) = 0 since D g = D f and they are differentiable
    have h : deriv (g.val - f.val) = 0 := by
      funext x
      rw [deriv_sub (hg_diff.differentiableAt) (hf_diff.differentiableAt)]
      rw [← hequiv]
      simp
    -- Let c = g(0) - f(0). Goal becomes: for any x, show g(x) = f(x) + g(0) - f(0)
    use (g.val - f.val) 0
    intro x
    -- Using the fact that D (g - f) = 0 we know that g(x) - f(x) = g(y) - f(y),
    -- ie, g(x) - f(x) = g(0) - f(0)
    have := is_const_of_deriv_eq_zero (hg_diff.sub hf_diff) (fun x => by simp [h]) x 0
    rw [← this]
    -- Goal is now: g(x) = f(x) + g(x) - f(x)
    simp
  · -- g(x) = f(x) + c → g ∈ π(f)
    intro hc
    obtain ⟨c, hc⟩ := hc
    simp only [equiv_class, R, D, Set.mem_setOf_eq]
    have heq := funext hc
    rw [heq]
    exact Eq.symm (deriv_add_const' c)
end ex4

namespace ex5
/- Exercise 5

Let E be the set of all functions from a set X into a set Y.
Let b ∈ X and let R be the subset of E × E consisting of those pairs (f, g)
such that f(b) = g(b).

Prove that R is an equivalence relation.

Define a one-one onto function e_b : E/R → Y. -/
variable (X Y : Type)
variable (b : X)

def E : Type := X → Y

def R : E X Y → E X Y → Prop := fun f g => f b = g b

theorem R_refl : ∀ f : E X Y, R X Y b f f := by
  sorry

theorem R_symm : ∀ f g : E X Y, R X Y b f g → R X Y b g f := by
  sorry

theorem R_trans : ∀ f g h : E X Y, R X Y b f g → R X Y b g h → R X Y b f h := by
  sorry

theorem R_equivalence : Equivalence (R X Y b) := by
  sorry

-- E/R
def E_mod_R : Type := Quot (R X Y b)

-- E/R → Y
def e_b : E_mod_R X Y b → Y := by
  sorry

theorem e_b_injective : Function.Injective (e_b X Y b) := by
  sorry

theorem e_b_surjective : Function.Surjective (e_b X Y b) := by
  sorry

theorem e_b_bijective : Function.Bijective (e_b X Y b) := by
  sorry

end ex5

end Ch1_7
