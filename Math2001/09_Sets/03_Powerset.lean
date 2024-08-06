/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Set Function


#check {3, 4, 5} -- `{3, 4, 5} : Set ℕ`
#check {n : ℕ | 8 < n} -- `{n | 8 < n} : Set ℕ`
#check {k : ℕ | ∃ a, a ^ 2 = k} -- `{k | ∃ a, a ^ 2 = k} : Set ℕ`


#check {{3, 4}, {4, 5, 6}} -- `{{3, 4}, {4, 5, 6}} : Set (Set ℕ)`
#check {s : Set ℕ | 3 ∈ s} -- `{s | 3 ∈ s} : Set (Set ℕ)`



example : {n : ℕ | Nat.Even n} ∉ {s : Set ℕ | 3 ∈ s} := by
  dsimp
  rw [← Nat.odd_iff_not_even]
  use 1
  numbers


def p (s : Set ℕ) : Set ℕ := {n : ℕ | n + 1 ∈ s}

#check @p -- `p : Set ℕ → Set ℕ`


example : ¬ Injective p := by
  dsimp [Injective, p]
  push_neg
  use {0}, ∅
  dsimp
  constructor
  · ext x
    dsimp
    suffices x + 1 ≠ 0 by exhaust
    apply ne_of_gt
    extra
  · ext
    push_neg
    use 0
    dsimp
    exhaust


def q (s : Set ℤ) : Set ℤ := {n : ℤ | n + 1 ∈ s}

example : Injective q := by
  dsimp [Injective, q]
  intro s t hst
  ext k
  have hk : k - 1 ∈ {n | n + 1 ∈ s} ↔ k - 1 ∈ {n | n + 1 ∈ t} := by rw [hst]
  dsimp at hk
  conv at hk => ring
  apply hk



example : ¬ ∃ f : X → Set X, Surjective f := by
  intro h
  obtain ⟨f, hf⟩ := h
  let s : Set X := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf s
  by_cases hxs : x ∈ s
  · have hfx : x ∉ f x := hxs
    rw [hx] at hfx
    contradiction
  · have hfx : ¬ x ∉ f x := hxs
    rw [hx] at hfx
    contradiction

/-! # Exercises -/


def r (s : Set ℕ) : Set ℕ := s ∪ {3}



example : ¬ Injective r := by
  dsimp [Injective]; push_neg
  use {3}, ∅
  constructor
  ·
    calc r {3}
      _ = {3, 3} := rfl
      _ = {3} := pair_eq_singleton 3
      _ = ∅ ∪ {3} := by rw [empty_union {3}]
      _ = r ∅ := rfl
  ·
    apply singleton_ne_empty 3

namespace Int

def U : ℕ → Set ℤ
  | 0 => univ
  | n + 1 => {x : ℤ | ∃ y ∈ U n, x = 2 * y}

example (n : ℕ) : U n = {x : ℤ | (2:ℤ) ^ n ∣ x} := by
  -- By induction on n
  simple_induction n with k hk
  · -- Base case: n = 0. Prove that U₀ = {x | 2⁰ ∣ x}
    rw [U]
    ext n
    constructor
    · -- ( → ) -- Since 2⁰ = 1, we're done
      intro _; use n; ring
    · -- ( ← ) -- Clearly ∀ n ∈ N, n ∈ N
      intro _; dsimp
  · -- Inductive step.
    -- Prove that Uₖ = {x | 2ᵏ ∣ x} → Uₖ₊₁ = {x | 2ᵏ⁺¹ ∣ x}
    -- Suppose Uₖ = {x | 2ᵏ ∣ x}
    --  Let x be arbitrary
    rw [U]; ext x; dsimp
    constructor
    · -- ( → )
      --  Suppose ∃ y ∈ Uₖ with x = 2 ⬝ y, and choose y accordingly
      intro h1
      obtain ⟨y, ⟨h2, h3⟩⟩ := h1
      --    Since y ∈ Uₖ, by definition of U, y ∣ 2ᵏ
      --    thus we can choose c with y = 2ᵏ ⬝ c
      have h4: 2 ^ k ∣ y := by
        rw [hk] at h2
        apply h2
      obtain ⟨c, hc⟩ := h4
      --  Since x = 2 ⬝ y = 2 ⬝ (2ᵏ ⬝ c) = 2ᵏ⁺¹ ⬝ c,
      --  2ᵏ⁺¹ divides x. Thus x ∈ Uₖ₊₁
      use c
      calc x
        _ = 2 * y := h3
        _ = 2 * (2 ^ k * c) := by rw [hc]
        _ = 2 ^ (k + 1) * c := by ring

    · -- Suppose 2ᵏ⁺¹ ∣ x
      intro h6
      --  Then we can choose c with x = c ⬝ 2ᵏ⁺¹
      obtain ⟨c, hc⟩ := h6 -- hc: x = 2 ^ (k + 1) * c
      --  Since 2ᵏ⁺¹ ∣ x, we also know 2ᵏ ∣ x
      --    Thus:
      --      2ᵏ ⬝ c ∈ Uₖ and since
      --      x = 2ᵏ⁺¹ ⬝ c = 2 ⬝ (2ᵏ ⬝ c)
      --    2ᵏ ⬝ c is witness to ∃ y ∈ Uₖ | x = 2 * y
      use 2 ^ k * c
      constructor
      ·
        rw [hk]; use c; ring
      ·
        rw [hc]; ring
