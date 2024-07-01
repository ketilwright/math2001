/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
set_option maxHeartbeats 1000000
math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left; use 0; numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · -- suppose k is even
      right;
      use x
      calc k + 1
        _ = 2 * x + 1 := by rw [hx];
    · -- suppose k is odd
      left;
      use x + 1
      calc k + 1
        _ = 2 * x + 1 + 1 := by rw [hx]
        _ = 2 * (x + 1) := by ring

-- Same as theorem 7.3.16 in HTPI, which uses Exercise 6.1.13
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · -- base case
    use 0
    calc a ^ 0 - b ^ 0
      _ = 1 - 1 := by rfl
      _ = d * 0 :=  by ring
  · -- induction step
    -- Suppose aᵏ ≡ bᵏ mod d. then ∃ x | aᵏ - bᵏ = d x
    obtain ⟨x, hx⟩ := IH
    -- Since a ≡ₘ b, ∃ y | a - b = d y
    obtain ⟨y, hy⟩ := h
    -- goal: a ^ (k + 1) ≡ b ^ (k + 1) [ZMOD d]
    use a * x + (b ^ k) * y
    calc a ^ (k + 1) - b ^ (k + 1)
      _ = a * (a ^ k - b ^ k) + (b ^ k) * (a - b) := by ring
      _ = a * (d * x) + (b ^ k) * (d * y) := by rw [hx, hy]
      _ = d * (a * x + b ^ k * y) := by ring

/-
  Another approach; based on something from HTPIwL
-/

theorem HTPI.Exercise_6_1_13
  :
  ∀ (a b : Int) (n : ℕ), (a - b) ∣ (a ^ n - b ^ n) := by
    intro a b n
    simple_induction n with k IH
    ·
      use 0
      calc a ^ 0 - b ^ 0
      _ = 1 - 1 := by rfl
      _ = (a - b) * 0 :=  by ring
    ·
      obtain ⟨c, hc⟩ := IH
      -- hc: a ^ k - b ^ k = (a - b) * c
      use a * c + b ^ k
      calc  a ^ (k + 1) - b ^ (k + 1)
        _ = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by ring
        _ = a * ((a - b) * c) + (a - b) * b ^ k := by rw [hc]
        _ = (a - b) * (a * c + b ^ k) := by ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  -- Since a ≡ b mod d, there is x with a - b = d x
  obtain ⟨x, hx⟩ := h
  -- From 6.1.13 above, there is y with a ^ n - b ^ n = y (a - b)
  obtain ⟨y, hy⟩ := HTPI.Exercise_6_1_13 a b n
  rw [hx] at hy
  use x * y
  calc a ^ n - b ^ n
    _ = (d * x) * y := hy
    _ = d * (x * y) := Int.mul_assoc d x y

/-
  let n ∈ ℕ. Show that 4ⁿ ≡₁₅ 1 or 4ⁿ ≡₁₅ 4
-/
example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    -- 4⁰ = 1 which is congruent to 1 mod 15
    left
    numbers
  · -- inductive step
    -- Suppose 4ᵏ ≡₁₅ 1 or Suppose 4ᵏ ≡₁₅ 4.
    -- Prove that 4ᵏ⁺¹ ≡₁₅ 1 or 4ᵏ⁺¹ ≡₁₅ 4
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra

/-
  for all sufficiently large numbers n, 2ⁿ ≥ n²
-/

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    -- 2⁴ ≥ 4².
    numbers
  · -- inductive step
    -- suppose 2ᵏ ≥ k²
    calc 2 ^ (k + 1)
      _ = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra



/-! # Exercises -/

example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k hk
  ·
    numbers
  ·
    -- Suppose 3 ^ k ≥ k ^ 2 + k + 1
    calc  3 ^ (k + 1)
      _ = (3 ^ k) * 3 := by ring
      _ ≥ (k ^ 2 + k + 1) * 3 := by rel [hk]
      _ = (k + 1) ^ 2 + 2 * k ^ 2 + k + 2 := by ring
      _ ≥  (k + 1) ^ 2 + k + 2 := by extra
      _ = (k + 1) ^ 2 + (k + 1) + 1 :=  by ring

-- Bernoulli's inequality
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k hk
  ·
    calc (1 + a) ^ 0
      _ ≥ 1 + 0 * a := by apply Eq.ge; ring
  · -- Induction step. Suppose  (1 + a)ᵏ ≥ 1 + k ⬝ a
    -- Since a ≥ -1, 1 + a is non negative (needed for rel [hk] below)
    have h1: 1 + a ≥ 0 := by addarith [ha]
    calc (1 + a) ^ (k + 1)
      _ = (1 + a) * ((1 + a) ^ k) := by ring
      _ ≥ (1 + a) * (1 + ↑k * a) := by rel [hk] --  Since (1 + a)ᵏ ≥ 1 + k ⬝ a,
      _ = 1 + ↑k * a + a + ↑k * a ^ 2 := by ring
      _ ≥ 1 + ↑k * a + a := by extra  -- k ⬝ a² ≥ 0
      _ = 1 + (↑k + 1) * a := by ring

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k hk
  ·
    left; numbers
  ·
    obtain h1 | h1 := hk
    · -- Suppose 5ᵏ ≡₈ 1. It will be sufficient to prove 5⁽ᵏ⁺¹⁾ ≡₈ 5
      right
      dsimp [Int.ModEq, . ∣ .] at h1
      --  Since 5ᵏ ≡₈ 1, we can choose c with 5ᵏ - 1 = 8 ⬝ c
      obtain ⟨c, hc⟩ := h1
      use 5 * c
      calc (5: ℤ)  ^ (k + 1) - 5
      --     We can rewrite 5⁽ᵏ⁺¹⁾ - 5 as 5 ⬝ (5ᵏ - 1)
        _ = 5 * (5 ^ k) - 5 * 1 := by ring
      --      and, since 5ᵏ - 1 = 8 ⬝ c, we have 5⁽ᵏ⁺¹⁾ - 5 = 40 ⬝ c
        _ = 5 * (5 ^ k - 1) := by rw[Int.mul_sub 5 (5 ^ k) 1]
        _ = 5 * (8 * c) := by rw [hc]
      --      which is divisible by 8
        _ = 8 * (5 * c) := by ring
      -- Thus 5⁽ᵏ⁺¹⁾ ≡₈ 5
    · -- suppose 5ᵏ ≡₈ 5. It will be sufficient to prove 5⁽ᵏ⁺¹⁾ ≡₈ 1
      left
      -- Since 5ᵏ ≡₈ 5, we can choose c with 5ᵏ = 8 ⬝ c + 5
      obtain ⟨c, hc⟩ := h1
      have h2: 5 ^ k = 8 * c + 5 := by addarith [hc]
      use 5 * c + 3
      calc (5: ℤ) ^ (k + 1) - 1
      --    Since we can rewrite 5⁽ᵏ⁺¹⁾ as 5 ⬝ 5ᵏ,
        _ = 5 * (5 ^ k) - 1 := by ring
      --    and can substitute 8 ⬝ c + 5 for 5ᵏ,
        _ = 5 * (8 * c + 5) - 1 := by rw [h2]
      --    we have 5⁽ᵏ⁺¹⁾ = 40 ⬝ c + 24, which is divisible by 8
        _ = 8 * (5 * c + 3) := by ring
      --  Thus 5⁽ᵏ⁺¹⁾ ≡₈ 1




example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k hk
  · -- base case
    left; numbers
  · -- inductive step
    obtain h1 | h1 := hk
    ·
      -- Suppose 6ᵏ ≡₇ 1.
      -- It will be sufficient to prove 6ᵏ⁺¹ ≡₇ 6
      right
      -- Since 6ᵏ ≡₇ 1, we can choose c with 6ᵏ = 7 ⬝ c + 1
      obtain ⟨c, hc⟩ := h1
      have h2: 6 ^ k = 7 * c + 1 := by addarith [hc]
      use 6 * c
      -- Since 6ᵏ⁺¹ - 6 = 6 ⬝ (6ᵏ - 1),
      calc  (6: ℤ) ^ (k + 1) - 6
        _ = 6 * (6 ^ k) - 6 * 1 := by ring
      -- we can substitute 7 ⬝ c + 1 for 6ᵏ
        _ = 6 * (7 * c + 1) - 6 * 1 := by rw [h2]
      -- Thus 6ᵏ⁺¹ - 6 = 42 ⬝ c, so 6ᵏ⁺¹ ≡₇ 6
        _ = 42 * c := by ring
        _ = 7 * (6 * c) := by ring
    ·
    -- Suppose 6ᵏ ≡₇ 6.
    -- It will be sufficient to prove 6ᵏ⁺¹ ≡₇ 1
      left
      -- Since 6ᵏ ≡₇ 6, we can choose c such that 6ᵏ = 7 ⬝ c + 6
      obtain ⟨c, hc⟩ := h1
      have h3: 6 ^ k = 7 * c + 6 := by addarith [hc]
      use 6 * c + 5
      -- Since 6ᵏ⁺¹ - 1 = 6 ⬝ (7 ⬝ c + 6) - 1 = 42 ⬝ c + 35, = 7 ⬝ (6 ⬝ c + 5)
      -- we see that 6ᵏ⁺¹ ≡₇ 1
      calc (6: ℤ) ^ (k + 1) - 1
        _ = 6 * (6 ^ k) - 1 := by ring
        _ = 6 * (7 * c + 6) - 1 := by rw [h3]
        _ = 42 * c + 35 := by ring
        _ = 7 * (6 * c + 5) := by ring

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  sorry

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  sorry

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  sorry

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  sorry
