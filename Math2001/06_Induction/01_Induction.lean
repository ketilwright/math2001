/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

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


example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
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


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    sorry
  · -- inductive step
    sorry


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

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
