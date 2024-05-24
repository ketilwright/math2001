/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

--#check ne_of_lt
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  ·
    -- sufficient to show t < 0
    apply ne_of_lt
    calc t
      _ = x * t / x := by
        calc t
          _ = t * 1 := by ring
          -- since x > 0 thus x ≠ 0 so x / x = 1
          _ = t * (x / x) := by rw [div_self (ne_of_gt hx)]
          _ = x * t / x := by ring
      _ < 0 / x := by rel [hxt]
      _ = 0 := by ring


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6; use 5; numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1; use a;
  --just ring works, but where's the fun in that?
  calc (a + 1) ^ 2 - a ^ 2
    _ = a ^ 2 + 2 * a + 1 - a ^ 2 := by ring
    _ = 2 * a + 1 := by ring


example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  calc p
    _ = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  calc (p + q) / 2
    _ < (q + q) / 2 := by rel [h]
    _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3; ring
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6; use 7; ring

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0; use 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have hx : x ^ 2 ≥ 0 := by extra
  obtain h | h := le_or_gt x 0
  -- suppose x ≤ 0
  -- Then choose (x²+ 1)², which is > x
  use x ^ 2 + 1;
  calc (x ^ 2 + 1) ^ 2
    _ = x ^ 4 + 2 * x ^ 2 + 1 := by ring
    _ ≥ 1 := by extra
    _ > 0 := by numbers
    _ ≥ x := by rel [h]
  -- Suppose x > 0
  use x + 1
  -- Since x > 0, 2x > x
  have h2x:=
    calc 2 * x
      _ = x + x := by ring
      _ > x + 0 := by rel [h]
      _ = x := by ring
  -- x² ≥ 0 and 2x > x, thus (x+1)² > x
  calc (x + 1) ^ 2
    _ = x ^ 2 + 2 * x + 1 := by ring
    _ > x ^ 2 + x + 1 := by rel [h2x]
    _ ≥ 0 + x + 1:= by rel [hx]
    _ = x + 1 := by ring
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
