/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 := -- m + 3 ≤ 9
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1] -- why is rel used here? just h1 works
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1]
  have h4 : r ≤ 3 - s := by addarith [h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h4, h3]
    _ = 3 := by ring

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3 -- sort of "rewrites" t * t = 3 * t ↔ t = 3
                 -- this works since t ≠ 0 from h2
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring -- a ^ 2 ≥ 1 ^ 2
  cancel 2 at h3 -- works with exponents when base non negative

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h1: x ≤ -1 :=
    calc x
      _ = x + 3 - 3 := by ring
      _ ≤ 2 - 3 := by rel [hx]
      _ ≤ -1 := by numbers
  calc y
    _ = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ ≥ 3 - 2 * (-1) := by rel [h1]
    _ > 3 := by numbers

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3: 0 ≤ b + a := by addarith [h1]
  have h4: 0 ≤ b - a := by addarith [h2]
  have h5: 0 ≤ (b + a) * (b - a) := by extra -- must use mul_nonneg h3 h4
  calc a ^ 2
    _ ≤ a ^ 2 + (b + a) * (b - a) := le_add_of_nonneg_right h5
    _ = b ^ 2 := by ring

-- Maybe they're looking for something like this:
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3: 0 ≤ b + a := by addarith [h1]
  have h4: 0 ≤ b - a := by addarith [h2]
  have h5: b ^ 2 - a ^ 2 ≥ 0 :=
    calc b ^ 2 - a ^ 2
      _ = (b + a) * (b - a) := by ring
      _ ≥ 0 := by extra --mul_nonneg h3 h4
  addarith [h5]

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1: b - a ≥ 0 := by addarith [h]
  -- the intermediate steps
  have h2: ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4 = b ^ 3 - a ^ 3 :=
    calc ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4
      _ = ((b - a) * (b ^ 2 - 2 * a * b + a ^ 2 + 3 * b ^ 2 + 6 * a * b + 3 * a ^ 2)) / 4 := by ring
      _ = ((b - a) * (4 * b ^ 2 + 4 * a * b + 4 * a ^ 2)) / 4 := by ring
      _ = b ^ 3 - a ^ 3 := by ring

  calc a ^ 3
    _ ≤ a ^ 3 + ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4 := by extra
    _ = a ^ 3 + (b ^ 3 - a ^ 3) := by rw [← h2]
    _ = b ^ 3 := by ring


/-! # Exercises -/

-- a more convoluted approach than that suggested in math2001
-- TODO: implement her way
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3: x ^ 2 + 4 * x + 4 = 4 * x + 8 := by addarith [h1]
  have h4: x ^ 2 + 4 * x + 4 = (x + 2) * (x + 2) := by ring
  have h5: 4 * x + 8 = (2 + 2) * (x + 2) := by ring
  rw [h4, h5] at h3
  have h6: 1 + 2 < x + 2 := by rel [h2]
  have h7:=
    calc x + 2
      _ > 1 + 2 := by rel [h2]
      _ > 0 := by numbers
  cancel (x + 2) at h3
  calc x
    _ = x + 2 - 2 := by ring
    _ = 2 + 2 - 2 := by rw [h3]
    _ = 2 := by numbers

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 :=
    calc (n - 2) ^ 2
      _ = n ^ 2 + 4 - 4 * n:= by ring
      _ = 4 * n - 4 * n := by rw [hn]
      _ = 0 := by ring
  calc n
    _ = n - 2 + 2 := by ring
    _ = 0 + 2 := by rw [pow_eq_zero h1] -- xⁿ = 0 → x = 0
    _ = 2 := by ring


example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  --have h1: 0 < 1 := by numbers
  have h3: 0 < x * y := by exact Eq.trans_gt (id h.symm) rfl
  cancel x at h3
  have h4: ¬ x = 0 := by exact left_ne_zero_of_mul_eq_one h
  calc y
    _ = x * y / x := by exact CancelDenoms.cancel_factors_eq_div rfl h4
    _ = 1 / x := by rw [h]
    _ ≤ 1 := by exact div_le_self rfl h2
