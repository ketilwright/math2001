/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.5: A shortcut -/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by addarith [h1]
-- the bad old way:
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc x
    _ = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by numbers


example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by addarith [ha]
-- the bad old way:
example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 :=
  calc a
    _ = a - 2 * b + 2 * b := by ring
    _ = 1 + 2 * b := by rw [ha]
    _ = 2 * b + 1 := Int.add_comm 1 (2 * b)

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by addarith [hy]
    _ = -5 := by addarith [hx]


example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by addarith [h]
-- probably does something like:
example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 :=
  calc t + s * t
    _ = t - (4 - s * t) + 4 := by ring
    _ = t - t + 4 := by rw [←h]
    _ = 0 + 4 := by ring
    _ > 0 := by numbers


example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by addarith [h1]


-- Check that `addarith` can't verify this deduction!
--example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := sorry -- no helpful error message
                                                        -- have to do it manually:
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc w
    _ = (3 * w + 1) / 3 - 1 / 3 := by ring
    _ = 4 / 3 - 1 / 3 := by rw [h1]
    _ = 1 := by ring
