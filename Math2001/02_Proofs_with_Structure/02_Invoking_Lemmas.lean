/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt -- goal becomes 0 < y² + 1
  calc 0
    _ ≤ y ^ 2 := by extra
    _ = y ^ 2 + 0 := by ring -- is this step really necessary?
    _ < y ^ 2 + 1 := by extra

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra -- satisfies 0 ≤ a²


/-! # Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  have h1 :=
    calc m
      _ = m + 1 - 1 := by ring
      _ = 5 - 1 := by rw[hm]
      _ = 4 := by numbers
  have h2 :=
    calc 3 * m
      _ = 3 * 4 := by rw [h1]
      _ = 12 := by ring
  rw [h2]; /-12 ≠ 6 -/ numbers


example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  sorry
