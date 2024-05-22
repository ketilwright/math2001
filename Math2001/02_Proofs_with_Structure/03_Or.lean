/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  -- splits h into statements hx and hy
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  -- It's exhaustive to consider the cases
  -- (1) n ≤ 1 and (2) 2 ≤ n
  have hn := le_or_succ_le n 1
  -- note hn on both sides of |. How clever.
  obtain hn | hn := hn
  -- 1) suppose n ≤ 1
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  -- 2) suppose n ≥ 2
  apply ne_of_gt -- lean reverses the inequality (which doesn't appear to matter)
  calc n ^ 2
    _ = n * n := by ring
    _ ≥ 2 * 2 := by rel [hn]
    _ > 2 := by numbers
  -- "this exhausts all possible cases & we conclude blah . . ."

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right -- prove right side of disjunct goal (left is false)
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  -- transforms (x - 1)(x - 2) = 0 into x - 1 = 0 ∨ x - 2 = 0
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1

  obtain h2 | h2 := h2
  -- now we have 2 goals / cases on h2
  left
  calc x
    _ = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h2]
    _ = 1 := by numbers
  right
  calc x
    _ = x - 2 + 2 := by ring
    _ = 0 + 2 := by rw [h2]
    _ = 2 := by ring


example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h | h := h
  calc x ^ 2 + 1
    _ = 4 ^ 2 + 1 := by rw [h]
    _ = 17 := by numbers

  calc x ^ 2 + 1
    _ = (-4) ^ 2 + 1 := by rw [h]
    _ = 17 := by numbers

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  -- suppose x = 1
  calc x ^ 2 - 3 * x + 2
    _ = 1 ^ 2 - 3 * 1 + 2 := by rw [h]
    _ = 0 := by ring
  -- suppose x = 2
  calc x ^ 2 - 3 * x + 2
    _ = 2 ^ 2 - 3 * 2 + 2 := by rw [h]
    _ = 0 := by ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h | h := h
  -- suppose t = - 2
  calc t ^ 2 - t - 6
    _ = (-2) ^ 2 - (-2) - 6 := by rw [h]
    _ = 0 := by ring
  -- t = 3
  calc t ^ 2 - t - 6
    _ = 3 ^ 2 - (3) - 6 := by rw [h]
    _ = 0 := by ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h | h := h
  -- suppose x = 2
  calc x * y + 2 * x
    _ = 2 * y + 2 * 2 := by rw [h]
    _ = 2 * y + 4 := by ring
  -- suppose y = -2
  -- then replace y by - 2 & we're done □
  rw [h]; ring


example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc s + t
    _ = 3 - t + t := by rw [h]
    _ = 3 := by ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc b
      _ = (a + 2 * b) / 2 - a / 2 := by ring
      _ < 0 / 2 - a / 2 := by rel [h]
      _ = - a  / 2 := by ring

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc x
    _ = (2 * x + 1) / 2 - 1 / 2 := by ring
    _ = y / 2 - 1 / 2 := by rw [h]
    _ < y / 2 - 1 / 2 + 1 / 2 := by extra
    _ = y / 2 := by ring

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 :=
    calc x ^ 2 + 2 * x - 3
      _ = (x + 3) * (x - 1) := by ring
  rw [h1] at hx
  have h2: x + 3 = 0 ∨ x - 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero hx
  obtain h2 | h2 := h2
  left
  calc x
    _ = x + 3 - 3 := by ring
    _ = 0 - 3 := by rw [h2]
    _ = -3 := by numbers
  right
  calc x
    _ = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h2]
    _ = 1 := by numbers


example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  -- a² + 3ab + 2b² = (a-b)(a-2b)
  have h1 :=
    calc (a - b) * (a - 2 * b)
      _ = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
      _ = 3 * a * b - 3 * a * b := by rw [hab]
      _ = 0 := by ring
  -- obtain a disjunction of the quad
  obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  -- handle case a - b = 0
  left
  calc a
    _ = a - b + b := by ring
    _ = 0 + b := by rw [h2]
    _ = b := by ring
  -- handle case a - 2b = 0
  right
  calc a
    _ = a - 2 * b + 2 * b := by ring
    _ = 0 + 2 * b := by rw [h2]
    _ = 2 * b := by ring

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
    calc (t ^ 2) * (t - 1)
      _ = t ^ 3 - t ^ 2 := by ring
      _ = t ^ 2 - t ^ 2 := by rw [ht]
      _ = 0 := by ring
  -- obtain a disjunction
  obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  right
  -- this is downright silly (pow_eq_zero closes the left side), but I'm trying to
  -- avoid theorems buried in the depths of lean
  obtain h5 | h5 := eq_zero_or_eq_zero_of_mul_eq_zero
    (calc t * t
      _ = t ^ 2 := by ring
      _ = 0 := by rw [h2])
  exact h5; exact h5 -- since h5 is t = 0 ∨ t = 0
  left
  calc t
    _ = t - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h2]
    _ = 1 := by numbers

example {n : ℕ} : n ^ 2 ≠ 7 := by
  -- handle the cases n ≤ 2 or n ≥ 3
  obtain hn | hn := le_or_succ_le n 2
  -- suppose n ≤ 2
  apply ne_of_lt
  calc n ^ 2
    _ = n * n := by ring
    _ ≤ 2 * 2 := by rel [hn]
    _ < 7 := by numbers
  -- suppose n ≥ 3
  apply ne_of_gt
  calc 7
    _ < 3 ^ 2 := by numbers
    _ ≤ n ^ 2 := by rel [hn]


example {x : ℤ} : 2 * x ≠ 3 := by
  obtain hx | hx := le_or_succ_le x 1
  -- case x ≤ 1
  apply ne_of_lt
  calc 2 * x
    _ ≤ 2 * 1 := by rel [hx]
    _ < 3 := by numbers
  -- case 2 ≤ x
  apply ne_of_gt -- 3 < 2 * x
  calc 2 * x
    _ ≥ 2 * 2 := by rel [hx]
    _ > 3 := by numbers

example {t : ℤ} : 5 * t ≠ 18 := by
  obtain ht | ht := le_or_succ_le t 3
  apply ne_of_lt
  calc 5 * t
    _ ≤ 5 * 3 := by rel [ht]
    _ < 18 := by numbers
  apply ne_of_gt
  calc 5 * t
    _ ≥ 5 * 4 := by rel [ht]
    _ > 18 := by numbers



example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
