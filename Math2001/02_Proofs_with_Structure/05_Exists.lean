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

-- I found it necessary to go "outside" of math2001 & use
-- a few tricks I learned in HTPIwL
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  -- obtain a with a ⬝ t + 1 < a + t
  obtain ⟨a, ha ⟩ := h
  -- Since we know a ⬝ t + 1 < a + t, it follows
  -- that (a - 1) ⬝ (t - 1) ≠ 0.
  have h1: (a - 1) * (t - 1) ≠ 0 := by
  -- It's sufficient to prove (a - 1)(t - 1) < 0
    apply ne_of_lt
    calc (a - 1) * (t - 1)
      _ = a * t + 1 - (a + t) := by ring
      _ < 0 := by addarith [ha]
  -- Thus, in particular t - 1 ≠ 0
  have h2: t - 1 ≠ 0 := by exact right_ne_zero_of_mul h1

  -- And clearly then t ≠ 1
  calc t
    _ = (t - 1) + 1 := by ring
    _ ≠ 0 + 1 := by exact (add_ne_add_left 1).mpr h2
    _ = 1 := by ring
  -- BTW: Similar reasoning shows that a ≠ 1


-- I think the previous exercise migh be easier by contrapositive, but that's not
-- discussed yet (ever?)
example {t : ℝ} (h :t = 1) : ¬ ∃ a : ℝ, a * t + 1 < a + t := by
  push_neg
  intro a
  rw [h]
  ring_nf
  apply Eq.ge
  rfl


example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by

  obtain ⟨a, h1⟩ := h
  obtain h2 | h2 := le_or_gt a 2
  -- suppose a ≤ 2.
  -- it's sufficient to prove m < 5
  apply ne_of_lt
  calc m
    _ = 2 * a := by rw [←h1]
    _ ≤ 2 * 2 := by rel [h2]
    _ < 5 := by numbers
  -- suppose a > 2
  --it's sufficient to prove m > 5
  apply ne_of_gt
  have h3: a ≥ 3 := h2
  calc m
    _ = 2 * a := by rw [←h1]
    _ ≥ 2 * 3 := by rel [h3]
    _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
-- since n ∈ ℤ, either n ≤ 0 or n ≥ 1
  obtain h1 | h1 := le_or_succ_le n 0
  -- suppose n ≤ 0
  -- Then either n = 0 or n < 0
  obtain h2 | h2 := eq_or_lt_of_le h1
  -- suppose n = 0
  use 2
  rw [h2]
  numbers
  -- suppose n < 0
  -- Then n - 2 < 0 also
  use (2 - n)
  -- it seems lean works better with < or ≤ than it does with > or ≥
  rw [ge_iff_le]
  rw [le_iff_eq_or_lt]
  right

  have h4: (0: ℤ) < (9: ℤ) := by numbers
  have h7: (12: ℤ) > (-1: ℤ) := by numbers

  have h5:= -- n² > 0 this is awkward, but works
    calc n ^ 2
      _ = (-n) * (-n) := by ring
      _ > (-0) * (-0) := by rel [h2]
      _ = 0 := by ring
  have h6:= -- n³ < 0
    calc n ^ 3
      _ = n * n ^ 2 := by ring
      _ < 0 * n ^ 2 := by rel [h2]
      _ = 0 := by ring
  --have h7: 12 * n ^ 2 > - (n ^ 2) := by

  have h6a: (2: ℤ) > (0: ℤ) := by numbers
  --have h6_ : 2 * (n ^ 3) < 0 := by exact Int.mul_neg_of_pos_of_neg h6a h6
  have h6b: -2 * n ^ 3 > 0 := Int.mul_pos_of_neg_of_neg h6a h6
  have h6c: 0 = 0 * n ^ 3 := by exact (Int.zero_mul (n ^ 3)).symm
  rewrite [h6c] at h6b

  have h8:=
    calc 12 * n ^ 2
      _ > (-1) * n ^ 2 := by rel [h7]
      _ = - (n ^ 2) := by ring

  -- since n < 0, -24n > 2n
  have h9a: -24 < 2 := by numbers
  have h9e: (2: ℤ) * n < (-24: ℤ) * n := by exact Int.mul_lt_mul_of_neg_right h9a h2
  have h10: (-2 * n ^ 3 + 12 * n ^ 2 + 16) + 2 * n  < (-2 * n ^ 3 + 12 * n ^ 2 + 16) + (- 24 * n) := by rel [h9e]


  calc n * (2 - n) + 7
    _ = - n ^ 2 + 2 * n + 7 + 0:= by ring
    _ < - n ^ 2 + 2 * n + 7 + 9 := by rel [h4]
    _ < 12 * n ^ 2 + 2 * n + 7 + 9 := by rel [h8]
    _ = 0 * n ^ 3 + 12 * n ^ 2 + 2 * n + 16 := by ring
    _ < -2 * n ^ 3 + 12 * n ^ 2 + 2 * n + 16 := by rel [h6b]
    _ = (-2 * n ^ 3 + 12 * n ^ 2 + 16) + 2 * n := by ring
    _ < (-2 * n ^ 3 + 12 * n ^ 2 + 16) + (- 24 * n) := by rel [h9e]
    _ = -2 * n ^ 3 + 12 * n ^ 2 - 24 * n + 16  := by ring
    _ = 2 * (2 - n) ^ 3 := by ring
  sorry -- todo: n ≥ 1



example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
