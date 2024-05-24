/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  -- for future ref: type \< for  ⟨ and \> for ⟩
  obtain ⟨h1, h2 ⟩ := hp'
  calc p
    _ ≥ -3 := h1
    _ ≥ - 5 := by numbers


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra --  a² nonnegative

  have h3:=
    calc a * a
      _ = a ^ 2 := by ring
      _ = 0 := h2
  have h4:=
    calc b * b--b ^ 2
      _ = a ^ 2 + b ^ 2 - a ^ 2 := by ring
      _ = 0 - a ^ 2 := by rw [h1]
      _ = 0 - (0) := by rw [h2]
      _ = 0 := by ring
  constructor


  obtain h5 | h5 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  apply h5; apply h5
  obtain h6 | h6 := eq_zero_or_eq_zero_of_mul_eq_zero h4
  apply h6; apply h6


/-! # Exercises -/
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc 2 * a + b
    _ = a + b + a := by ring
    _ ≤ 3 + a := by rel [h2]
    _ ≤ 3 + 1 := by rel [h1]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc 2 * r
    _ = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [h1, h2]
    _ = 6 := by ring


example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc m
    _ = m + 5 - 5 := by ring
    _ ≤ n - 5 := by rel [h2]
    _ ≤ 8 - 5 := by rel [h1]
    _ = 3 := by ring

-- Must be missing something here. This is about the 3rd time
-- I have a proof which repeats itself verbatim on a conjunction

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by

  have hp1 :=
    calc p
      _ = p + 2 - 2 := by ring
      _ ≥ 9 - 2 := by rel [hp]
      _ = 7 := by ring

  obtain h1 | h1 := LE.le.eq_or_gt hp1
  constructor -- p² ≥ 49
  calc p ^ 2
    _ ≥ 7 ^ 2 := by rel [hp1]
    _ = 49 := by ring
  apply hp1

  constructor -- p² ≥ 49
  calc p ^ 2
    _ ≥ 7 ^ 2 := by rel [hp1]
    _ = 49 := by ring
  apply hp1


example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have ha :=
    calc a
      _ = a - 1 + 1 := by ring
      _ ≥ 5 + 1 := by rel [h]
      _ = 6 := by ring
  obtain h1 | h1 := LE.le.eq_or_gt ha
  constructor
  apply ha
  calc 3 * a
    _ = 3 * 6 := by rw [←h1]
    _ ≥ 10 := by numbers
  constructor
  apply ha
  calc 3 * a
    _ ≥ 3 * 6 := by rel [h1]
    _ = 18 := by numbers
    _ ≥ 10 := by numbers


example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have hy :=
    calc y
      _ = (x + 2 * y) - (x + y) := by ring
      _ = 7 - 5 := by rw [←h2, ←h1]
      _ = 2 := by ring
  constructor
  addarith [h1, hy]
  apply hy

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by

  -- Clearly a = b from h1 & h2
  have h3 :=
    calc a
      _ = a * b := by rw [h1]
      _ = b := by rw [h2]
  -- Either a = 0 or a ≠ 0
  obtain ha | ha := eq_or_ne a 0
  -- Suppose a = 0. Then since a = b, b = 0 & we're done with the case a = 0
  left
  constructor
  apply ha
  calc b
    _ = 0 := by rw [←h3, ha]
  -- Suppose a ≠ 0.
  right
  -- Then since a = b, b ≠ 0
  have h4:=
    calc b
      _ = a := by rw [←h3]
      _ ≠ 0 := ha
  -- Since a * b = a, a b = a * 1
  have h5:=
    calc a * b
      _ = a := h1
      _ = a * 1 := by ring
  -- Since a = b, we have b * b = b * 1, and since
  -- b ≠ 0 divide both sides by b to have b = 1
  rw [h3] at h5
  cancel b at h5
  constructor
  calc a
    _ = b := h3
    _ = 1 := h5
  apply h5
