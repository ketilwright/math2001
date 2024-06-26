/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  use -3
  numbers


example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  -- since a ∣ b, there is k with b = ak
  obtain ⟨k, hk⟩ := hab
  dsimp [(. ∣ .)] -- ∃ c, b ^ 2 + 2 * b = a * c
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by

  obtain ⟨k, hk⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  dsimp [(. ∣ .)]
  -- not discussed (?): from hab we have a ≠ 0, and b ≠ 0 from hbc
  use k ^ 2 * j
  rw [hj, hk]
  ring


example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨k, hk⟩ := h -- z = x * y * k
  use y * k
  rw [hk]
  ring

example : ¬(5 : ℤ) ∣ 12 := by
  -- not lean native
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`

-- Nat.le_of_dvd
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  -- ∃k ∈ ℕ | b = ak
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1 -- OK since ℕ
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]

-- Nat.pos_of_dvd_pos
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk⟩ := hab
  rewrite [hk] at hb
  cancel k at hb


/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  use 0
  ring
example : ¬(3 : ℤ) ∣ -10 := by
  -- equivalent to show there is some x ∈ ℤ
  -- with 3x < -10 and -10 < 3(x + 1)
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  numbers
  numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  use 3 * k - 4 * x * k ^ 2
  rw[hk]
  ring


example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk⟩ := h
  use 2 * m ^ 2 * k ^ 3 + k
  calc 2 * n ^ 3 + n
    _ = 2 * (m * k) ^ 3 + m * k := by rw [hk]
    _ = m * (2 * m ^ 2 * k ^ 3 + k) := by ring


example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use 2 * a ^ 2 * k ^ 3 - k ^ 2 * a + 3 * k
  rw [hk]; ring


example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨x, hx⟩ := h1 -- l = kx
  obtain ⟨y, hy⟩ := h2 -- m = l³y
  use x ^ 3 * y
  calc m
    _ = l ^ 3 * y := by rw [hy]
    _ = (k * x) ^ 3 * y := by rw [hx]
    _ = k ^ 3 * (x ^ 3 * y) := by ring


example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨a, ha⟩ := hpq -- q = p³a
  obtain ⟨b, hb⟩ := hqr -- r = q²b
  use (a ^ 2) * b
  calc r
    _ = q ^ 2 * b := hb
    _ = (p ^ 3 * a) ^ 2 * b := by rw [ha]
    _ = p ^ 6 * (a ^ 2 * b) := by ring

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  -- 0 < 6 and 9 ∣ 63 = 2⁶-1
  use 6
  constructor
  numbers
  use 7
  ring

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  -- 0 < 1 < 2 and 2 - 1 ∣ 2 + 1
  use 2; use 1
  constructor
  numbers
  constructor
  numbers
  use 3
  ring
