/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5 * a - 3 * n
  calc n
    _ = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring


example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨c, hc⟩ := h1
  use 12 * c - 7 * n
  calc n
    _ = 12 * (3 * n) - 35 * n := by ring
    _ = 12 * (5 * c) - 35 * n := by rw [hc]
    _ = 5 * (12 * c - 7 * n) := by ring

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1 -- m = 8a
  obtain ⟨b, hb⟩ := h2 -- m = 5b
  -- -3 * 5 + 2 * 8 = 1
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring



/-! # Exercises -/

example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 2 * n - a
  calc n
    _ = 12 * n - 11 * n := by ring
    _ = 12 * n - 6 * a := by rw [ha]
    _ = 6 * (2 * n - a) := by ring


example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨b, hb⟩ := ha
  use 3 * b - 2 * a
  calc a
    _ = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * b) - 14 * a := by rw [hb]
    _ = 7 * (3 * b - 2 * a) := by ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h1 -- n = 7 * a
  obtain ⟨b, hb⟩ := h2 -- n = 9 * b
  use 4 * b - 3 * a
  calc n
    _ = 4 * (7 * n) - 3 * (9 * n) := by ring
    _ = 4 * (7 * (9 * b)) - 3 * (9 * n) := by rw [hb]
    _ = 4 * (7 * (9 * b)) - 3 * (9 * (7 * a)) := by rw [ha]
    _ = 63 * (4 * b - 3 * a) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha⟩ := h1 -- n = 5 * a
  obtain ⟨b, hb⟩ := h2 -- n = 13 * b
  use 8 * b - 3 * a
  calc n
    _ = 8 * 5 * n - 3 * 13 * n := by ring
    _ = 8 * 5 * (13 * b) - 3 * 13 * n := by rw [hb]
    _ = 8 * 5 * (13 * b) - 3 * 13 * (5 * a) := by rw [ha]
    _ = 65 * (8 * b - 3 * a) := by ring
