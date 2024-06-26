/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h -- (→)
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h -- (←)
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h -- n = 2 * k + 1
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h -- n ≡ 1 [ZMOD 2]
    obtain ⟨k, hk⟩ := h -- n - 1 = 2 * k
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    addarith [hk]


example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  ·
    intro h -- assume x² + x - 6 - 0
    have h1:=
      calc (x + 3) * (x - 2)
        _ = x ^ 2 + x - 6 := by ring
        _ = 0 := h

    obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    left; addarith [h2];
    right; addarith [h2]
  ·
    intro h
    obtain h2 | h2 := h
    calc x ^ 2 + x - 6
      _ = (-3) ^ 2 + (-3) - 6 := by rw [h2]
      _ = 0 := by numbers
    calc x ^ 2 + x - 6
      _ = 2 ^ 2 + 2 - 6 := by rw [h2]
      _ = 0 := by numbers


-- Int.mul_pos_of_neg_of_neg
-- Int.mul_lt_mul_of_neg_right
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · -- ( → )
  -- Suppose a² -5a + 5 ≤ 1
    intro h
  -- then (2a - 5)² ≤ 1 = 1²
    have h1:=
      calc (2 * a - 5) ^ 2
        _ = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel [h]
        _ = 1 ^ 2 := by ring
    /-
      “And” hypotheses turn up relatively rarely in the wild
      One situation in which one might occur is when a single hypothesis has
      two natural consequences, which are paired together in a lemma
      For example, if x² ≤ y² for some positive number y, then one can draw
      the conclusion  -y ≤ x ≤ y ( use abs_le_of_sq_le_sq')
    -/
    have h2: (0: ℤ) ≤ 1 ^ 2 := by numbers
    obtain ⟨h3, h4⟩ := abs_le_of_sq_le_sq' h1 h2

    have h5:=
      calc 2 * a
        _ = 2 * a - 5 + 5 := by ring
        _ ≥ -1 + 5 := by rel [h3]
        _ = 2 * 2 := by ring
    have h6: (0: ℤ) < 2 := by numbers
    have h7: 2 ≤ a := le_of_mul_le_mul_left h5 h6
    have h8:=
      calc 2 * a
        _ = 2 * a - 5 + 5 := by ring
        _ ≤ 1 + 5 := by rel [h4]
        _ = 2 * 3 := by ring
    have h9: a ≤ 3 := le_of_mul_le_mul_left h8 h6
    obtain h10 | h10 := lt_or_eq_of_le h7
    ·
      -- suppose a > 2
      right; apply Int.le_antisymm h9 h10
    ·
      -- a = 2
      left;
      apply h10.symm
  · -- ( ← )
    intro h11
    obtain h12 | h12 := h11
    ·
      -- suppose a = 2
      calc a ^ 2 - 5 * a + 5
        _ = 2 ^ 2 - 5 * 2 + 5 := by rw [h12]
        _ = -1 := by ring
        _ ≤ -1 := by extra
    ·
      -- suppose a = 3
      calc a ^ 2 - 5 * a + 5
        _ = 3 ^ 2 - 5 * 3 + 5 := by rw [h12]
        _ = -1 := by ring
        _ ≤ -1 := by extra

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain h3 | h3 := hn2
  have h4: n = 4 := by addarith [h3]
  use 2; rw [h4]; numbers
  have h5: n = 6 := by addarith [h3]
  use 3; rw [h5]; numbers


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h2 | h2 := hn1
  have h3: n = 4 := by addarith [h2]
  use 2; rw [h3]; numbers
  have h4: n = 6 := by addarith [h2]
  use 3; rw [h4]; numbers

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at * --  x + y + 1 ≡ 1 [ZMOD 2]

  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · -- →
    intro hx -- 2 * x - 1 = 11
    calc x
      _ = 2 * x / 2 := by ring
      _ = 12 / 2 := by addarith [hx]
      _ = 6 := by ring
  · -- ←
    intro hx
    rw [hx]; numbers


example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · -- →
    intro hn
    obtain ⟨j, hj⟩ := hn
    constructor
    · -- 7 | n
      use 9 * j
      calc n
        _ = 63 * j := hj
        _ = 7 * (9 * j) := by ring
    · -- 9 | n
      use 7 * j
      calc n
        _ = 63 * j := hj
        _ = 9 * (7 * j) := by ring
  · -- ←
    intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a, ha⟩ := h1 -- n = 7a
    obtain ⟨b, hb⟩ := h2 -- n = 9b
    use 4 * b - 3 * a
    calc n
      _ = 7 * 4 * n - 9 * 3 * n := by ring
      _ = 7 * 4 * (9 * b) - 9 * 3 * n := by rw [hb]
      _ = 7 * 4 * (9 * b) - 9 * 3 * (7 * a) := by rw [ha] -- why can't we combine in 1 step??
      _ = 63 * (4 * b - 3 * a) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · -- →
    intro h
    obtain ⟨x, hx⟩ := h
    use x
    calc a - 0
      _ = a := by ring
      _ = n * x := hx
  · -- ←
    intro h
    obtain ⟨x, hx⟩ := h
    use x
    calc a
      _ = a - 0 := by ring
      _= n * x := hx

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨c, hc⟩ := hab
  use 2 * a ^ 2 * c ^ 3 - a * (c ^ 2) + 3 * c
  calc  2 * b ^ 3 - b ^ 2 + 3 * b
    _ = 2 * (a * c) ^ 3 - (a * c) ^ 2 + 3 * (a * c) := by rw [hc]
    _ = a * (2 * a ^ 2 * c ^ 3 - a * c ^ 2 + 3 * c) := by ring

-- alternativly: make use of n ∣ a ↔ a ≡ₙ 0
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  -- since a ∣ b, and b divides each term in the goal expression
  obtain ⟨c, hc⟩ := hab
  have h1: a ∣ 2 * b ^ 3 := by
    use 2 * a ^ 2 * c ^ 3
    calc 2 * b ^ 3
      _ = 2 * (a * c) ^ 3 := by rw [hc]
      _ = a * (2 * a ^ 2 * c ^ 3) := by ring
  rw [dvd_iff_modEq] at h1
  have h2: a ∣ - b ^ 2 := by
    use - a * c ^ 2
    calc -b ^ 2
      _ = - (a * c) ^ 2 := by rw [hc]
      _ = a * (-a * c ^ 2) := by ring
  rw [dvd_iff_modEq] at h2
  have h3: a ∣ 3 * b := by
    use 3 * c
    calc 3 * b
      _ = 3 * (a * c) := by rw [hc]
      _ = a * (3 * c) := by ring
  rw [dvd_iff_modEq] at h3
  have h4: a ∣ 2 * b ^ 3 - b ^ 2 := by
    rw [dvd_iff_modEq];
    apply Int.ModEq.add h1 h2
  have h5: a ∣ (2 * b ^ 3 - b ^ 2) + 3 * b := by
    rw [dvd_iff_modEq]
    rw [dvd_iff_modEq] at h4
    apply Int.ModEq.add h4 h3
  apply h5


example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  ·
    intro hk
    -- we have k² ≤ 6 < 3²
    have h1:=
      calc k ^ 2
        _ ≤ 6 := hk
        _ < 3 ^ 2 := by numbers
    -- Since k² < 9, k < 3
    --apply lt_of_pow_lt_pow' 2 at h1 -- abs_le_of_sq_le_sq doesn't work here. Probably because of ℕ
    -- hmmm. See section 2.1.5
    cancel 2 at h1 -- section 2.1.5: cancel works on exponents.
    -- Since k ∈ ℕ < 3, we are done
    interval_cases (k)
    left; numbers
    right; left; numbers
    right; right; numbers
  ·
    intro hk
    obtain h1 | h1 := hk
    calc k ^ 2
      _ = 0 ^ 2 := by rw [h1]
      _ ≤ 6 := by numbers
    obtain h2 | h2 := h1
    calc k ^ 2
      _ = 1 ^ 2 := by rw [h2]
      _ ≤ 6 := by numbers
    calc k ^ 2
      _ = 2 ^ 2 := by rw [h2]
      _ ≤ 6 := by numbers
