/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

-- Let x and y ∈ ℝ, with 0 < xy and 0 ≤ x. Show 0 < y
example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  -- y is either ≤ or > 0
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- Suppose  `y ≤ 0`
    -- Then since x ≥ 0, ¬ xy > 0
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    -- But this contradicts h
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!



example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  -- Consider the cases of n % 3
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    -- Suppose n % 3 = 1
    have h42: 3 ∣ n - 1 := h
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


#check Int.not_dvd_of_exists_lt_and_lt
#check Nat.not_dvd_of_exists_lt_and_lt
#check Nat.pos_of_dvd_of_pos
/-
Nat.pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m
-/
--#check Nat.le_of_dvd
--#check Int.le_of_dvd
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    -- Since m | p, we consider m < p
    obtain h3 | h3 := eq_or_lt_of_le (Nat.le_of_dvd hp' hmp)
    ·
      -- suppose m = p. Then we're done
      right; apply h3
    ·
      -- Suppose m < p
      -- Then by H, and also 1 < m. we have the contradiction ¬ m | p
      -- with hmp
      have h6: ¬ m ∣ p := by apply H m hm_left h3
      contradiction


example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  -- Either a ≤ 2 or a ≥ 3
  obtain h1 | h1 := le_or_succ_le a 2
  · -- Suppose a ≤ 2
    -- Either b ≤ 1 or b ≥ 2
    obtain h2 | h2 := le_or_succ_le b 1
    · -- Suppose b ≤ 1
      -- Then we know c² < 3², so c < 3
      have h3:=
        calc c ^ 2
          _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [h1, h2]
          _ < 3 ^ 2 := by numbers
      cancel 2 at h3
      -- we have a = 1 ∨ a = 2
      -- we have b = 1
      have h4: b = 1 := by exact Nat.le_antisymm h2 hb
      rw [h4] at h_pyth
      -- we have c \ 1 ∨ c = 2
      interval_cases a
      interval_cases c
      ·
        numbers at h_pyth
      ·
        numbers at h_pyth
      ·
        interval_cases c
        ·
          numbers at h_pyth
        ·
          numbers at h_pyth

    · -- Suppose b ≥ 2
      have h6:=
        calc b ^ 2
          _ < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := h_pyth
      cancel 2 at h6
      have h7: b + 1 ≤ c := h6
      have h8:=
        calc c ^ 2
          _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel [h1]
          _ = b ^ 2 + 2 * 2 := by ring
          _ ≤ b ^ 2 + 2 * b := by rel [h2]
          _ = b ^ 2 + 2 * b + 0 := by ring
          _ < b ^ 2 + 2 * b + 1 := by extra
          _ = (b + 1) ^ 2 := by ring
      cancel 2 at h8 -- c < b + 1
      -- We reach a contradiction with b + 1 ≤ c and b + 1 > c
      rw [←Nat.not_le] at h8
      contradiction
  ·
    -- Suppose 3 ≤ a. Then we're done
    apply h1




/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  sorry

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  sorry

example : Prime 7 := by
  sorry

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  sorry

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  sorry
