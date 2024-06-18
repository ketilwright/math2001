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
  cancel n at h -- appears to be enough, since h is now y ≤ x

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  -- ∃ c ∈ ℤ | n ^ 2 - 4 = 5c
  obtain ⟨c, hc⟩ := hn
  -- We evaluate the cases of n % 5 = 0, 1, 2, 3, 4
  mod_cases hMod: n % 5
  · -- suppose n ≡₀ 5
    -- Then there is d ∈ ℤ | n = 5 ⬝ d
    obtain ⟨d, hd⟩ := hMod -- n - 0 = 5 * d
    ring_nf at hd -- converts n - 0 to n (& also reverse 5 & d :-( )
    -- Substituting 5d for n in n² ≡₅ 4 we have
    -- 5 ∣ 25d² - 4. Since 5 ∣ 25d², 5 must also divide -4
    have h1:=
      calc 25 * d ^ 2 - 4
        _ = (d * 5) ^ 2 - 4 := by ring
        _ = n ^ 2 - 4 := by rw [hd]
        _ = 5 * c := hc
    have h2: 5 ∣ 25 * d ^ 2 - 4 := by use c; apply h1
    have h3: 5 ∣ 25 * d ^ 2 := by use 5 * d ^ 2; ring
    apply (Int.dvd_add_right h3).mp at h2
    -- But since ¬ 5 ∣ (-4), we reach a contradiction.
    have h5: ¬ 5 ∣ (-4) := by
      apply Int.not_dvd_of_exists_lt_and_lt
      use -1
      constructor; numbers; numbers
    contradiction
  · -- suppose n ≡₁ 5
    obtain ⟨d, hd⟩ := hMod -- n - 1 = 5 * d
    have h6: n = 5 * d + 1 := by addarith [hd]
    have h7:=
      calc 25 * d ^ 2 + 10 * d - 3
        _ = (5 * d + 1) ^ 2 - 4 := by ring
        _ = n ^ 2 - 4 := by rw [h6]
        _ = 5 * c := hc
    have h8 : 5 ∣ 25 * d ^ 2 + 10 * d - 3 := by use c; apply h7
    have h9 : 5 ∣ 25 * d ^ 2 + 10 * d := by use 5 * d ^ 2 + 2 * d; ring
    apply (Int.dvd_add_right h9).mp at h8
    have h10: ¬ 5 ∣ (-3) := by
      apply Int.not_dvd_of_exists_lt_and_lt
      use -1
      constructor; numbers; numbers
    contradiction
  · -- suppose n ≡₂ 5
    left; apply hMod
  · -- suppose n ≡₃ 5
    right; apply hMod
  · -- suppose n ≡₄ 5
    obtain ⟨d, hd⟩ := hMod -- n - 4 = 5 * d
    have h11: n = 5 * d + 4 := by addarith [hd]
    have h12:=
      calc 25 * d ^ 2 + 40 * d + 12
        _ = (5 * d + 4) ^ 2 - 4 := by ring
        _ = n ^ 2 - 4 := by rw [h11]
        _ = 5 * c := hc
    have h13: 5 ∣ 25 * d ^ 2 + 40 * d + 12 := by use c; apply h12
    have h14: 5 ∣ 25 * d ^ 2 + 40 * d := by use 5 * d ^ 2 + 8 * d; ring
    apply (Int.dvd_add_right h14).mp at h13
    have h10: ¬ 5 ∣ (12: ℤ) := by
      apply Int.not_dvd_of_exists_lt_and_lt
      use 2
      constructor; numbers; numbers
    contradiction


example : Prime 7 := by
  apply prime_test
  numbers
  intro m h1_lt_m hm_lt_7
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  ·
    use 3; constructor; numbers; numbers
  ·
    use 2; constructor; numbers; numbers
  ·
    use 1; constructor; numbers; numbers
  ·
    use 1; constructor; numbers; numbers
  ·
    use 1; constructor; numbers; numbers




example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h4 | h4 := h3
  · -- suppose x + 2 = 0
    have h5:=
      calc x
        _ = -2 := by addarith [h4]
        _ ≤ 1 := by numbers
    have h6: ¬ x > 1 := not_lt.mpr h5
    contradiction
  ·
    calc x = 2 := by addarith [h4]



namespace Nat
-- running into trouble N vs Z
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨h1, h2⟩ := h
  obtain h3 | h3  := Nat.lt_or_eq_of_le h1
  ·
    right
    mod_cases h4: (p: ℤ) % 2
    ·
      have h5: 2 ∣ p := Int.ofNat_dvd.mp h4
      have h6: 2 ∣ p → 2 = 1 ∨ 2 = p := by apply h2
      sorry
    ·
      obtain ⟨c, hc⟩ := h4
      sorry


  ·
    left; apply h3.symm
