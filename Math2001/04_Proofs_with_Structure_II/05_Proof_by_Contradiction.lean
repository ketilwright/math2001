/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H -- Suppose 3 ∣ 13, goal becomes "False"
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · -- Suppose k ≥ 5
    have h :=
      calc 13 = 3 * k := hk
        _ ≥ 3 * 5 := by rel [h5]
        _ = 15 := by ring
    numbers at h



example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  -- Suppose both x, y > 0
  intro h -- h
  obtain ⟨hx, hy⟩ := h -- splits conjunction at h
  have H :=
    calc 0 = x + y := by rw [h]
      -- my OCD requires I sniff out what "extra" is doing
      _ > 0 + y := by rel [hx]
      _ > 0 + 0 := by rel [hy]
      _ = 0 := by numbers
    --_ > 0 := by extra
  numbers at H

-- Prove there is no natural number whose square is 2
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  -- Suppose there is n ∈ ℕ with n² = 2
  intro h
  obtain ⟨n, hn⟩ := h
  -- either n ≤ 1 or n ≥ 2
  obtain h1 | h2 := le_or_succ_le n 1
  · -- suppose n ≤ 1
    -- Then 2 ≤ 1², a contradiction
    have h3:=
      calc 2
        _ = n ^ 2 := by rw [hn]
        _ ≤ 1 ^ 2 := by rel [h1]

    numbers at h3
  · -- suppose n ≥ 2
    have h4:=
      calc 2
        _ = n ^ 2 := by rw [hn]
        _ ≥ 2 ^ 2 := by rel [h2]
    numbers at h4

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction

-- no contrapositive support? (yet?)
example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · -- (→)
    intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h3 :=
      calc 0 ≡ n [ZMOD 2] := by rel [h2]
          _ ≡ 1 [ZMOD 2] := by rel [h1]
    numbers at h3
  · -- (←)
    intro h4
    obtain h5 | h5 := Int.even_or_odd n
    ·
      contradiction
    ·
      apply h5

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h0 := -- original eclipses outer scope h
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h0 -- contradiction!
  · -- suppose n ≡ 1 [ZMOD 3]
    have h1 :=
      calc (1: ℤ) = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h1
  · -- suppose n % 3 = 2: ie n ≡ 2 [ZMOD 3]
    have h3:=
      calc 1
        _ ≡ 4 [ZMOD 3] := by use -1; numbers
        _ = 2 ^ 2 := by ring
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := h
    numbers at h3


example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  -- since p = k ⬝ l, k divides p
  have hk : k ∣ p
  · use l
    apply hkl
  -- Suppose for a contradiction that p is prime
  intro h
  -- Then ∀ m ∈ ℕ, m ∣ p → m = 1 ∨ m = p
  obtain ⟨h2, hfact⟩ := h
  -- by UI on the above and k | p, either k = 1 or k = p
  have h3: k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := h3
  ·
    -- Suppose k = 1. But we were given k ≠ 1
    contradiction
  ·
    -- Suppose k = p. But we were given k ≠ p
    contradiction

/-
  Let a, b be integers. If there exists q ∈ Z with bq < a < b(q + 1)
  then b does not divide a
-/
example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  -- Suppose for a contradiction that b ∣ a
  intro H
  -- then there is k such that a = kb
  obtain ⟨k, hk⟩ := H
  -- From the given, we can choose q ∈ ℤ with
  -- bq < a and a < b(q + 1)
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  -- Since bq < a and a < b(q + 1) it follows that b > 0
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  -- Since a = bk and a < b(q + q), we have bk < b(q + 1)
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  -- Thus k < q + 1
  cancel b at h1
  -- We next observe that bq = bk
  have h2 :=
    calc b * q
      _ < a := hq₁
      _ = b * k := hk
  -- And, since b > 0, thus q < k
  cancel b at h2
  -- But we already know k < q + 1, so q ≥ k & thus ¬ q < k, contradicting q < k
  have h3: ¬ q < k := by addarith [h1]
  contradiction


example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  -- let m ∈ ℕ be arbitrary, and assume 1 < m and m < p
  intro m hm1 hmp
  -- we know that either m < T or m ≥ T
  obtain hmT | hmT := lt_or_le m T
  · -- Suppose m < T
    -- Then since ∀ m ∈ N, 1 < m ∧ m < T → ¬ m ∣ p and 1 < m and m < T, ¬ m ∣ p
    apply H m hm1 hmT
  · -- Suppose T ≤ m, and (for a contradiction) that m ∣ p
    intro h_div
    -- Since m ∣ p, there is l ∈ ℕ with p = m ⬝ l
    obtain ⟨l, hl⟩ := h_div
    -- Since p = m ⬝ l, l divides p
    have h_l_div_p: l ∣ p
    ·
      use m;
      calc p
        _ = m * l := hl
        _ = l * m := by ring
    --  Since m < p = m ⬝ l thus 1 < l
    have hl1 :=
      calc m * 1 = m := by ring
        _ < p := hmp
        _ = m * l := hl
    cancel m at hl1
    -- We claim that 1 < l.
    have hl2 : l < T
    ·
    --   To see why, note that since T ≤ m, Tl ≤ ml = p < T²
    --   Thus we have T ⬝ l < T² and l < T
      have hl_lt_T:=
        calc T * l
          _ ≤ m * l := by rel [hmT]
          _ = p := by rw [hl]
          _ < T ^ 2 := by rel [hTp]
          _ = T * T := by ring
      cancel T at hl_lt_T
    -- Finally, since ∀ m ∈ N, 1 < m ∧ m < T → ¬ m ∣ p and 1 < l and l < T, ¬ l ∣ p
    -- which contradicts l ∣ p
    have : ¬ l ∣ p := H l hl1 hl2
    contradiction
    -- Since m ∣ p results in l ∣ p ∧ ¬ l ∣ p, ¬ m ∣ p


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, ht⟩ := h
  obtain ⟨h1, h2⟩  := ht
  have h3:=
    calc t
      _ ≤ 4 := h1
      _ < 5 := by numbers
  have h4: ¬ t < 5 := not_lt.mpr h2
  contradiction


example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨h1, h2⟩ := ha

  obtain h4 | h4 := lt_or_ge a 0
  · -- Suppose a < 0.

    have h5: a ^ 2 > 0 := sq_pos_of_neg h4
    have h6:=
      calc a
        _ < 0 := h4
        _ < 1 := by numbers

    have h7:=
      calc a ^ 3
        _ = a * a ^ 2 := by ring
        _ < 1 * (a ^ 2) := by rel [h6]
        _ = a ^ 2 := by ring
    have h8:=
      calc 8
        _ ≥ a ^ 2 := h1
        _ > a ^ 3 := h7
        _ ≥ 30 := h2

    numbers at h8

  · -- suppose a ≥ 0

    have h9:=
      calc a * a
        _ = a ^ 2 := by ring
        _ ≤ 8 := h1
        _ < 3 * 3 := by numbers
    have h10: (0: ℝ) ≤ 3 := by numbers
    have h11: a < 3 := (mul_self_lt_mul_self_iff h4 h10).mpr h9
    have h12:=
      calc a ^ 3
        _ < 3 ^ 3 := by rel [h11]
        _ = 27 := by ring
    have h13:=
      calc 27
        _ > a ^ 3 := h12
        _ ≥ 30 := h2
    numbers at h13



example : ¬ Int.Even 7 := by
  -- Since 7 is odd it can't be even.
  have h1: Int.Odd 7 := by use 3; ring
  rw [odd_iff_not_even 7] at h1
  apply h1

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have h3: n = 4 := by addarith [hn]
  have h4:=
    calc 10
      _ = n ^ 2 := by rw [h2]
      _ = 4 ^ 2 := by rw [h3]
      _ = 16 := by numbers
  numbers at h4

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry
example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  sorry

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

example : ¬ Prime 1 := by
  sorry

example : Prime 97 := by
  sorry
