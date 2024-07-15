/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

open Nat


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by numbers
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by numbers
  | k + 2  =>
      -- note we can refer to the outer name of the
      -- theorem for values < k + 2
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
        _ = 2 ^ (k + 2) := by ring


namespace Nat

theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n
  . -- case 1: `n` is prime
    use n
    constructor
    · apply hn
    · use 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn -- inductive hypothesis
    obtain ⟨p, hp, y, hy⟩ := IH
    use p
    constructor
    · apply hp
    · use x * y
      calc n = m * x := hx
        _ = (p * y) * x := by rw [hy]
        _ = p * (x * y) := by ring

/-! # Exercises -/

/-
  Show that for all natural numbers n > 0, there exists a, x ∈ ℕ, with x odd | n = 2ᵃ ⬝ x
-/
theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  by_cases hnPrime : Prime n
  ·
    --dsimp [Prime] at hn
    obtain ⟨h1, h2⟩ := hnPrime
    by_cases h3: n > 2
    · -- suppose n > 2

      use 0; use n
      constructor
      · -- Since n > 2 and prime, n is odd
        have h4: ¬Even n := by
          intro hContra
          obtain h5 | h5 := (h2 2) hContra
          · numbers at h5
          ·
            have h6: 2 ≠ n := ne_of_lt h3
            contradiction
        apply (odd_iff_not_even n).mpr h4
      · -- n = 2⁰⬝ n
        ring
    ·
      use 1; use 1
      constructor
      · use 0; numbers
      · calc n
          _ = 2 := by
            rw [Nat.not_lt] at h3
            apply Nat.le_antisymm h3 h1
          _ = (2 ^ 1) * 1 := by ring
  · -- Suppose n is not prime
    by_cases h7: n ≥ 2
    · -- Since n ≥ 2, and not prime, choose some m, c ∈ ℕ with n = m ⬝ c and m ≥ 2
      obtain ⟨m, h8, h9, ⟨c, hc⟩⟩ := exists_factor_of_not_prime hnPrime h7
      -- and since m ≥ 2, we can choose some prime factor p of m
      obtain ⟨p, ihp1, ihp2⟩ := exists_prime_factor h8
      have h8: 0 < p := by
        obtain ⟨h9, _⟩ := ihp1
        apply zero_lt_of_lt h9

      have h9: ∃ a x, Odd x ∧ p = 2 ^ a * x := by
        apply extract_pow_two; apply h8

      have h10: m ∣ n := by use c; apply hc
      -- have h11: p ∣ n := by exact Nat.dvd_trans ihp2 h10
      obtain ⟨k, hk⟩ := Nat.dvd_trans ihp2 h10

      -- how do I extract a, x from h9?

      --obtain ⟨h10, h11⟩ := ihp1

      --have h12: p > 0 := by exact zero_lt_of_lt h10
      -- have h13: _ := extract_pow_two p h8 ihp1


      sorry
    ·
      use 0; use 1
      constructor
      · use 0; numbers
      · rw [not_le] at h7
        calc n
          _ = 1 := eq_of_le_of_lt_succ hn h7
          _ = 2 ^ 0 * 1 := by numbers
