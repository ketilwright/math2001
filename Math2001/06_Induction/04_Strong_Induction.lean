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



-- Doesn't this just follow almost immediately from the fundamental theorem of arithmetic?

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  -- Proof by (strong silent type induction)
  by_cases nParity : Odd n
  · -- Suppose n is odd. Then it has no factors of 2,
    -- so let a = 0 and x = n & we are done
    use 0, n; constructor; apply nParity; ring
  · -- Suppose n is even.
    rw [←even_iff_not_odd] at nParity
    -- Then we can choose c with n = 2 ⬝ c
    obtain ⟨c, hc⟩ := nParity
    -- Since n > 0 and n = 2 ⬝ c thus c > 0
    have h1: c > 0 := by rw [hc] at hn; cancel 2 at hn
    -- Since 0 < c < n, we can appeal to the induction hypothesis and
    -- choose a, x ∈ N with x odd and c = 2ᵃ ⬝ x
    have ih: ∃ a x, Odd x ∧ c = 2 ^ a * x := extract_pow_two c h1
    obtain ⟨a, x, h2, h3⟩ := ih
    -- Then since n = 2 ⬝ c ∧ c = 2ᵃ ⬝ x, we have
    -- n = 2ᵃ⁺¹ ⬝ x so a + 1 and x are our witnesses.
    use a + 1, x
    constructor
    · apply h2
    · calc n
        _ = 2 * c := hc
        _ = 2 * (2 ^ a * x) := by rw [h3]
        _ = 2 ^ (a + 1) * x := by ring
