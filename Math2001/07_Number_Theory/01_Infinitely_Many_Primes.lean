/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

namespace Nat

#check dvd_factorial

example (N : ℕ) : ∃ p ≥ N, Prime p := by
  have hN0 : 0 < N ! := by apply factorial_pos
  have hN2 : 2 ≤ N ! + 1 := by addarith [hN0]
  -- `N! + 1` has a prime factor, `p`
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := exists_prime_factor hN2

  have hp2 : 2 ≤ p --term mode!
  · obtain ⟨hp', hp''⟩ := hp
    apply hp'

  obtain ⟨k, hk⟩ := hpN -- N ! + 1 = p * k

  match k with
  | 0 => -- if `k` is zero, contradiction
    have k_contra :=
    calc 0 < N ! + 1 := by extra
      _ = p * 0 := hk
      _ = 0 := by ring
    numbers at k_contra
  | l + 1 => -- so `k = l + 1` for some `l`

    -- the key fact: `p` is not a factor of `N!`
    -- ie. since p divides n ! + 1, it cannot divide n!
    -- a job for not_dvd_of_exists_lt_and_lt
    have key : ¬ p ∣ (N !)
    · apply Nat.not_dvd_of_exists_lt_and_lt (N !)
      use l
      constructor
      · -- prove p ⬝ l < N!
        have :=
        calc p * l + p
          _ = p * (l + 1) := by ring
          _ = N ! + 1 := by rw [hk]
          _ < N ! + p := by addarith [hp2] -- since 2 ≤ p
        addarith [this] -- too clever for me
      · calc N ! < N ! + 1 := by extra
          _ = p * (l + 1) := by rw [hk]
    -- so `p` is a prime number greater than or equal to `N`, as we sought
    use p
    constructor
    · -- prove p ≥ N
      -- Either p ≤ N or N < 0
      obtain h_le | h_gt : p ≤ N ∨ N < p := le_or_lt p N
      · -- suppose p ≤ N
        -- Then by the definition of factorial, p divides N!
        have : p ∣ (N !)
        ·
          -- Nat.dvd_factorial {m n : ℕ} (a✝ : 0 < m) (a✝¹ : m ≤ n) : m ∣ n !
          apply dvd_factorial
          · -- 0 < p
            -- Since 2 ≤ p, 0 < p
            extra
          · -- suppose p ≤ N. Why then, p ≤ n
            apply h_le -- addarith [h_le]
        -- But p doesn't divide N, so we can eliminate the case
        -- that p ≤ N
        contradiction
      · -- Suppose N < p. Then we have p ≥ N
        addarith [h_gt]
    · apply hp
