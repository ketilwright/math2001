/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

/-
#eval 0 ^ 0 ^ 0 + 1 -- 1
#eval 0 ^ 0 ^ 1 + 1 -- 2
#eval 0 ^ 0 ^ 2 + 1 -- 2
-/

theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  -- Not to worry about "conv"
  conv at one_prime => numbers -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction

/-
#eval 1 ^ 1 ^ 0 + 1 -- 2
#eval 1 ^ 1 ^ 1 + 1 -- 2
#eval 1 ^ 1 ^ 2 + 1 -- 2
-/

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

/-
#eval 2 ^ 2 ^ 0 + 1 -- 3
#eval 2 ^ 2 ^ 1 + 1 -- 5
#eval 2 ^ 2 ^ 2 + 1 -- 17
#eval 2 ^ 2 ^ 3 + 1 -- 257
#eval 2 ^ 2 ^ 4 + 1 -- 65537
-/

/-
#eval 3 ^ 3 ^ 0 + 1 -- 4
#eval 3 ^ 3 ^ 1 + 1 -- 28
#eval 3 ^ 3 ^ 2 + 1 -- 19684
-/

theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1`
    · numbers -- show `2 ≠ 4`
    · numbers -- show `4 = 2 * 2`
  contradiction

/-
  The point about this proof is that it works even though we don’t
  know whether 2 is superpowered or not. Either way, we have a way
  of solving the problem.

  I think this is the 1st use of by_cases in math2001
-/

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2


example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction

/-! # Exercises -/


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h0: Tribalanced 1
  ·
    use 1
    constructor
    ·
      apply h0
    ·
      have h2: ¬ Tribalanced (1 + 1) := by
        dsimp [Tribalanced]
        intro h3 -- ∀ (n : ℕ), (1 + 2 / ↑n) ^ n < 3
        have h4: (1 + (1 + 1) / (2: ℝ)) ^ 2 < 3 := by apply h3 (1 + 1)
        have h5: ¬ ((1: ℝ) + (1 + 1) / 2) ^ 2 < 3 := by numbers
        contradiction
      apply h2
  ·
    use 0
    constructor
    ·
      dsimp [Tribalanced]
      intro n
      calc ((1: ℝ) + 0 / ↑n) ^ n
        _ = (1: ℝ) ^ n := by ring
        _ = 1 := by exact one_pow n
        _ < 3 := by numbers

    ·
      have h3: (0: ℝ) + 1 = 1 := by numbers
      rw [h3];
      apply h0




example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  sorry

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  sorry
