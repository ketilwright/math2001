/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


def a (n : ℕ) : ℕ := 2 ^ n


#eval a 20 -- infoview displays `1048576`


def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2


--#eval b 7 -- infoview displays `316837008400094222150776738483768236006420971486980607`


example (n : ℕ) : Odd (b n) := by
  simple_induction n with k hk
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring

/-
  You might like to try giving another proof using the modular-arithmetic
  characterization of parity; this will work both in text and in Lean.
-/
example (n : ℕ) : b n ≡ 1 [ZMOD 2] := by
  dsimp [Int.ModEq, . ∣ .]
  simple_induction n with k hk
  ·
    use 1;  rw [b]; numbers
  ·
    obtain ⟨x, hx⟩ := hk
    have h1: b k = 2 * x + 1 := by addarith [hx]
    have h2: b (k + 1) = (b k) ^ 2 - 2 := by rfl
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) - 1
      _ = (b k) ^ 2 - 2 - 1 := by rw [h2]
      _ = (2 * x + 1) ^ 2 - 2 - 1 := by rw [h1]
      _ = 4 * x ^ 2 + 4 * x - 2 := by ring
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) := by ring


def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  have x0: x 0 = 5 := by rw [x]
  simple_induction n with k IH
  · -- base case is trivial
    dsimp [Int.ModEq]; rw [x]; use 1; numbers
  · -- inductive step
    -- Suppose xₖ ≡₄ 1
    -- Then since xₖ₊₁ = 2 ⬝ xₖ - 1, 2 ≡₄ 2 and -1 ≡₄ -1 we can use ModEq.mul and add to
    -- see that we have xₖ₊₁ ≡₄ (2 ⬝ 1 - 1)
    calc x (k + 1)
      _ = 2 * (x k) - 1 := by rw [x]
      _ ≡ (2 * 1 - 1) [ZMOD 4] := Int.ModEq.add (Int.ModEq.mul (by extra) IH) (by extra)
      _ = 1 := by numbers

-- closed form
example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ (k + 1 + 2) + 1 := by ring


def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)


example (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/-
  Show that every natural number d with 1 ≤ d < n is a factor of n!
-/
-- protected theorem pos_iff_ne_zero : 0 < n ↔ n ≠ 0 := ⟨ne_of_gt, Nat.pos_of_ne_zero⟩

example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · -- base case: Suppose k = 0
    intro k hk1 hk
    interval_cases k
    /-
        My OC suggests another possible approach, which doesn't rely
        on super clever use of interval_cases

    apply Nat.eq_zero_of_le_zero at hk
    -- Since 1 ≤ k either 1 < k or 1 = k
    obtain h1 | h1 := lt_or_eq_of_le hk1
    · -- We can't have 1 < k since k = 0
      have h2: ¬ 1 < 0 := by numbers
      rw [hk] at h1; contradiction
    ·  -- Thus k = 1, and since 0! = 1, we are done
      rw [factorial, h1]
    -/

  · -- inductive step
    intro d hk1 hk
    -- Since d ≤ k + 1, either d = k + 1 or d < k + 1
    obtain hk | hk : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hk
    · -- case 1: suppose d = k + 1
      use (k !); rw [factorial, hk];
    · -- case 2: suppose d < k + 1
      -- The d ≤ k, and since 1 ≤ d, from the induction hypothesis, d ∣ k !
      rw [Nat.lt_succ] at hk
      -- Since d ∣ k!, there is x with k! = d * x
      obtain ⟨x, hx⟩ := IH d hk1 hk
      use (k + 1) * x
      calc (k + 1)!
      --  Since (k + 1) ! = (k + 1) ⬝ k!
        _ = (k + 1) * k ! := by rw [factorial]
      --  and k! = dx, we are done.
        _ = (k + 1) * (d * x) := by rw [hx]
        _ = d * ((k + 1) * x) := by ring

-- this theorem is dvd_factorial

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k hk
  · -- base case: n = 0
    -- we have (0 + 1)! = (0 + 1) ⬝ 0! = 1 ≥ 2⁰ = 1
    rw [factorial, factorial]; extra
  · -- inductive step
    -- Suppose (k + 1)! ≥ 2ᵏ
    calc (k + 1 + 1)!
      _ = (k + 2) * (k + 1) ! := by rw [factorial]
      _ ≥ (k + 2) * 2 ^ k := by rel [hk]
      _ = k * 2 ^ k + 2 ^ (k + 1) := by ring
      _ ≥ 2 ^ (k + 1) := by extra

/-! # Exercises -/


def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  sorry

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  sorry

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  sorry

example (n : ℕ) : 0 < n ! := by
  sorry

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  sorry

example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  sorry
