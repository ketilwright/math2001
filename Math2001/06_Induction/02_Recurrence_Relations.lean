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

lemma example_6_2_6 (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
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
  simple_induction n with x hx
  ·
    rewrite [c]; use 3; numbers
  ·
    obtain ⟨y, hy⟩ := hx
    rw [c]
    dsimp [Odd]
    use 3 * y - 4
    calc 3 * c x - 10
      _ = 3 * (2 * y + 1) - 10 := by rw [hy]
      _ = 2 * (3 * y - 4) + 1 := by ring

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with a ha
  ·
    rewrite [c]; ring
  ·
    calc  c (a + 1)
      _ = 3 * (c a) - 10 := by rw [c]
      _ = 3 * (2 * 3 ^ a + 5) - 10 := by rw [ha]
      _ = 2 * 3 ^ (a + 1) + 5 := by ring


def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with x hx
  ·
    rw [y]; ring
  ·
    calc y (x + 1)
      _ = (y x) ^ 2 := by rw [y]
      _ = (2 ^ 2 ^ x) ^ 2 := by rw [hx]
      _ = 2 ^ 2 ^ (x + 1) := by ring

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2


example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with x hx
  ·
    rw [B]; numbers
  · -- hx: B x = ↑x * (↑x + 1) * (2 * ↑x + 1) / 6
    calc  B (x + 1)
      _ = B x + (x + 1 : ℚ) ^ 2 := by rw [B]
      _ = x * (x + 1) * (2 * x + 1) / 6 + (x + 1: ℚ) ^ 2 := by rw [hx]
      -- Lean is better at algebra than I: it canskip all the steps except
      -- the final one
      _ = x * (x + 1) * (2 * x + 1) / 6 + (6 * (x + 1: ℚ) ^ 2) / 6 := by ring
      _ = x * (x + 1) * (2 * x + 1) / 6 + (6 * (x ^ 2 + 2 * x + 1)) / 6 := by ring
      _ = (x ^ 2 + x) * (2 * x + 1) / 6 + (6 * (x ^ 2 + 2 * x + 1)) / 6 := by ring
      _ = (2 * x ^ 3 + 9 * x ^ 2 + 13 * x + 6) / 6 := by ring
      _ = (x + 1) * (2 * x ^ 2 + 7 * x + 6) / 6 := by ring
      _ = (x + 1) * (2 * x + 3) * (x + 2)/ 6 := by ring
      _ = (x + 1) * (x + 1 + 1) * (2 * (x + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with x hx
  ·
    rw [S]; numbers
  ·
    calc S (x + 1)
      _ = 2 - 1 / 2 ^ x + 1 / 2 ^ (x + 1) := by rw[S, hx]
      _ = 2 - 1 / 2 ^ (x + 1) := by ring
-- might be useful
lemma factorial_positive /-example-/ (n : ℕ) : 0 < n ! := by
  simple_induction n with x hx
  · -- Base case is true by definition
    dsimp [factorial]; numbers
  · -- Inductive step: suppose x ! > 0
    -- Then since x + 1 ≥ 1, we have
    -- 0 < x! ≤ (x + 1) ⬝ (x !) = (x + 1)!
    calc  0
      _ < x ! := hx
      _ ≤ (x + 1) * (x !)  := by exact Nat.le_mul_of_pos_left (Nat.succ_pos x)
      _ = (x + 1)! := by rw [factorial]


example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with x hx ih
  ·
    dsimp [Nat.Even, factorial]; use 1; ring
  · -- suppose x ! is even
    dsimp [Nat.Even, factorial]
    -- Then there is c with x! = 2 ⬝ c
    obtain ⟨c, hc⟩ := ih
    use c * (x + 1)
    calc (x + 1) * (x !)
      _ = (x + 1) * (2 * c) := by rw [hc]
      _ = 2 * (c * (x + 1)) := by ring

--#eval 1 !

--#check Nat.lt.base
lemma factorial_non_decreasing (n: ℕ) : (n + 1) ! ≥ n ! := by
  --have h0: n ≥ n := by exact Nat.le_refl n

  simple_induction n with x hx
  · -- Base case: let n = 0
    --rw [factorial];
    --have h1: 1 ≥ 1 := by exact Nat.factorial_eq_one.mp rfl
    calc (0 + 1)!
      _ = 1 ! := by rw [factorial]
      _ = 1  := by rfl
      _ ≥ 1 := Nat.le_refl 1
  ·
    have h0: x ! > 0 := by exact factorial_positive x
    have h1: x + 1 > 0 := by exact Nat.succ_pos x

    have h2: x + 2 > 0 := by exact Nat.succ_pos (x + 1)
    have h3: (x + 1) * (x !) > 0 := by exact Nat.mul_pos h1 h0
    have h4: (x + 2) * ((x + 1) * (x !)) > 0 := Nat.mul_pos h2 h3
    --have h5: (x + 2) * ((x + 1) * (x !)) = (x + 2) * (x + 1) * (x !) := by apply?
    --rw [←mul_assoc] at h4
    have h5: x + 1 + 1 = x + 2 := by ring
    have h6: x + 2 > x + 1 :=  Nat.lt.base (x + 1)
    have h7: x + 2 > 1 := by exact Nat.one_lt_succ_succ x

    rw [factorial, factorial, h5]
    have h100:=
      calc (x + 2) * ((x + 1) * x !)
        _ > 1 * ((x + 1) * x !) := by rel [h7]
        _ = (x + 1) * x ! := by ring
    apply le_of_lt -- apparently there is not ge_of_gt
    apply h100

example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with x hx
  ·
    dsimp [factorial]; extra
  · -- suppose (x + 1)! ≤ (x + 1) ^ x
    have h0: x + 1 + 1 = x + 2 := by ring;
    rw [h0]
    have h1: (x + 1) ! = (x + 1) * (x !) := by rw [factorial]
    have h2: (x + 2) ! = (x + 2) * (x + 1) ! := by rw [factorial]
    rw [h1] at h2
    have h3: x ! > 0 := factorial_positive x
    have h4: 0 ! = 1 := by rfl -- rw [factorial]
    have h5: 1 ! = 1 := by rfl -- exact h4
    have h6: 2 ! = 2 := by rfl
    --have h7: (x + 1) * x ! ≥ 2 ^ x := by example

    have h8: x + 1 < x + 2 := by exact Nat.lt.base (x + 1)
    have h8a: x + 1 ≤ x + 2 := by exact Nat.le_succ (x + 1)
    have h9: (x + 2) ^ (x + 1) = (x + 2) * (x + 2) ^ x := by ring
    -- rw [h9]
    have h10: x + 1 > 0 := by exact Nat.succ_pos x

    have h11: (x + 1) ^ x ≤ (x + 2) ^ x := by exact Nat.pow_le_pow_of_le_left h8a x

    have h100 :=
      calc (x + 2)!
        _ = (x + 2) * (x + 1) ! := by rw [factorial]
        _ ≤ (x + 2) * (x + 1) ^ x := by rel [hx]
        --_ ≤
        --_ ≤ (x + 2) ^ (x + 1) := sorry
        _ ≤ (x + 2) * (x + 2) ^ x := by rel [h11]
        _ = (x + 2) ^ (x + 1) := by rw [h9]
    apply h100
