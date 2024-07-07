/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n


--#eval a 5 -- infoview displays `31`


example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  two_step_induction n with k IH1 IH2
  . calc a 0 = 2 := by rw [a]
      _ = 2 ^ 0 + (-1) ^ 0 := by numbers
  . calc a 1 = 1 := by rw [a]
      _ = 2 ^ 1 + (-1) ^ 1 := by numbers
  calc
    a (k + 2)
      = a (k + 1) + 2 * a k := by rw [a]
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [IH1, IH2]
    _ = (2 : ℤ) ^ (k + 2) + (-1) ^ (k + 2) := by ring

/-
  Prove that ∀ m ∈ ℕ ≥ 1, aₘ ≡₆ 1 ∨ aₘ ≡₆ 5

  This actually proves (aₘ ≡₆ 1 ∧ aₘ₊₁ ≡₆ 5) ∨ (aₘ ≡₆ 5 ∧ aₘ₊₁ ≡₆ 1)
-/
example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ, 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧ a (n + 1) ≡ 5 [ZMOD 6])
    ∨ (a n ≡ 5 [ZMOD 6] ∧ a (n + 1) ≡ 1 [ZMOD 6])
  · intro n hn
    induction_from_starting_point n, hn with k hk IH
    · -- Base case: suppose  n = 1
      left
      constructor
      calc a 1 = 1 := by rw [a]
        _ ≡ 1 [ZMOD 6] := by extra
      calc a (1 + 1) = 1 + 2 * 2 := by rw [a, a, a]
        _ = 5 := by numbers
        _ ≡ 5 [ZMOD 6] := by extra
    · obtain ⟨IH1, IH2⟩ | ⟨IH1, IH2⟩ := IH
      · right
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 5 + 2 * 1 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 1 := by numbers
          _ ≡ 1 [ZMOD 6] := by extra
      · left
        constructor
        · apply IH2
        calc a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
          _ ≡ 1 + 2 * 5 [ZMOD 6] := by rel [IH1, IH2]
          _ = 6 * 1 + 5 := by numbers
          _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m hm
  · left
    apply H1
  · right
    apply H1


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n


example (n : ℕ) : F n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc F 0 = 1 := by rw [F]
      _ ≤ 2 ^ 0 := by numbers
  · calc F 1 = 1 := by rw [F]
      _ ≤ 2 ^ 1 := by numbers
  · calc F (k + 2) = F (k + 1) + F k := by rw [F]
      _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
      _ = 2 ^ (k + 2) := by ring


example (n : ℕ) : F (n + 1) ^ 2 - F (n + 1) * F n - F n ^ 2 = - (-1) ^ n := by
  simple_induction n with k IH
  · calc F 1 ^ 2 - F 1 * F 0 - F 0 ^ 2 = 1 ^ 2 - 1 * 1 - 1 ^ 2 := by rw [F, F]
      _ = - (-1) ^ 0 := by numbers
  · calc F (k + 2) ^ 2 - F (k + 2) * F (k + 1) - F (k + 1) ^ 2
        = (F (k + 1) + F k) ^ 2 - (F (k + 1) + F k) * F (k + 1)
            - F (k + 1) ^ 2 := by rw [F]
      _ = - (F (k + 1) ^ 2 - F (k + 1) * F k - F k ^ 2) := by ring
      _ = - -(-1) ^ k := by rw [IH]
      _ = -(-1) ^ (k + 1) := by ring


def d : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | k + 2 => 3 * d (k + 1) + 5 * d k

/-
#eval d 2 -- infoview displays `18`
#eval d 3 -- infoview displays `59`
#eval d 4 -- infoview displays `267`
#eval d 5 -- infoview displays `1096`
#eval d 6 -- infoview displays `4623`
#eval d 7 -- infoview displays `19349`


#eval 4 ^ 2 -- infoview displays `16`
#eval 4 ^ 3 -- infoview displays `64`
#eval 4 ^ 4 -- infoview displays `256`
#eval 4 ^ 5 -- infoview displays `1024`
#eval 4 ^ 6 -- infoview displays `4096`
#eval 4 ^ 7 -- infoview displays `16384`
-/

example : forall_sufficiently_large n : ℕ, d n ≥ 4 ^ n := by
  dsimp
  use 4
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc d 4 = 267 := by rfl
      _ ≥ 4 ^ 4 := by numbers
  · calc d 5 = 1096 := by rfl
      _ ≥ 4 ^ 5 := by numbers
  calc d (k + 2) = 3 * d (k + 1) + 5 * d k := by rw [d]
    _ ≥ 3 * 4 ^ (k + 1) + 5 * 4 ^ k := by rel [IH1, IH2]
    _ = 16 * 4 ^ k + 4 ^ k := by ring
    _ ≥ 16 * 4 ^ k := by extra
    _ = 4 ^ (k + 2) := by ring

/-! # Exercises -/


def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k ih1 ih2
  · -- Base case 1
    rw [b]; numbers
  · -- Base case 2
    rw [b]; numbers
  · -- Inductive step:
    -- Suppose bᵏ = 3ᵏ - 2ᵏ and bᵏ⁺¹ = 3ᵏ⁺¹ - 2ᵏ⁺¹
    -- Prove that bᵏ⁺² = 3ᵏ⁺² - 2ᵏ⁺²
    have h: k + 1 + 1 = k + 2 := by ring
    rw [h]
    calc  b (k + 2)
      _ = 5 * b (k + 1) - 6 * (b (k)) := by rw [b]
      _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1) ) - 6 * (3 ^ k - 2 ^ k ) := by rw [ih1, ih2]
      _ = 5 * ((3 ^ k * 3) - 2 ^ k  * 2) - 6 * (3 ^ k - 2 ^ k ) := by ring
      _ = 15 * 3 ^ k - 10 * 2 ^ k - 6 * 3 ^ k + 6 * 2 ^ k := by ring
      _ = 3 ^ 2 * 3 ^ k - 2 ^ 2 * 2 ^ k := by ring
      _ = 3 ^ (k + 2) - 2 ^ (k + 2) := by ring


def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

-- #eval [c 0, c 1, c 2, c 3, c 4, c 5, c 6]
--         [3,   2,   12,  8,  48,  32, 192]

example (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k ih1 ih2
  · -- Base case 1
    calc c 0
      _ = 3 := by rw [c]
      _ = 2 * 2 ^ 0 + (-2) ^ 0 := by numbers
  · -- Base case 2
    calc c 1
      _ = 2 := by rw [c]
      _ = 2 * 2 ^ 1 + (-2) ^ 1 := by numbers
  · -- Inductive step
    -- Suppose cₖ - 2 ⬝ 2ᵏ + (-2)ᵏ and cₖ₊₁ = 2 ⬝ 2ᵏ⁺¹ + (-2)ᵏ⁺¹
    have h: k + 1 + 1 = k + 2 := by ring
    rw [h]
    -- Prove that cₖ₊₂ = 2 ⬝ 2ᵏ⁺² + (-2)ᵏ⁺²
    calc c (k + 2)
      _ = 4 * (c k) := by rw [c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [ih1]
      _ = 2 * 2 ^ (k + 2) + (-2) ^ (k + 2) := by ring
    -- hmm, didn't use the 2nd inductive hypothesis
    -- (although it doesn't differ much from the 1st)
    -- I think 2step induction is needed though, since
    -- there is no definition for cₙ₊₁

def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

-- #eval [t 0, t 1, t 2, t 3, t 4, t 5, t 6]
--         [5,   7,   9,  11,  13,  15,  17]

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k ih1 ih2
  · -- Base case 1
    calc t 0
      _ = 5 := by rw [t]
      _ = 2 * 0 + 5 := by numbers
  · -- Base case 2
    calc t 1
      _ = 7 := by rw [t]
      _ = 2 * 1 + 5 := by numbers
  · -- Inductive step
    -- Suppose tₖ = 2 ⬝ k + 5 and tₖ₊₁ = 2 ⬝ (k + 1) + 5
    -- Prove that tₖ₊₂ = 2 ⬝ (k + 2) + 5
    have h: k + 1 + 1 = k + 2 := by ring
    have h': (↑k: ℤ) + 1 + 1 = (↑k: ℤ) + 2 := by ring
    rw [h, h'] -- clean up infoview k + 1 + 1 stuff
    calc t (k + 2)
      _ = 2 * t (k + 1) - (t k) := by rw [t]
      _ = 2 * (2 * (k + 1) + 5) - (2 * k + 5) := by rw [ih1, ih2]
      _ = 2 * (k + 2) + 5 := by ring
    -- I understand the infoview has a coercion to Z on the 2nd
    -- since t is N → Z. But why is it not needed in the calc block?

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

-- #eval [q 0, q 1, q 2, q 3, q 4, q 5, q 6]
--          [1,  2,   9,  28,  65, 126, 217]
example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k ih1 ih2
  · -- Base case 1
    calc q 0
      _ = 1 := by rw [q]
      _ = 0 ^ 3 + 1 := by numbers
  · -- Base case 2
    calc q 1
      _ = 2 := by rw [q]
      _ = 1 ^ 3 + 1 := by numbers
  · -- Inductive step
    -- suppose qₖ = k³ + 1 and qₖ₊₁ = (k + 1)³
    -- prove that qₖ₊₂ = (k + 2)³
    have h: k + 1 + 1 = k + 2 := by ring
    have h': (↑k: ℤ) + 1 + 1 = (↑k: ℤ) + 2 := by ring
    rw [h, h'] -- clean up infoview k + 1 + 1 stuff
    calc q (k + 2)
      _ = 2 * (q (k + 1)) - (q k) + 6 * k + 6 := by rw [q]
      _ = 2 * ((k + 1) ^ 3 + 1) - (k ^ 3 + 1) + 6 * k + 6 := by rw [ih1, ih2]
      _ = 2 * (k ^ 3 + 3 * k ^ 2 + 3 * k + 2) - (k ^ 3 + 1) + 6 * k + 6:= by ring
      _ = k ^ 3 + 6 * k ^ 2 + 12 * k + 8 + 1 := by ring
      _ = (↑k + 2) ^ 3 + 1 := by ring

def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

-- #eval [s 0, s 1, s 2, s 3, s 4, s 5, s 6]
--       [  2,   3,  12,  33, 102, 303, 912]
-- looks like
-- even s(m) ≡₅ 2
-- odd s(m) ≡₅ 3

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  -- very similar to preceding example
  have H : ∀ n: ℕ,
      (s n ≡ 2 [ZMOD 5] ∧ s (n + 1) ≡ 3 [ZMOD 5])
    ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n + 1) ≡ 2 [ZMOD 5]) := by
      intro n
      simple_induction n with k hk
      ·
        left
        constructor
        ·
          calc s 0
            _ = 2 := by rw [s]
            _ ≡ 2 [ZMOD 5] := by numbers
        ·
          calc s (1)
            _ = 3 := by rw [s]
            _ ≡ 3 [ZMOD 5] := by numbers
      ·
        have h₀: k + 1 + 1 = k + 2 := by ring
        rw [h₀]
        obtain ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ := hk
        · -- suppose sₖ ≡₅ 2 and sₖ₊₁ ≡₅ 3
          right
          constructor
          ·
            apply ih2
          ·
            calc s (k + 2)
              _ = 2 * s (k + 1) + 3 * s k := by rw [s]
              _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [ih1, ih2]
              _ ≡ (2 * 5 + 2) [ZMOD 5] := by numbers
              _ ≡ 2 [ZMOD 5] := by extra
        · -- suppose sₖ ≡₅ 3 and sₖ₊₁ ≡₅ 2
          left
          constructor
          ·
            apply ih2
          ·
            calc s (k + 2)
              _ = 2 * s (k + 1) + 3 * s k := by rw [s]
              _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [ih2, ih1]
              _ ≡ (2 * 5 + 3) [ZMOD 5] := by numbers
              _ ≡ 3 [ZMOD 5] := by extra


  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m
  · left
    apply H1
  · right
    apply H1


def p : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 6 * p (n + 1) - p n

example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  sorry

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  sorry

example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by
  sorry
