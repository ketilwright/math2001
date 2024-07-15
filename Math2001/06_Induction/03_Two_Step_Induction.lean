/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
set_option maxHeartbeats 0
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
  -- very similar to preceding example: ∀ m ∈ ℕ ≥ 1, aₘ ≡₆ 1 ∨ aₘ ≡₆ 5
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

--#eval [p 0, p 1, p 2, p 3, p 4,  p 5,   p 6,    p 7,    p 8,     p 9      p 10]
--      [  2,   3,  16,  93, 542, 3159, 18412, 107313, 625466, 3645483, 21247432]
--             ^              ^                   ^                          ^
#eval [  2 % 7,   3 % 7,  16 % 7,  93 % 7, 542 % 7, 3159 % 7, 18412 % 7, 107313 % 7, 625466 % 7, 3645483 % 7, 21247432 % 7]
--    [      2,       3,       2,       2,       3,        2,         2,          3,          2,           2,            3]
--    case   2        0        1        2        0,        1,         1,          0,          1,           0


example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by

  have h: ∀ n: ℕ, (p n ≡ 2 [ZMOD 7] ∧  p (n + 1) ≡ 3 [ZMOD 7] ∧ p (n + 2) ≡ 2 [ZMOD 7]) -- 2, 3, 2
                ∨ (p n ≡ 3 [ZMOD 7] ∧  p (n + 1) ≡ 2 [ZMOD 7] ∧ p (n + 2) ≡ 2 [ZMOD 7]) -- 3, 2, 2
                ∨ (p n ≡ 2 [ZMOD 7] ∧  p (n + 1) ≡ 2 [ZMOD 7] ∧ p (n + 2) ≡ 3 [ZMOD 7]) -- 2, 2, 3
                := by
      intro n
      two_step_induction n with k hk1 hk2
      · -- Base case 1
        left
        constructor
        · rw [p]; extra
        · constructor
          · rw [p]; extra
          · rw [p, p, p];
            calc (6: ℤ) * 3 - 2
              _ = 2 * 7 + 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
      · -- Base case 2
        right; left; constructor
        · rw [p]; numbers
        · constructor
          · rw [p, p, p]
            calc (6: ℤ) * 3 - 2
              _ = 2 * 7 + 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
          · rw [p, p, p, p, p]
            calc  (6: ℤ) * (6 * 3 - 2) - 3
              _ = 7 * 13 + 2 := by numbers
              _ ≡ 2 [ZMOD 7] := by extra
      · -- Inductive step

        have cleanup1: k + 1 + 1 = k + 2 := by ring
        have cleanup2: k + 2 + 1 = k + 3 := by ring
        rw [cleanup1, cleanup2]
        rw [cleanup1] at hk1
        rw [cleanup1, cleanup2] at hk2
        obtain ⟨ha1, ha2, ha3⟩ | ⟨ha1, ha2, ha3⟩ | ⟨ha1, ha2, ha3⟩ := hk1
        ·
          obtain ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ := hk2
          ·
            right; right
            constructor
            · apply ha3 -- in reality, this case can't happen: ha1, hb1
            · constructor
              · apply hb3 -- sorry
              · -- This case cannot happen: hb2 and ha3 contradict each other
                -- let z = pₖ₊₂
                set z: ℤ := p (k + 2)
                obtain ⟨x, hx⟩ := ha3
                obtain ⟨y, hy⟩ := hb2
                -- Since z - 2 = 7 ⬝ x and z - 3 = 7 ⬝ y we have 7y + 1 = 7 x
                have h102:=
                  calc 7 * y + 1
                    _ = (7 * y + 3) - 2 := by ring
                    _ = z - 2 := by addarith [hy]
                    _ = 7 * x := by addarith [hx]
                -- Since 7 ∣ 7x and 7x = 7y + 1 we arrive at the contradiction
                -- that 7 ∣ 7y + 1
                have h104: 7 ∣ 7 * y + 1 := by rw [h102]; use x; ring
                have h108: ¬ 7 ∣ 7 * y + 1 := by
                  apply Int.not_dvd_of_exists_lt_and_lt
                  use y
                  constructor
                  · extra
                  · calc 7 * y + 1
                      _ < 7 * y + 1 + 6 := by extra
                      _ = 7 * (y + 1) := by ring

                contradiction -- I get the feeling I did this the hard way
          · right; right
            constructor
            · apply ha3
            · constructor
              · apply hb3
              ·
                calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [hb3, hb2]
                  _ ≡ 7 + 3 [ZMOD 7] := by numbers
                  _ ≡ 3 [ZMOD 7] := by use 1; ring
          ·
            left
            constructor
            · apply hb2
            · constructor
              · apply hb3
              · calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [hb3, ha3]
                  _ ≡ 7 * 2 + 2 [ZMOD 7] := by numbers
                  _ ≡ 2 [ZMOD 7] := by use 2; ring
        ·
          obtain ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ := hk2
          ·
            right; left
            constructor
            · apply hb2
            · constructor
              · apply hb3
              · calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [hb3, hb2]
                  _ ≡ 7 + 2 [ZMOD 7] := by numbers
                  _ ≡ 2 [ZMOD 7] := by use 1; ring
          · right; right
            constructor
            · apply ha3
            · constructor
              · apply hb3
              ·
                calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [hb3, hb2]
                  _ ≡ 7 + 3 [ZMOD 7] := by numbers
                  _ ≡ 3 [ZMOD 7] := by use 1; ring

          · left
            constructor
            · apply ha3
            · constructor
              · apply hb3
              ·
                calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [hb3, hb2]
                  _ ≡ 2 * 7 + 2 [ZMOD 7] := by numbers
                  _ ≡ 2 [ZMOD 7] := by use 2; ring
        ·
          obtain ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩ := hk2
          · right; left
            constructor
            · apply ha3
            · constructor
              · apply hb3
              ·
                calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [hb3, hb2]
                  _ ≡ 7 + 2 [ZMOD 7] := by numbers
                  _ ≡ 2 [ZMOD 7] := by use 1; ring
          · right; left
            constructor
            · apply ha3
            · constructor
              · apply hb3
              ·
                calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [hb3, ha3]
                  _ ≡ 7 + 2 [ZMOD 7] := by numbers
                  _ ≡ 2 [ZMOD 7] := by use 1; ring
          · left
            constructor
            · apply hb2
            · constructor
              · apply hb3
              ·
                calc p (k + 4)
                  _ = 6 * p (k + 3) - p (k + 2) := by rw [p]
                  _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [hb3, hb2]
                  _ ≡ 2 * 7 + 2 [ZMOD 7] := by numbers
                  _ ≡ 2 [ZMOD 7] := by use 2; ring



  obtain ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ := h m
  ·
    -- suppose:
    /-
      h1 : p m ≡ 2 [ZMOD 7]
      h2 : p (m + 1) ≡ 3 [ZMOD 7]
      h3 : p (m + 2) ≡ 2 [ZMOD 7]
    -/
    left; apply h1
  · -- suppose:
    /-
      h1 : p m ≡ 3 [ZMOD 7]
      h2 : p (m + 1) ≡ 2 [ZMOD 7]
      h3 : p (m + 2) ≡ 2 [ZMOD 7]
    -/
    right; apply h1
  · -- suppose:
    /-
      h1 : p m ≡ 2 [ZMOD 7]
      h2 : p (m + 1) ≡ 2 [ZMOD 7]
      h3 : p (m + 2) ≡ 3 [ZMOD 7]
    -/
    left; apply h1

/-
-- a bit more thought reveals we don't need a 3 conjuncts within the 3 disjuncts.
-- The form is completely expressed by a disjunction of:
  case 1) pₙ ≡₇ 2 ∧ p₍ₙ₊₁₎ ≡₇ 3
  case 2) pₙ ≡₇ 3 ∧ p₍ₙ₊₁₎ ≡₇ 2
  case 3) pₙ ≡₇ 2 ∧ p₍ₙ₊₁₎ ≡₇ 2

#eval [  2 % 7,   3 % 7,  16 % 7,  93 % 7, 542 % 7, 3159 % 7, 18412 % 7, 107313 % 7, 625466 % 7, 3645483 % 7, 21247432 % 7]
--    [      2,       3,       2,       2,       3,        2,         2,          3,          2,           2,            3]
--    case   2        0        1        2        0,        1,         1,          0,          1,           0

-/
example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by

  have h: ∀ n: ℕ, (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 3 [ZMOD 7]) ∨
                  (p n ≡ 3 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])  ∨
                  (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7]) := by

    intro n
    two_step_induction n with k hk1 hk2
    ·
      left
      constructor
      · -- Base 1 case
        calc p 0
          _ = 2 := by rw [p]
          _ ≡ 2 [ZMOD 7] := by use 0; ring
      ·
        calc p 1
          _ = 3 := by rw [p]
          _ ≡ 3 [ZMOD 7] := by use 0; ring
    · -- Base 2 case
      right; left;
      constructor
      · calc p 1
          _ = 3 := by rw [p]
          _ ≡ 3 [ZMOD 7] := by use 0; ring
      ·
        have h1: p 2 = 6 * (p 1) - p 0 := by exact rfl
        calc p 2
          _ = 6 * (p 1) - p 0 := by exact rfl
          _ = 6 * 3 - 2 := by rw [p, p]
          _ = 2 * 7 + 2 := by numbers
          _ ≡ 2 [ZMOD 7] := by use 2; numbers
    · -- Inductive step
      obtain ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ := hk1
      ·
        obtain ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ := hk2
        · -- This case can't happen since we have both
          -- pₖ₊₁ ≡₇ 2 and pₖ₊₁ ≡₇ 3
          set z: ℤ := p (k + 1)
          obtain ⟨x, hx⟩ := hb1
          obtain ⟨y, hy⟩ := ha2
          -- Which leads us to the dubious 7 ∣ 7 ⬝ y + 1
          have h3:=
            calc 7 * y + 1
              _ = 7 * y + 3 - 2 := by ring
              _ = z - 2 := by addarith [hy]
              _ = 7 * x := by addarith [hx]
          have h4: 7 ∣ 7 * y + 1 := by rw [h3]; use x; ring
          -- But 7 cannot divide 7y + 1
          have h5: ¬7 ∣ 7 * y + 1 := by
            apply Int.not_dvd_of_exists_lt_and_lt
            use y
            constructor
            · extra
            · calc 7 * y + 1
                _ < 7 * y + 1 + 6 := by extra
                _ = 7 * (y + 1) := by ring
          contradiction -- TODO (maybe) This contradiction happens
                        -- 3 times in this proof & could be wrapped
                        -- into a lemma. But it turns out simple_induction
                        -- avoids the problem entirely
        ·
          right; right

          constructor; apply hb2
          calc p (k + 3)
            _ = 6 * p ( k + 2) - p (k + 1) := by rw[p, p]
            _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [hb2, hb1]
            _ ≡ 1 * 7 + 2 [ZMOD 7] := by numbers
            _ ≡ 2 [ZMOD 7] := by use 1; ring
        · -- This case can't happen since we have
          -- pₖ₊₁ ≡₇ 2 and pₖ₊₁ ≡₇ 3
          set z: ℤ := p (k + 1)
          obtain ⟨x, hx⟩ := hb1
          obtain ⟨y, hy⟩ := ha2
          -- Which leads us to the dubious 7 ∣ 7 ⬝ y + 1
          have h6:=
            calc 7 * y + 1
              _ = 7 * y + 3 - 2 := by ring
              _ = z - 2 := by addarith [hy]
              _ = 7 * x := by addarith [hx]
          have h7: 7 ∣ 7 * y + 1 := by rw [h6]; use x; ring
          -- But 7 cannot divide 7y + 1
          have h8: ¬7 ∣ 7 * y + 1 := by
            apply Int.not_dvd_of_exists_lt_and_lt
            use y
            constructor
            · extra
            · calc 7 * y + 1
                _ < 7 * y + 1 + 6 := by extra
                _ = 7 * (y + 1) := by ring
          contradiction
      · obtain ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ := hk2
        · right; left
          constructor
          · apply hb2
          · calc p (k + 3)
              _ = 6 * p ( k + 2) - p (k + 1) := by rw[p, p]
              _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [hb2, hb1]
              _ ≡ 2 * 7 + 2 [ZMOD 7] := by numbers
              _ ≡ 2 [ZMOD 7] := by use 2; ring
        ·
          -- This case can't happen since we have
          -- pₖ₊₁ ≡₇ 2 and pₖ₊₁ ≡₇ 3
          set z: ℤ := p (k + 1)
          obtain ⟨x, hx⟩ := ha2
          obtain ⟨y, hy⟩ := hb1
          have h9:=
            calc 7 * y + 1
              _ = 7 * y + 3 - 2 := by ring
              _ = z - 2 := by addarith [hy]
              _ = 7 * x := by addarith [hx]
          have h10: 7 ∣ 7 * y + 1 := by rw [h9]; use x; ring
          have h11: ¬7 ∣ 7 * y + 1 := by
            apply Int.not_dvd_of_exists_lt_and_lt
            use y
            constructor
            · extra
            · calc 7 * y + 1
                _ < 7 * y + 1 + 6 := by extra
                _ = 7 * (y + 1) := by ring
          contradiction
        · left
          constructor
          · apply hb2
          ·
            calc p (k + 3)
              _ = 6 * p ( k + 2) - p (k + 1) := by rw[p, p]
              _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [hb2, hb1]
              _ ≡ 1 * 7 + 3 [ZMOD 7] := by numbers
              _ ≡ 3 [ZMOD 7] := by use 1; ring

      ·
        obtain ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ := hk2
        · right; left
          constructor
          · apply hb2
          ·
            calc p (k + 3)
              _ = 6 * p ( k + 2) - p (k + 1) := by rw[p, p]
              _ ≡ 6 * 3 - 2 [ZMOD 7]:= by rel [hb2, hb1]
              _ ≡ 2 * 7 + 2 [ZMOD 7]:= by numbers
              _ ≡ 2 [ZMOD 7] := by use 2; ring
        · -- This case can't happen since we have
          -- pₖ₊₁ ≡₇ 2 and pₖ₊₁ ≡₇ 3
          set z: ℤ := p (k + 1)
          obtain ⟨x, hx⟩ := ha2
          obtain ⟨y, hy⟩ := hb1
          have h12:=
            calc 7 * y + 1
              _ = 7 * y + 3 - 2 := by ring
              _ = z - 2 := by addarith [hy]
              _ = 7 * x := by addarith [hx]
          have h13: 7 ∣ 7 * y + 1 := by rw [h12]; use x; ring
          have h14: ¬7 ∣ 7 * y + 1 := by
            apply Int.not_dvd_of_exists_lt_and_lt
            use y
            constructor
            · extra
            · calc 7 * y + 1
                _ < 7 * y + 1 + 6 := by extra
                _ = 7 * (y + 1) := by ring
          contradiction
        · left;
          constructor
          · apply hb2
          ·
            calc p (k + 3)
              _ = 6 * p ( k + 2) - p (k + 1) := by rw[p, p]
              _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel [hb2, hb1]
              _ ≡ 1 * 7 + 3 [ZMOD 7] := by numbers
              _ ≡ 3 [ZMOD 7] := by use 1; ring


  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩  := h m
  ·
    left; apply h1
  ·
    right; apply h1
  ·
    left; apply h1

/-
  3rd attempt: It looks like this can be done with simple_induction
  So why's it in the 2 step induction chapter?
-/
example (m : ℕ) : p m ≡ 2 [ZMOD 7] ∨ p m ≡ 3 [ZMOD 7] := by
  have h: ∀ n: ℕ, (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 3 [ZMOD 7]) ∨
                  (p n ≡ 3 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7])  ∨
                  (p n ≡ 2 [ZMOD 7] ∧ p (n + 1) ≡ 2 [ZMOD 7]) := by
    intro n
    simple_induction n with k hk
    · -- Base case
      left
      constructor
      · calc p 0
          _ = 2 := by rw [p]
          _ ≡ 2 [ZMOD 7] := by numbers
      · calc p 1
        _ = 3 := by rw [p]
        _ ≡ 3 [ZMOD 7] :=  by numbers
    ·
      obtain ⟨h1, h2⟩  | ⟨h1, h2⟩  | ⟨h1, h2⟩  := hk
      · right; left;
        constructor
        · apply h2
        · calc p (k + 2)
            _ = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 3 - 2 [ZMOD 7] := by rel [h2, h1]
            _ ≡ 2 * 7 + 2 [ZMOD 7] := by numbers
            _ ≡ 2 [ZMOD 7] := by use 2; numbers
      · right; right
        constructor
        · apply h2
        · calc p (k + 2)
            _ = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 2 - 3 [ZMOD 7] := by rel [h2, h1]
            _ ≡ 1 * 7 + 2 [ZMOD 7] := by numbers
            _ ≡ 2 [ZMOD 7] := by use 1; numbers
      ·
        left
        constructor
        · apply h2
        · calc  p (k + 2)
            _ = 6 * p (k + 1) - p k := by rw [p]
            _ ≡ 6 * 2 - 2 [ZMOD 7] := by rel[h2, h1]
            _ ≡ 1 * 7 + 3 [ZMOD 7] := by numbers
            _ ≡ 3 [ZMOD 7] := by use 1; numbers

  obtain ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩  := h m
  ·
    left; apply h3
  ·
    right; apply h3
  ·
    left; apply h3



def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n


example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 10
  intro x hx
  two_step_induction_from_starting_point x, hx with k hk ih1 ih2
  · -- base case 1
    calc r 10
      _ = 1970 := by rfl
      _ ≥ 2 ^ 10 := by numbers
  · -- base case 2
    calc r 11
      _ = 4756 := by rfl
      _ ≥ 2 ^ 11 := by numbers
  · -- induction step
    calc r (k + 2)
      _ = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [ih1, ih2]
      _ = 2 ^ (k + 2) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 2) := by extra


example : forall_sufficiently_large n : ℕ,
    (0.4:ℚ) * 1.6 ^ n < F n ∧ F n < (0.5:ℚ) * 1.7 ^ n := by

  use 8
  intro x hx
  two_step_induction_from_starting_point x, hx with k hk ih1 ih2
  · constructor
    · calc (0.4:ℚ) * 1.6 ^ 8
        _ < 34 := by numbers
        _ = F 8 :=  by rfl
    · calc ((F 8) : ℚ)
        _ = 34 := by rfl
        _ < (0.5:ℚ) * 1.7 ^ 8 := by numbers
    -- Appears to be _some_ flexibility in implicit cast Q <-> N
  · constructor
    ·
      calc (0.4: ℚ) * 1.6 ^ (9)
        _ < 55 := by numbers
        _ = ↑(F (9)) := by rfl
    ·
      calc ↑(F (9))
        _ = (55: ℚ) := by rfl
        _ < (0.5: ℚ) * 1.7 ^ (9) := by numbers
  ·
    -- suppose 0.4 ⬝ 1.6ᵏ < Fₖ < 0.5 ⬝ 1.7ᵏ and
    -- suppose 0.4 ⬝ 1.6ᵏ⁺¹ < Fₖ₊₁ < 0.5 ⬝ 1.7ᵏ⁺¹
    obtain ⟨ih1l, ih1r⟩ := ih1
    obtain ⟨ih2l, ih2r⟩ := ih2

    constructor
    ·
      calc (0.4: ℚ) * 1.6 ^ (k + 2)
        _ = (0.4: ℚ) * (1.6 ^ k * (1.6 ^ 2)) := by ring
        _ < (0.4: ℚ) * (1.6 ^ k * 2.6) := by
          have h3: (2.6: ℚ) > 1.6 ^ 2 := by numbers
          rel [h3]
        _ = (0.4: ℚ) * 1.6 ^ (k + 1) + (0.4: ℚ) * 1.6 ^ k := by ring
        _ < ↑( F ( k + 1)) + ↑ (F k) := by rel [ih2l, ih1l]
        _ =  ↑ (F ( k + 1) + F k)   := by rw [Rat.intCast_add (F ( k + 1)) (F k) ]
        _ = ↑ (F (k + 2)) := by rw [F]
    ·
      have h4: (2.7: ℚ) < 2.89 := by numbers
      have h5: (1.7: ℚ) ^ k * 1.7 ^ 2 = 1.7 ^ (k + 2) := by ring
      calc ↑(F (k + 2))
        _ = ↑( F ( k + 1) + F k) := by rw [F]
        _ = ↑( F ( k + 1)) + ↑ (F k) := by exact Rat.intCast_add (F (k + 1)) (F k)
        _ <  (0.5: ℚ) * 1.7 ^ (k + 1) + 0.5 * 1.7 ^ k := by rel [ih2r, ih1r]
        _ = (0.5: ℚ) * (1.7 ^ (k + 1) + 1.7 ^ k) := by ring
        _ = (0.5: ℚ) * 1.7 ^ k * (2.7) := by ring
        _ < (0.5: ℚ) * 1.7 ^ k * (2.89) := by rel [h4]
        _ = (0.5: ℚ) * ((1.7: ℚ) ^ k * (1.7 ^ 2)) := by ring
        _ = (0.5: ℚ) * (1.7: ℚ) ^ (k + 2) := by rw [h5]
