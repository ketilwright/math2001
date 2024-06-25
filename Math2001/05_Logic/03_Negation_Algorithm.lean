/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  ·
    intro h
    obtain h1 | h1 := h
    ·
      intro h2
      obtain ⟨h3, h4⟩ := h2
      contradiction

    ·
      intro h5
      obtain ⟨h6, h7⟩ := h5
      contradiction



example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=    by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=

  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    _ ↔ ∃ n : ℤ, ¬ ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2 :=    by rel [not_forall]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m ∧ m < (n + 1) ^ 2) :=   by rel [not_exists]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ n ^ 2 < m ∨ ¬ m < (n + 1) ^ 2 :=  by rel [not_and_or]
    _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=      by rel[not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m

-- ∀ m n: ℤ ¬∀ t : ℝ, m < t ∧ t < n
-- ∀ m n: ℤ, ∃ t : ℝ, ¬ (m < t ∧ t < n)
-- ∀ m n: ℤ, ∃ t : ℝ, m ≥ t ∨ t ≥ n -- close but lean reverse t ≤ m ∨ n ≤ t for some reason
#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
-- ∃ a: ℕ, ∀ x y: ℕ, ¬ (x * y ∣ a → x ∣ a ∧ y ∣ a)
-- ∃ a: ℕ, ∀ x y: ℕ, ¬ x * y ∣ a ∨ ¬ y ∣ a
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
-- ∃ m : ℤ ¬ (m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
-- ∃ m : ℤ ¬ (m ≠ 2) ∨ ¬ ∃ n: ℤ, n ^ 2 = m NOPE!
-- ∃ m : ℤ, m = 2 ∨ ∀ n: ℤ, n² ≠ m
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
-- got the one above wrong, so by hand:
example: ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ (m : ℤ), m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m := by
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
    _ ↔ ∃ m : ℤ,  ¬ (m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel[not_forall]
    _ ↔ ∃ m : ℤ,  m ≠ 2 ∧  ¬ ∃ n : ℤ, n ^ 2 = m := by rel[not_imp] -- <--!
    _ ↔ ∃ m : ℤ,  m ≠ 2 ∧ ∀ n : ℤ, ¬ n ^ 2 = m := by rel[not_exists]
    _ ↔ ∃ (m : ℤ), m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m := by rfl




example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  -- It suffices to prove that for any n ∈ N, n² ≠ 2
  push_neg
  -- Let n be arbitrary
  intro n
  -- Consider the cases n ≤ 1 and 2 ≤ n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  ·
    -- suppose n ≤ 1. It suffices to prove that n² < 2
    apply ne_of_lt
    -- Since n ≤ 1, n² ≤ 1² < 2
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  ·
    -- suppose n ≥ 2. It suffices to prove that n² ≥ 4
    apply ne_of_gt
    -- Since n ≥ 2, n > 1
    have h1: n > 1 := hn
    calc n ^ 2
      _ = n * n := by ring
      _ ≥ 2 * n := by rel [hn]
      _ > 2 * 1:= by rel [h1]
      _ = 2 := by ring


/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  sorry

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  sorry

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  sorry

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  sorry

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  sorry

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  sorry

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  sorry

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  sorry

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    sorry
  sorry
