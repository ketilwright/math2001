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
  by_cases hp : P
  · constructor
    · intro _; apply hp
    · intro _; intro h; contradiction
  · constructor
    · intro _; contradiction
    · intro _; intro h; contradiction


example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  ·
    intro h
    constructor
    ·
      by_cases hp: P
      · apply hp
      ·
        by_cases hq: Q
        · have hp_imp_q: P → Q := by intro _; apply hq
          contradiction
        · have hp_imp_q: P → Q := by intro hp2; contradiction
          contradiction
    ·
      by_cases hq: Q
      ·
        by_cases hp: P
        · have hp_imp_q: P → Q := by intro _; apply hq
          contradiction
        · have hp_imp_q: P → Q := by intro hp2; contradiction
          contradiction
      ·
        apply hq
  ·
    intro h
    obtain ⟨hp, hq⟩ := h
    have h1: ¬(P → Q) := by
      intro hContra
      have h2: P → Q := by intro _; apply hContra hp
      have h3: Q := h2 hp
      contradiction
    apply h1

-- TODO: come back & see if some of these double negations can be avoided
example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  -- We consider the cases of (1) ∃ x ¬ P(x) or (2) ¬ ∃ x ¬ P(x)
  by_cases h1: ∃ x, ¬ P x
  · -- Case (1) Suppose ∃ x ¬ P(x)
    constructor
    ·
    -- (→) Then ∃ x ¬ P(x)
      intro _; apply h1
    ·
    -- (←) Proof that ∃x ¬P(x) → ¬ ∀x P(x)
      intro _;
    -- Since ∃ x ¬ P(x), choose x such that ¬P(x)
      obtain ⟨x, hx⟩ := h1
    -- Suppose for a contradiction that ∀ x P(x)
      intro hContra
    --  Since ∀ x P(x), P(x)
      have h2: P x := hContra x
    -- Thus we reach the contradiction P(x) and ¬ P(x),
      contradiction
    -- Since ∀ x P(x) leads to a contradiction, ¬ ∀ x P(x)
  -- Therefore ∃ x, ¬ P x → ¬ ∀ x P(x)
  · -- Case (2) Suppose ¬ ∃ x ¬ P(x)
    constructor
    · -- (→) Proof that ¬∀xP(x) → ∃x¬P(x)
      -- Suppose ¬ ∀ x P(x).
      intro h3
      -- We will show this cannot happen:
      have h4: ∀ x, P x := by
      --  Let x be arbitrary, and consider the cases (2.1) P(x) or (2.2) ¬P(x)
        intro x
        by_cases h5: P x
        · --  Case (2.1). Suppose P(x). Then P(x) is true
          apply h5
        · -- Case (2.2). Suppose ¬P(x). This case cannot happen since
          -- then x is a witness for ∃x ¬P(x), which contradicts ¬∃x¬P(x)
          have h6: ∃ x, ¬ P x := by use x; apply h5
          contradiction
      -- Therefore ∀xP(x) leads to a contradiction
      contradiction
    ·
    -- Suppose ∃x ¬P(x)
      intro h7
    --  Then we can choose x with ¬ P(x)
      obtain ⟨x, hx⟩ := h7
    --  Since ¬P(x), it follows that ¬∀xP(x)
      have h8: ¬ ∀ x, P x := by
        intro h9
        have h10: P x := h9 x
        contradiction
      apply h8
    -- Since ∃ x, ¬ P x → ¬ ∀ x P(x) and ¬ ∀ x P(x) → ∃ x, ¬ P x
    -- thus ¬ [∀ x, P(x)] ↔ [∃ x, ¬ P(x)]


example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=

  calc (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    _ ↔ ¬ ∀ a b : ℤ, (a * b = 1 → (a = 1 ∨ b = 1)) := by rfl -- for precedence clarification
    _ ↔ ∃ a: ℤ, (¬ ∀ b: ℤ, (a * b = 1 → (a = 1 ∨ b = 1))) := by rel [not_forall]
    _ ↔ ∃ a: ℤ, (∃ b: ℤ, ¬ (a * b = 1 → (a = 1 ∨ b = 1))) := by rel [not_forall] -- can this be consolidated?
    _ ↔ ∃ a b : ℤ, ¬(a * b = 1 → (a = 1 ∨ b = 1)) := by rfl
    _ ↔ ∃ a b : ℤ, (a * b = 1 ∧ ¬(a = 1 ∨ b = 1)) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by rel [not_or]


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
