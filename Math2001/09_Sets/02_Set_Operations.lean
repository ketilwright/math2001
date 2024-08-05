/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right -- suppose t ≤ 0
    addarith [h] -- I keep forgetting addarith can be used for this
  · left
    addarith [h]

/-
example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry
-/

example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust -- what else will this magic bullet do?


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-2, -1, 2, 3, 4} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0, 2, 4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = ∅ := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨y, hy⟩ := hx -- hy: x - 7 = 10y
  constructor
  ·
    use 5 * y + 3
    calc x - 1
      _ = x - 7 + 6 := by ring
      _ = 10 * y + 6 := by rw [hy]
      _ = 2 * (5 * y + 3) := by ring
  ·
    use 2 * y + 1
    calc x - 2
      _ = x - 7 + 5 := by ring
      _ = 10 * y + 5 := by rw [hy]
      _ = 5 * (2 * y + 1) := by ring


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use 2 * a - 3 * b
  calc x
    _ = 16 * x - 15 * x := by ring
    _ = 16 * (5 * a) - 15 * x := by rw [ha]
    _ = 16 * (5 * a) - 15 * (8 * b) := by rw [hb]
    _ = 80 * a - 120 * b := by ring
    _ = 40 * (2 * a - 3 * b) := by ring


-- TODO: see about doing this without so much contradiction
example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro x hx
  dsimp [Int.ModEq]
  dsimp [· ∣ · ]
  push_neg
  intro c
  intro hContra

  obtain h1 | h1 := hx
  · -- suppose 3 ∣ x
    obtain ⟨k, hk⟩ := h1
    have h2: 3 ∣ x ^ 2 := by use 3 * k ^ 2; rw [hk]; ring
    have h3: ¬ 3 ∣ (x ^ 2) - 1 := by
      intro hContra1
      have h4: 3 ∣ (-1) := (Int.dvd_add_right h2).mp hContra1
      have h5: ¬ 3 ∣ (-1) := by
        apply Int.not_dvd_of_exists_lt_and_lt
        use (-1)
        constructor
        · numbers
        · numbers
      contradiction

    have h6: 3 ∣ (x ^ 2 - 1) := by
      dsimp [· ∣ · ]
      use 2 * c
      calc x ^ 2 - 1
        _ = 3 * 2 * c := hContra
        _ = 3 * (2 * c) := mul_assoc 3 2 c
    contradiction
  ·
    obtain ⟨k, hk⟩ := h1
    have h7: 2 ∣ x ^ 2 := by use 2 * k ^ 2; rw [hk]; ring
    have h8: ¬ 2 ∣ (x ^ 2 - 1) := by
      intro hContra2
      have h9: 2 ∣ (-1) := (Int.dvd_add_right h7).mp hContra2
      have h10: ¬ 2 ∣ (-1) := by
        apply Int.not_dvd_of_exists_lt_and_lt
        use (-1)
        constructor
        · numbers
        · numbers
      contradiction
    -- Int.mul_comm (a b : ℤ) : a * b = b * a
    have h11: 2 ∣ x ^ 2 - 1 := by
      use 3 * c
      calc x ^ 2 - 1
        _ = (3 * 2) * c := hContra
        _ = 2 * (3 * c) := by ring
    contradiction


def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  dsimp [SizeAtLeastTwo] at hs
  dsimp [SizeAtLeastTwo] at ht
  dsimp [SizeAtLeastTwo] at hst; push_neg at hst

  obtain ⟨s₁, s₂, ⟨hs₁nes₂, hs₁_in_s, hs₂_in_s⟩ ⟩ := hs
  obtain ⟨t₁, t₂, ⟨ht₁net₂, ht₁_in_t, ht₂_in_t⟩ ⟩ := ht
  dsimp [SizeAtLeastThree]
  obtain h1 | h1 | h1 := hst s₁ t₁
  · -- suppose s₁ = t₁
    use s₂, t₁, t₂
    constructor
    · -- s₂ ≠ t
      -- Since s₁ = t₁ and s₁ ≠ s₂, s₂ ≠ t
      exhaust
    · constructor
      ·
        have: _ := hst s₁ s₂
        -- Since ¬ | S ∩ T | ≥ 2, thus either
        --    (1) s₁ = s₂ or
        --    (2) (s₁ ∉ s ∨ s₁ ∉ t) or
        --    (3) (s₂ ∉ s ∨ s₂ ∉ t)
        -- Case 1 is a contradiction of h1
        -- The left disjunct of (2) is a contradiction with hs₁_in_s : s₁ ∈ s
        -- the left disjunct of (3) is a contradiction with hs₂_in_s : s₂ ∈ s
        -- Therefore either s₁ or s₂ is not in T
        -- But since s₁ = t₁ and t₁ ∈ T, thus s₁ ∈ T, therefore we
        -- know that S ∪ T is at least {s₁, t₁ = s₁, t₂}
        -- Thus S ∪ T has at least 3 elements
        exhaust
      · constructor
        · apply ht₁net₂ -- by assumption t₁ ≠ t₂
        · constructor
          · left; apply hs₂_in_s -- by assumption, s₂ ∈ S
          · constructor
            · right; apply ht₁_in_t -- by assumption, t₂ ∈ T
            · right; apply ht₂_in_t -- by assumption, t₂ ∈ T
  ·
    obtain h2 | h2 := h1
    · contradiction
    · use s₁, t₁, t₂
      exhaust
  ·
    obtain h3 | h3 := h1
    · use t₁, s₁, s₂
      exhaust
    · contradiction
