/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Set


#check {n : ℤ | n ≤ 3}


example : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  numbers


namespace Nat
example : 10 ∉ {n : ℕ | Odd n} := by
  dsimp
  rw [← even_iff_not_odd]
  use 5
  numbers
end Nat


example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def] -- optional
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  · numbers
  · numbers


example : {x : ℤ | Int.Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    use l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 6
  right
  constructor
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor <;> numbers
  · use 3
    numbers


example : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  ext n
  dsimp
  constructor
  · -- Proof 8 ∣ n
    intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · -- Proof 8 ∣ 5 ⬝ n
    intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers


example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]

/-! # Exercises -/

/-
example : 4 ∈ {a : ℚ | a < 3} := by
  sorry
-/
example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers


example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7; numbers

/-
example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry
-/
/-
example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry
-/
example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor
  · numbers
  · numbers

example : 11 ∈ {n : ℕ | Odd n} := by
  dsimp; use 5; numbers

/-
example : 11 ∉ {n : ℕ | Odd n} := by
  sorry
-/

example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  dsimp
  intro y
  calc (↑(-3): ℝ)
    _ ≤ 0 := by numbers
    _ ≤ y ^ 2 := by extra
/-
example : -3 ∉ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  sorry
-/

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intro n hn
  obtain ⟨k, hk⟩ := hn
  use 4 * k
  calc n
    _ = 20 * k := hk
    _ = 5 * (4 * k) := by ring

/-
example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry
-/

/-
example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry
-/

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]; push_neg
  use 10
  constructor
  · use 2; numbers
  ·
    apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers

/-
example : {r : ℤ | 3 ∣ r} ⊆ {s : ℤ | 0 ≤ s} := by
  sorry
-/

example : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by
  dsimp [Set.subset_def]; push_neg
  use -3
  constructor
  · use -1; numbers
  · numbers



example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  dsimp [Set.subset_def]
  intro m hm
  have h1: m ^ 3 - 7 * m ^ 2 = ( m ^ 2 - 7 * m) * m := by ring
  rw [h1]

  have h2:=
    calc m
      _ ≥ 10 := hm
      _ > 0 := by numbers

  have h3:  (m ^ 2 - 7 * m) * m ≥ 4 * m ↔  (m ^ 2 - 7 * m) ≥ 4 := mul_le_mul_right h2
  rw [h3]
  have h4: m ^ 2 - 7 * m ≥ 4 ↔ m ^ 2 ≥ 7 * m + 4 := by
    constructor
    · intro h5
      exact Int.add_le_of_le_sub_left h5

    ·
      intro h5
      exact Int.le_sub_left_of_add_le h5

  rw [h4]
  have h6:=
    calc 3 * m
      _ ≥ 3 * 10 := by rel [hm]
      _ > 4 := by numbers
  calc m ^ 2
    _ = m * m := by ring
    _ ≥ 10 * m := by rel [hm]
    _ = 7 * m + 3 * m := by ring
    _ ≥ 7 * m + 4 := by rel [h6]

/-
example : {m : ℤ | m ≥ 10} ⊈ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  sorry
-/

namespace Int
example : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  ext x
  dsimp
  constructor
  ·
    intro hx
    obtain ⟨c, hc⟩ := hx
    use c - 3
    calc x - 6
      _ = 2 * c - 6 := by rw [hc]
      _ = 2 * (c - 3) := by ring
  ·
    intro hx
    obtain ⟨c, hc⟩ := hx
    use c + 3
    calc x
      _ = x - 6 + 6 := by ring
      _ = 2 * c + 6 := by rw [hc]
      _ = 2 * (c + 3) := by ring

/-
example : {n : ℤ | Even n} ≠ {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry
-/
end Int

/-
example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {4} := by
  sorry
-/
example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by
  ext; dsimp; push_neg
  use 1
  left
  constructor
  · numbers
  · numbers

/-
example : {k : ℤ | 8 ∣ 6 * k} = {l : ℤ | 8 ∣ l} := by
  sorry
-/
example : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by
  ext; dsimp; push_neg
  use 4
  left
  constructor
  · use 3; numbers
  · apply Int.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers


example : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  ext k
  dsimp
  constructor
  ·
    intro hk
    obtain ⟨c, hc⟩ := hk -- 9k = 7c
    use 4 * k - 3 * c
    calc k
      _ = 7 * (4 * k) - 3 * (9 * k) := by ring
      _ = 7 * (4 * k) - 3 * (7 * c) := by rw [hc]
      _ = 7 * (4 * k - 3 * c) := by ring
  ·
    intro hk
    obtain ⟨c, hc⟩ := hk -- k = 7 * c
    dsimp [·  ∣ · ]
    use 9 * c
    calc 9 * k
      _ = 9 * (7 * c) := by rw [hc]
      _ = 7 * (9 * c) := by ring

/-
example : {k : ℤ | 7 ∣ 9 * k} ≠ {l : ℤ | 7 ∣ l} := by
  sorry
-/

/-
example : {1, 2, 3} = {1, 2} := by
  sorry
-/
example : {1, 2, 3} ≠ {1, 2} := by
  ext; dsimp; push_neg
  use 3
  left
  constructor
  · right; right; numbers
  · constructor
    · numbers
    · numbers

example : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  dsimp
  constructor
  ·
    intro hx
    have h1: x ^ 2 + 3 * x + 2 = (x + 1) * (x + 2) := by ring
    rw [h1] at hx
    obtain h2 | h2 := zero_eq_mul.mp hx.symm
    ·
      left;
      have h3: x = -1 := by addarith [h2]
      apply h3
    ·
      right
      have h4: x = -2 := by addarith [h2]
      apply h4
  ·
    intro h5
    obtain h6 | h6 := h5
    ·
      calc x ^ 2 + 3 * x + 2
        _ = (-1) ^ 2 + 3 * (-1) + 2 := by rw [h6]
        _ = 0 := by numbers

    ·
      calc x ^ 2 + 3 * x + 2
        _ = (-2) ^ 2 + 3 * (-2) + 2 := by rw [h6]
        _ = 0 := by numbers
