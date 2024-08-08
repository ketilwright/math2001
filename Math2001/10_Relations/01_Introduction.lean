/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init


example : Reflexive ((·:ℕ) ∣ ·) := by
  dsimp [Reflexive]
  intro x
  use 1
  ring


example : ¬ Symmetric ((·:ℕ) ∣ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  · use 2
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers


example : AntiSymmetric ((·:ℕ) ∣ ·) := by
  have H : ∀ {m n}, m = 0 → m ∣ n → m = n
  · intro m n h1 h2
    obtain ⟨k, hk⟩ := h2
    calc m = 0 := by rw [h1]
      _ = 0 * k := by ring
      _ = m * k := by rw [h1]
      _ = n := by rw [hk]
  dsimp [AntiSymmetric]
  intro x y h1 h2
  obtain hx | hx := Nat.eq_zero_or_pos x
  · apply H hx h1
  obtain hy | hy := Nat.eq_zero_or_pos y
  · have : y = x := by apply H hy h2
    rw [this]
  apply le_antisymm
  · apply Nat.le_of_dvd hy h1
  · apply Nat.le_of_dvd hx h2


example : Transitive ((·:ℕ) ∣ ·) := by
  dsimp [Transitive]
  intro a b c hab hbc
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  calc c = b * l := by rw [hl]
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring


example : Reflexive ((·:ℝ) = ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric ((·:ℝ) = ·) := by
  dsimp [Symmetric]
  intro x y h
  rw [h]

example : AntiSymmetric ((·:ℝ) = ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  rw [h1]

example : Transitive ((·:ℝ) = ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  rw [h1, h2]


section
local infix:50 "∼" => fun (x y : ℝ) ↦ (x - y) ^ 2 ≤ 1

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  calc (x - x) ^ 2 = 0 := by ring
    _ ≤ 1 := by numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc (y - x) ^ 2 = (x - y) ^ 2 := by ring
    _ ≤ 1 := by rel [h]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 1.1
  constructor
  · numbers
  constructor
  · numbers
  · numbers

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 1.9, 2.5
  constructor
  · numbers
  constructor
  · numbers
  · numbers

end


section

inductive Hand
  | rock
  | paper
  | scissors

open Hand


@[reducible] def r : Hand → Hand → Prop
  | rock, rock => False
  | rock, paper => True
  | rock, scissors => False
  | paper, rock => False
  | paper, paper => False
  | paper, scissors => True
  | scissors, rock => True
  | scissors, paper => False
  | scissors, scissors => False

local infix:50 " ≺ " => r


example : ¬ Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  push_neg
  use rock
  exhaust

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use rock, paper
  exhaust

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  cases x <;> cases y <;> exhaust

example : ¬ Transitive (· ≺ ·) := by
  dsimp [Transitive]
  push_neg
  use rock, paper, scissors
  exhaust

end

/-! # Exercises -/


example : ¬ Symmetric ((·:ℝ) < ·) := by
  dsimp [Symmetric]; push_neg
  use (0: ℝ); use (1: ℝ)
  constructor
  · numbers
  · numbers

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD 2]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]; push_neg
  use 2; use 4
  constructor
  ·
    use -1; numbers
  · constructor
    ·
      use 1; numbers
    .
      numbers


end


section
inductive Little
  | meg
  | jo
  | beth
  | amy
  deriving DecidableEq

open Little

@[reducible] def s : Little → Little → Prop
  | meg, meg => True
  | meg, jo => True
  | meg, beth => True
  | meg, amy => True
  | jo, meg => True
  | jo, jo => True
  | jo, beth => True
  | jo, amy => False
  | beth, meg => True
  | beth, jo => True
  | beth, beth => False
  | beth, amy => True
  | amy, meg => True
  | amy, jo => False
  | amy, beth => True
  | amy, amy => True

local infix:50 " ∼ " => s

/-
example : Reflexive (· ∼ ·) := by
  sorry
-/
example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]; push_neg
  use beth
  exhaust


example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y hxy
  cases x <;> cases y <;> exhaust

/-
example : ¬ Symmetric (· ∼ ·) := by
  sorry
-/
/-
example : AntiSymmetric (· ∼ ·) := by
  sorry
-/
example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]; push_neg
  use meg; use beth
  exhaust

/-
example : Transitive (· ∼ ·) := by
  sorry
-/
example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]; push_neg
  use jo, beth, amy
  exhaust


end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

/-
example : Reflexive (· ∼ ·) := by
  sorry
-/
example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]; push_neg
  use 1
  intro hContra
  obtain ⟨x, hx⟩ := hContra
  have h2: -1 = 5 * x := by addarith [hx]
  have h3: 5 ∣ (-1) := by use x; apply h2
  have h4: ¬ 5 ∣ (-1) := by
    apply Int.not_dvd_of_exists_lt_and_lt
    use -1; constructor; numbers; numbers
  contradiction

/-
example : Symmetric (· ∼ ·) := by
  sorry
-/
example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]; push_neg
  use 0, 6
  constructor
  ·
    dsimp [Int.ModEq]
    calc 6
      _ ≡ 1 [ZMOD 5] := by use 1; numbers
      _ ≡ 0 + 1 [ZMOD 5] := by numbers
  ·
    intro hContra
    obtain ⟨c, hc⟩ := hContra
    have h1: 5 ∣ -7 := by use c; addarith [hc]
    have h2: ¬ 5 ∣ -7 := by
      apply Int.not_dvd_of_exists_lt_and_lt
      use -2; constructor; numbers; numbers
    contradiction

example : AntiSymmetric (· ∼ ·) := by
  --  let x, y be arbitrary,
  --  Suppose
  --        y ≡ (x + 1) [zmod 5] and
  --        x ≡ (y + 1) [zmod 5]
  --  which leads us to 5 ∣ -2.
  --  Thus our premise is false
  --  and ~ is vacuously antisymmetric
  dsimp [AntiSymmetric]
  intro x y h1 h2
  have h3: 5 ∣ -2 := by
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    use (a + b)
    calc -2
      _ = (y - (x + 1)) + (x - (y + 1)) := by ring
      _ = 5 * a + 5 * b := by rw [ha, hb]
      _ = 5 * (a + b) := by ring
  have h4 : ¬ 5 ∣ -2 := by
    apply Int.not_dvd_of_exists_lt_and_lt
    use -1; constructor; numbers; numbers
  contradiction


/-
example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry
-/

/-
example : Transitive (· ∼ ·) := by
  sorry
-/
example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]; push_neg
  use 0, 6, 12
  constructor
  ·
    use 1; numbers
  · constructor
    ·
      use 1; numbers
    ·
      apply Int.not_dvd_of_exists_lt_and_lt
      use 2
      constructor
      · numbers
      · numbers


end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]
/-
example : Reflexive (· ∼ ·) := by
  sorry
-/
example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]; push_neg
  use 1
  apply Int.not_dvd_of_exists_lt_and_lt
  use 0
  constructor
  · numbers
  · numbers



example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h1
  rw [add_comm]; apply h1

/-
example : ¬ Symmetric (· ∼ ·) := by
  sorry
-/

/-
example : AntiSymmetric (· ∼ ·) := by
  sorry
-/
example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]; push_neg
  use 0, 3
  constructor
  ·
    use 1; numbers
  · constructor
    · use 1; numbers
    · numbers

/-
example : Transitive (· ∼ ·) := by
  sorry
-/

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]; push_neg
  use 1, 2, 1
  constructor
  · use 1; numbers
  · constructor
    · use 1; numbers
    · apply Int.not_dvd_of_exists_lt_and_lt
      use 0
      constructor
      · numbers
      · numbers

end


example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  intro s
  dsimp [Set.subset_def]
  intro x hx; apply hx

/-
example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry
-/

/-
example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry
-/
example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]; push_neg
  use {1}, {1, 2}
  dsimp [Set.subset_def]
  constructor
  ·
    intro n hn; left; apply hn
  · push_neg
    use 2
    exhaust


example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intro s r h1 h2
  dsimp [Set.subset_def] at h1
  dsimp [Set.subset_def] at h2
  ext x
  constructor
  ·
    intro h3;
    apply h1 x h3
  ·
    intro h4
    apply h2 x h4
/-
example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry
-/
example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intro A B C h1 h2
  intro x hx
  apply h2 (h1 hx)

/-
example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
-/


section
local infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)


example : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro (x, y); dsimp

  constructor
  ·
    rw [le_iff_lt_or_eq]; right; rfl
  ·
    rw [le_iff_lt_or_eq]; right; rfl

/-
example : ¬ Reflexive (· ≺ ·) := by
  sorry
-/
/-

example : Symmetric (· ≺ ·) := by
  sorry
-/
example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]; push_neg
  use (2, 4), (3, 5)
  constructor
  ·
    constructor; numbers; numbers
  ·
    left; numbers

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro (x₁, y₁) (x₂, y₂) h1 h2
  dsimp at h1; dsimp at h2
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  calc (x₁, y₁)
    _ = (x₂, y₂) := by rw [ge_antisymm h2l h1l, ge_antisymm h2r h1r]

/-
example : ¬ AntiSymmetric (· ≺ ·) := by
  sorry
-/
example : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro (x₁, y₁) (x₂, y₂) (x₃, y₃) h1 h2
  dsimp at h1; dsimp at h2
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  dsimp
  constructor
  · apply le_trans h1l h2l
  · apply le_trans h1r h2r

/-
example : ¬ Transitive (· ≺ ·) := by
  sorry
-/
end
