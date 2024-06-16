/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


-- goal of ∃!
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp --gets rid of "fun x → . . . unexplained gibberish"
  constructor
  · -- Existence
    intro a ha -- a ∈ ℚ | a ≥ 1
    intro h1 -- a ≤ 3
    have h2 :=
      calc a - 2
        _ ≥ 1 - 2 := by rel [ha]
        _ = -1 := by numbers
    have h3 :=
      calc a - 2
        _ ≤ 3 - 2 := by rel [h1]
        _ = 1 := by numbers
    calc (a - 2) ^ 2
      _ ≤ 1 ^ 2 := sq_le_sq' h2 h3
      _ = 1 := by ring
  ·
    -- Here we are saying
    --    ∀ y ∈ ℚ
    --      ∀ a ∈ Q, if 1 ≤ a ≤ 3 and (a - y)² ≤ 1 then y = 2
    -- Rather different than the way HTPIwL put it, although equivalent
    intro y hy
    -- this both (1 - y)² ≤ 1 and (3 - y)² ≤ 1
    have h4: (1 - y) ^ 2 ≤ 1 := by apply hy 1; numbers; numbers
    have h5: (3 - y) ^ 2 ≤ 1 := by apply hy 3; numbers; numbers
    -- Since (1 - y)² ≤ 1 and (3 - y)² ≤ 1, (y - 2)² ≤ 0
    have h6 :=
      calc (y - 2) ^ 2
        _ = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + 1 - 2) / 2 := by rel [h4, h5]
        _ = 0 := by numbers
    -- But (y - 2)² ≥ 0, so (y - 2)² = 0, and y = 2
    have h7: (y - 2) ^ 2 ≥ 0 := by extra
    have h8: (y - 2) ^ 2 = 0 := le_antisymm h6 h7
    addarith [pow_eq_zero h8]

-- The only rational number with a unique √ is 0
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  -- hx is a unique existential
  obtain ⟨a, ha1, ha2⟩ := hx
  -- ha1: a² = x
  -- ha2: ∀ (y : ℚ), (fun a ↦ a ^ 2 = x) y → y = a
  dsimp at ha2 -- gets rid of infoview gibberish & presents -> ∀ (y : ℚ), y ^ 2 = x → y = a
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have h42:=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]

  cancel 5 at h42 -- q > 1
  have h43:=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at h43 -- q < 3
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  ·
    numbers
  ·
    intro y hy
    calc y
      _ = (4 * y - 3 - 9) / 4 + 3 := by ring
      _ = (9 - 9) / 4 + 3 := by rw [hy]
      _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  ·
    intro a
    apply Nat.zero_le a
  ·
    intro y hy
    calc y = 0 := Nat.le_zero.mp (hy 0)

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  sorry
