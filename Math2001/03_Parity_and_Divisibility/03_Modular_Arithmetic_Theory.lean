/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  dsimp [Int.ModEq, (.∣.)]
  use x - y
  calc a - c - (b - d)
    _ = (a - b) - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring

theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  use - x
  calc - a - (- b)
    _ = - (a - b) := by ring
    _ = - (n * x) := by rw [hx]
    _ = n * -x := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring


theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring


theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  dsimp [Int.ModEq, . ∣ .]
  use x * (a ^ 2 + a * b + b ^ 2)

  calc a ^ 3 - b ^ 3
    _ = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = (n * x) * (a ^ 2 + a * b + b ^ 2) := by rw[hx]
    _ = n * (x * (a ^ 2 + a * b + b ^ 2)) := by ring


theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] :=
  sorry -- we'll prove this later in the book


theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2) =
        (a - 2) * (b ^ 2 + a * b + 2 * b + 3) :=
      by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring

-- this requires less thinking, you gotta be kidding. god forbid.
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.pow
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply ha

/-! # Exercises -/


example : 34 ≡ 104 [ZMOD 5] := by
  use -14; numbers


theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use - x
  calc b - a
    _ = - 1 * (a - b) := by ring
    _ = -1 * (n * x) := by rw [hx]
    _ = n * -x := by ring

theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1 -- a - b = n ⬝ x
  obtain ⟨y, hy⟩ := h2 -- b - c = n ⬝ y
  -- goal: ∃ z ∈ Z | a - c = n ⬝ z
  use x + y
  calc  a - c
    _ = (a - b) + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

example : a + n * c ≡ a [ZMOD n] := by
  -- goal: ∃z∈ ℤ | a + n ⬝ c - a = n ⬝ z
  use c
  calc a + n * c - a = n * c := by ring


example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  -- h: ∃ c ∈ ℤ | a - b = 5c
  obtain ⟨c, hc⟩ := h
  -- goal ∃ d ∈ Z | 2 ⬝ a + 3 - (2 ⬝ b + 3) = d ⬝ c
  use 2 * c
  calc  2 * a + 3 - (2 * b + 3)
    _ = 2 * (a - b) := by ring
    _ = 2 * (5 * c) := by rw [hc]
    _ = 5 * 2 * c := by ring


example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  -- ∃ x ∈ ℤ | m - n = 4x
  obtain ⟨x, hx⟩ := h
  -- goal: ∃ y ∈ Z with 3m - 1 - (3n - 1) = 4 y
  dsimp [Int.ModEq, . ∣ .]
  use 3 * x
  calc 3 * m - 1 - (3 * n - 1)
    _ = 3 * (m - n) := by ring
    _ = 3 * (4 * x) := by rw [hx]
    _ = 4 * (3 * x) := by ring


example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
    -- ∃ j ∈ Z | k - 3 = 5 ⬝ j
    obtain ⟨j, hj⟩ := hb
    -- 4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5]
    -- goal ∃ x ∈ ℤ | 4 ⬝ k + k³ + 3 - (4 ⬝ 3 + 3³ + 3) = 5x
    dsimp [Int.ModEq, . ∣ .]
    have h2:=
      calc k
        _ = k - 3 + 3 := by ring
        _ = 5 * j + 3 := by rw [hj]
    use 25 * j ^ 3 + 45 * j ^ 2 + 31 * j
    calc 4 * k + k ^ 3 + 3 - (4 * 3 + 3 ^ 3 + 3)
      _ = 4 * (5 * j + 3) + (5 * j + 3) ^ 3 + 3 - (4 * 3 + 3 ^ 3 + 3) := by rw [h2]
      _ = 125 * j ^ 3 + 225 * j ^ 2 + 155 * j := by ring
      _ = 5 * (25 * j ^ 3 + 45 * j ^ 2 + 31 * j) := by ring

    -- or perhaps there's something which requires less thinking.
