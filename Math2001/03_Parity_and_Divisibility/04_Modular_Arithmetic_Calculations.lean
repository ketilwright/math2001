/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  rel [ha]



example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    _ = 2 + 5 * 8 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra


example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra


example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by

  mod_cases hx : x % 3

  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

/-! # Exercises -/

#check Int.ModEq.trans

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] :=
  -- maybe this can be done with a long string of apply(s)
  -- or a single calc
  -- Note: this exercise has no "by"
  have h7n:=
    calc 7 * n
      _ ≡ 7 [ZMOD 3] := Int.ModEq.mul_left hn
      _ ≡ 1 [ZMOD 3] := by use 2; ring
  calc n ^ 3 + 7 * n
    _ ≡ ((1 ^ 3) + 1) [ZMOD 3]:= by exact Int.ModEq.add (Int.ModEq.pow 3 hn) h7n
    _ ≡ 2 [ZMOD 3] := Int.ModEq.refl (1 ^ 3 + 1)


example {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] := --by
    -- 3³ + 4 ⬝ 3² + 2 = 65 ≡₄ 1
    have h: 0 ≡ 64 [ZMOD 4] := by use -16; ring

    calc a ^ 3 + 4 * a ^ 2 + 2
      _ ≡ 3 ^ 3 + 4 * (3 ^ 2) + 2 [ZMOD 4] := by rel [Int.ModEq.pow 3 ha, -- a³ ≡ 3³ [ZMOD 4]
                                                      Int.ModEq.pow 2 ha, -- a² ≡ 3² [ZMOD 4]
                                                      Int.ModEq.mul_left  -- scale above by 4
                                                      (Int.ModEq.pow 2 ha)]
      _ ≡ (64 + 1) [ZMOD 4] := Int.ModEq.refl 2
      _ ≡ (0 + 1) [ZMOD 4] := by exact (Int.ModEq.symm h)
      _ ≡ 1 [ZMOD 4] := Int.ModEq.refl (0 + 1)


-- I added "by" here since I need rw
example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by
  have h1: a ^ 3 + b ^ 3 = a ^ 3 + 0 + 0 + b ^ 3 := by ring
  have h2: (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * b ^ 2 * a + b ^ 3 := by ring
  rw [h1, h2]
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.refl
  use a ^ 2 * b; ring
  use b ^ 2 * a; ring
  apply Int.ModEq.refl

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2; use 1; ring

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6; use 3; ring

example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases hn: n % 2
  obtain ⟨c, hc⟩ := hn
  have h1:=
    calc n
      _ = n - 0 := by ring
      _ = 2 * c := hc
  rw [h1]
  use 10 * c ^ 2 + 3 * c + 3
  ring
  obtain ⟨c, hc⟩ := hn
  have h2:=
    calc n
      _ = n - 1 + 1 := by ring
      _ = 2 * c + 1 := by rw [hc]
  rw [h2]
  use 10 * c ^ 2 + 13 * c + 7
  ring

example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by

  mod_cases hx: x % 5
  -- x ≡ 0 [ZMOD 5]
  calc x ^ 5
    _ ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  -- x ≡ 1 [ZMOD 5]
  calc x ^ 5
    _ ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  -- x ≡ 2 [ZMOD 5]
  calc x ^ 5
    _ ≡ (2 ^ 5) [ZMOD 5] := by rel [hx]
    _ = 32 := by numbers
    _ ≡ 2 [ZMOD 5] := by use 6; ring
    _ ≡ x [ZMOD 5] := by rel [hx]
  -- x ≡ 3 [ZMOD 5]
  calc x ^ 5
    _ ≡ (3 ^ 5) [ZMOD 5] := by rel [hx]
    _ = 243 := by numbers
    _ ≡ 3 [ZMOD 5] := by use 48; ring
    _ ≡ x [ZMOD 5] := by rel [hx]
  -- x ≡ 4 [ZMOD 5]
  calc x ^ 5
    _ ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 1024 := by numbers
    _ ≡ 4 [ZMOD 5] := by use 204; ring
    _ ≡ x [ZMOD 5] := by rel [hx]
