/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd] -- dsimp = "definitional simplify"
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  use -2; numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at * -- unfold def of Odd everywhere
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  obtain ⟨j, h1⟩ := hn
  use 7 * j + 1
  calc 7 * n - 4
    _ = 7 * (2 * j + 1) - 4 := by rw [h1]
    _ = 2 * (7 * j + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx -- ∃a | x = 2a + 1
  obtain ⟨b, hb⟩ := hy -- ∃b | y = 2b + 1
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring
  -- thus ∃n = a + b + 1 | x + y + 1 is odd


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx -- ∃a | x = 2a + 1
  obtain ⟨b, hb⟩ := hy -- ∃b | y = 2b + 1
  use 2 * a * b + 3 * b + a + 1
  calc x * y + 2 * y
    _ = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 4 * a * b + 2 * a + 2 * b + 1 + 4 * b + 2 := by ring
    _ = 4 * a * b + 6 * b + 2 * a + 3 := by ring
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring



example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨a, ha⟩ := hm -- ∃a | m = 2a + 1
  dsimp [Even]
  use 3 * a - 1
  calc 3 * m - 5
    _ = 3 * (2 * a + 1) - 5 := by rw[ha]
    _ = 6 * a - 2 := by ring
    _ = 2 * (3 * a - 1) := by ring


example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨x, hx⟩ := hn -- n = 2 * x
  use 2 * x ^ 2 + 2 * x - 3
  -- seems unsportsmanlike to just use ring
  rewrite [hx]
  ring


example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn -- suppose n is even
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn -- suppose n is odd
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use - 5
  numbers

example : Even (26 : ℤ) := by
  use 13
  ring

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use (a + b)
  rewrite [ha, hb];
  ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  use a - b - 2
  rewrite [ha, hb]
  ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use 3 * x + y - 1
  rewrite [hx, hy]
  ring


example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  use 3 * a - 5 * b - 1
  rewrite [ha, hb]
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  use 4 * a ^ 3 + 6 * a ^ 2 + 3 * a
  rewrite [ha]
  ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hn
  rewrite [ha]
  use 2 * a ^ 2 - a
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at *
  obtain ⟨x, hx⟩ := ha
  rewrite [hx]
  use 2 * x ^ 2 + 4 * x - 1
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  obtain ⟨x, hx⟩ := hp
  rewrite [hx]
  use 2 * x ^ 2 + 5 * x - 1
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rewrite [ha, hb]
  use 2 * a * b + a + b
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  -- The first 2 terms of 3n² + 3n - 1 = 3n(n+1) which is even
  have h1: Even (3 * n ^ 2 + 3 * n) := by
    have h2: 3 * n ^ 2 + 3 * n = 3 * n * (n + 1) := by ring
    rewrite [h2]
    -- n must be even or odd
    obtain h3 | h3 := Int.even_or_odd n
    -- suppose n is even
    obtain ⟨j, hj⟩ := h3
    rewrite [hj]
    use 6 * j ^ 2 + 3 * j
    ring
    -- suppose n is odd
    obtain ⟨j, hj⟩ := h3
    use 6 * j ^ 2 + 9 * j + 3
    rewrite [hj]
    ring
    done
  -- Since 3n² + 3n is even, 3n² + 3n - 1 is odd
  obtain ⟨x, hx⟩ := h1
  rewrite [hx]
  use x - 1
  ring


example (n : ℤ) : ∃ m ≥ n, Odd m := by
  -- n is either even or odd
  obtain h1 | h1 := Int.even_or_odd n
  -- suppose n is even, and choose k | n = 2k
  obtain ⟨k, hk⟩ := h1
  -- the n + 1 = 2 k + 1 is a "witness"
  use n + 1
  constructor
  apply le.intro 1 rfl
  use k; rewrite [hk]; ring
  -- suppose n is odd, and choose k ∣ n = 2k + 1
  obtain ⟨k, hk⟩ := h1
  --  n is a witness that k is odd
  use n
  constructor
  apply Int.le_refl n
  use k; apply hk

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  sorry
