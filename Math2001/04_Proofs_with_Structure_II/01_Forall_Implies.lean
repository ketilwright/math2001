/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers


example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.pos_of_dvd_of_pos h1 h2


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1: (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h2 | h2 := h1 -- like "by_cases on" in htpi
  -- suppose (a + b) / 2 ≥ a
  calc b
    _ = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [h2]
    _ = a := by ring
  -- suppose (a + b) / 2 ≤ b
  calc a
    _ = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [h2]
    _ = b := by ring

/-
  Let a, b ∈ ℝ with a², b² at most 2. Prove a = b
-/
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  -- Since ≤ is antisymmetric, we can prove both a ≤ b and b ≤ a
  apply le_antisymm
  -- Proof that a ≤ b
  ·
    -- Since ∀y ∈ ℝ, y² ≤ 2 → y < b, we can prove that a² ≤ 2
    apply hb2
    -- & we were given that a² ≤ 2
    apply ha1
  ·
    -- Since ∀y ∈ ℝ, y² ≤ 2 → y < a, we can prove that b² ≤ 2
    apply ha2
    -- And, we already know b² ≤ 2
    apply hb1



example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x -- "let x be arbitrary": universal instantiation
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring

/-
  Show that there exists c ∈ R s.t. ∀x, y ∈ ℝ, x² + y² ≤ 4 → x + y ≥ c
-/
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x
  intro y
  intro h1 -- x² + y^2 ≤ 4 -- this was not explained, but appears to work

  have h2 :=
    calc (x + y) ^ 2
      _ ≤ (x + y) ^ 2 + (x - y)^ 2 := by extra
      _ = 2 * (x ^ 2 + y ^ 2) := by ring
      _ ≤ 2 * 4 := by rel [h1]
      _ ≤ 3 ^ 2 := by numbers
  -- adding an hypothesis h: 0 ≤ 3 doesn't work
  -- unless you say 0 ≤ (3: ℝ) := by numbers
  have h3: -3 ≤ x + y ∧ x + y ≤ 3 := abs_le_of_sq_le_sq' h2 (by numbers /- 0 ≤ 3-/)
  apply h3.left -- not covered, but this is how HTPIwL handles this sort of thing


example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp -- ∃ C, ∀ x ≥ C, x ^ 3 ≥ 4 * x ^ 2 + 7
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra

-- from the lean source: it appears interval_cases finds w₁ and w₂
-- & based on that changes the goal to 41 = 41 ∨ 41 = 42 ∨ 41 = 43 ∨ 41 = 44
example (n : ℕ) (w₁ : n ≥ 41) (w₂ : n < 45) : n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44:= by
  interval_cases n; left;
  ring;
  right; left;
  ring;
  right; right; left
  ring
  right; right; right; ring



example : Prime 2 := by

  constructor
  · numbers -- show `2 ≤ 2`
  -- let m be arbitrary
  --    Suppose 2 | n
  intro m hmp
  have hp : 0 < 2 := by numbers
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  -- couldn't be expected to work with Q or R since
  -- intervals of those have no lub or glb
  interval_cases m
  · left
    numbers -- show `1 = 1`
  · right
    numbers -- show `2 = 2`


example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! # Exercises -/


example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  calc a
    _ ≥ -3 + 4 * 2 - 2 ^ 2 := h 2
    _ = 1 := by ring
    _ ≥ 1 := by numbers

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h1: 3 ∣ n := by apply hn 3; numbers; numbers
  have h2: 5 ∣ n := by apply hn 5; numbers; numbers
  obtain ⟨a, ha⟩ := h1 -- n = 3a
  obtain ⟨b, hb⟩ := h2 -- n = 2b
  use 2 * a - 3 * b
  calc n
    _ = 10 * n - 9 * n := by ring
    _ = 10 * (3 * a) - 9 * n := by rw [ha]
    _ = 10 * (3 * a) - 9 * (5 * b) := by rw [hb]
    _ = 15 * (2 * a - 3 * b) := by ring

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intro m
  extra


example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 0
  intro b
  use b + 1
  calc 0 + b
    _ = b := by ring
    _ < b + 1 := by extra

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 7; intro x; intro hx -- x ≥ 7
  apply le_of_lt_or_eq
  left
  calc x ^ 3 + 3 * x
    _ = x * x ^ 2 + 3 * x := by ring
    _ ≥ 7 * x ^ 2 + 3 * 7 := by rel [hx]
    _ = (7 * x ^ 2 + 12) + 9 := by ring
    _ > (7 * x ^ 2 + 12) + 0 := by extra
    _ = 7 * x ^ 2 + 12 := by ring

example : ¬(Prime 45) := by
  apply not_prime 3 15
  .numbers
  .numbers
  .numbers
