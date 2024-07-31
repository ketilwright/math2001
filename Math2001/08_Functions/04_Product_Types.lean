/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
--import Mathlib.Data.Prod.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function



def q (m : ℤ) : ℤ × ℤ := (m + 1, 2 - m)

-- #eval [q (-3), q (-2), q (-1), q (0), q (1), q (2), q (3)]
-- [(-2, 5), (-1, 4), (0, 3), (1, 2), (2, 1), (3, 0), (4, -1)]

example : Injective q := by
  dsimp [Injective]
  intro m1 m2 hm
  dsimp [q] at hm
  -- new trick usage of obtain
  -- I think this may be similar to Prod.mk.inj_iff
  obtain ⟨hm', hm''⟩ := hm
  -- eq: rewrite [Prod.mk.inj_iff] at hm: hm is now a conjeunction of
  addarith [hm']


example : ¬ Surjective q := by
  dsimp [Surjective]
  push_neg
  use (0, 1)
  intro m hm
  dsimp [q] at hm
  obtain ⟨hm1, hm2⟩ := hm
  have H : 1 = -1 := by addarith [hm1, hm2]
  numbers at H


example : Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m + 2 * n)) := by
  rw [bijective_iff_exists_inverse]
  -- now show the the function has an inverse
  use fun (a, b) ↦ (2 * a - b, b - a)
  constructor
  · ext ⟨m, n⟩
    dsimp
    ring
  · ext ⟨a, b⟩
    dsimp
    ring


example : Bijective (fun ((m, n) : ℝ × ℝ) ↦ (m + n, m - n)) := by
  rw [bijective_iff_exists_inverse]

  /- Scratch work:
    a = m + n
    b = m - n
    a + b = (m + n) + (m - n)
          = 2m
    a - b = (m + n) - (m - n)
          = 2 n
    So (m, n) ↦ ((a + b) / 2, (a - b) / 2)
  -/
  use fun (a, b) ↦ ((a + b) / 2, (a - b) / 2)
  constructor
  · ext ⟨m, n⟩
    dsimp
    ring
  · ext ⟨m, n⟩
    dsimp
    ring

-- Whole different ball game over Z:
example : ¬ Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m - n)) := by
  dsimp [Bijective, Injective, Surjective]
  push_neg
  -- Show f is not onto
  right
  -- Since there is no f(m,n) = (0, 1)
  use (0, 1)
  -- not angle brackets this time.
  intro (m, n) h
  dsimp at h
  -- splits into h1: m + n = 0 and h2: m - n = 1
  obtain ⟨h1, h2⟩ := h

  -- have :=
  -- calc 0 ≡ 2 * m [ZMOD 2] := by extra
  --   _ = (m - n) + (m + n) := by ring
  --   _ = 1 + 0 := by rw [h1, h2]
  --   _ = 1 := by numbers
  -- numbers at this

  -- another approach
  have h3: (2: ℤ) ∣  1 := by
    use m
    calc 1
      _ = m - n := by rw [h2]
      _ = m + m := by addarith [h1]
      _ = 2 * m := by ring

  have h4: ¬(2: ℤ) ∣ 1 := by
    apply Int.not_dvd_of_exists_lt_and_lt
    use 0; constructor; numbers; numbers
  contradiction

example : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x - y, y)) := by
  intro (x1, y1) (x2, y2) h
  dsimp at h
  obtain ⟨h, h', hy⟩ := h
  constructor -- note use of ctor tactiv to reduce goal of eq in prod type
  · addarith [h, hy]
  · apply hy


example : ¬ Injective (fun ((x, y) : ℝ × ℝ) ↦ x + y) := by
  dsimp [Injective]
  push_neg
  use (0, 0), (1, -1)
  dsimp
  constructor
  · numbers
  · numbers

example : Surjective (fun ((x, y) : ℝ × ℝ) ↦ x + y) := by
  intro a
  use (a, 0)
  dsimp
  ring


example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 8 * n) := by
  dsimp [Injective]
  push_neg
  use (0, 0), (8, -5)
  constructor
  · numbers
  · numbers

example : Surjective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 8 * n) := by
  intro a
  use (-3 * a, 2 * a)
  dsimp
  ring


example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  dsimp [Injective]; push_neg
  use (2, 0); use (0, 1) -- both map the same place (10)
  constructor
  · ring
  · intro hContra
    obtain ⟨h1, h2⟩ := hContra
    numbers at h1


example : ¬ Surjective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  dsimp [Surjective]
  push_neg
  use 1 -- 5m + 10n can never equal 1
  intro (m, n) h
  dsimp at h
  have :=
  calc 0 ≡ 5 * (m + 2 * n) [ZMOD 5] := by extra
    _ = 5 * m + 10 * n := by ring
    _ = 1 := h
  numbers at this


def g : ℝ × ℝ → ℝ × ℝ
  | (x, y) => (y, x)

example : g ∘ g = id := by
  ext ⟨x, y⟩
  dsimp [g]


def A : ℕ → ℕ
  | 0 => 0
  | n + 1 => A n + n + 1

-- #eval [A 0, A 1, A 2, A 3, A 4, A 5] -- triangle numbers

theorem A_mono {n m : ℕ} (h : n ≤ m) : A n ≤ A m := by
  induction_from_starting_point m, h with k hk IH
  · extra
  · calc A n ≤ A k := IH
      _ ≤ A k + (k + 1) := by extra
      _ = A k + k + 1 := by ring
      _ = A (k + 1) := by rw [A]


theorem of_A_add_mono {a1 a2 b1 b2 : ℕ} (h : A (a1 + b1) + b1 ≤ A (a2 + b2) + b2) :
    a1 + b1 ≤ a2 + b2 := by

  -- le_or_lt on N would ordinarily say a₁ + b₁ ≤ a₂ + b₂ or a₂ + b₂ < a₁ + b₁
  -- but it looks like you can add 1 to the lhs & use ≤
  obtain h' | h' : _ ∨ a2 + b2 + 1 ≤ a1 + b1 := le_or_lt (a1 + b1) (a2 + b2)

  · -- by assumption a₁ + b₁ ≤ a₂ + b₂
    apply h'
  · -- Suppose a₂ + b₂ + 1 ≤ a₁ + b₁
    rw [← not_lt] at h -- converts to negative, & proceeds to contradict
    have :=
    calc A (a2 + b2) + b2
      < A (a2 + b2) + b2 + (a2 + 1) := by extra
      _ = A (a2 + b2) + (a2 + b2) + 1 := by ring
      _ = A ((a2 + b2) + 1) := by rw [A]
      _ = A (a2 + b2 + 1) := by ring
      _ ≤ A (a1 + b1) := A_mono h'
      _ ≤ A (a1 + b1) + b1 := by extra
    contradiction


def p : ℕ × ℕ → ℕ
  | (a, b) => A (a + b) + b


def i : ℕ × ℕ → ℕ × ℕ
  | (0, b) => (b + 1, 0)
  | (a + 1, b) => (a, b + 1)

theorem p_comp_i (x : ℕ × ℕ) : p (i x) = p x + 1 := by
  match x with
  | (0, b) =>
    calc p (i (0, b)) = p (b + 1, 0) := by rw [i]
      _ = A ((b + 1) + 0) + 0 := by dsimp [p]
      _ = A (b + 1) := by ring
      _ = A b + b + 1 := by rw [A]
      _ = (A (0 + b) + b) + 1 := by ring
      _ = p (0, b) + 1 := by dsimp [p]
  | (a + 1, b) =>
    calc p (i (a + 1, b)) = p (a, b + 1) := by rw [i] ; rfl -- FIXME
      _ = A (a + (b + 1)) + (b + 1) := by dsimp [p]
      _ = (A ((a + 1) + b) + b) + 1 := by ring
      _ = p (a + 1, b) + 1 := by rw [p]

example : Bijective p := by
  constructor
  · intro (a1, b1) (a2, b2) hab
    dsimp [p] at hab
    have H : a1 + b1 = a2 + b2
    · apply le_antisymm
      · apply of_A_add_mono
        rw [hab]
      · apply of_A_add_mono
        rw [hab]
    have hb : b1 = b2
    · zify at hab ⊢
      calc (b1:ℤ) = A (a2 + b2) + b2 - A (a1 + b1) := by addarith [hab]
        _ = A (a2 + b2) + b2 - A (a2 + b2) := by rw [H]
        _ = b2 := by ring
    constructor
    · zify at hb H ⊢
      addarith [H, hb]
    · apply hb
  · apply surjective_of_intertwining (x0 := (0, 0)) (i := i)
    · calc p (0, 0) = A (0 + 0) + 0 := by dsimp [p]
        _ = A 0 := by ring
        _ = 0 := by rw [A]
    · intro x
      apply p_comp_i

/-! # Exercises -/


example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (a + b, a)
  constructor
  · ext ⟨r, s⟩
    dsimp
    ring
  · ext ⟨r, s⟩
    dsimp
    ring




example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]; push_neg
  use ⟨(0: ℤ), (1: ℤ)⟩; use ⟨(-2: ℤ), (0: ℤ)⟩
  dsimp
  constructor
  ·
    numbers
  ·
    numbers


example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intro b
  use (b + 1, 0)
  dsimp
  ring


example : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective]; push_neg
  use (-1: ℚ)
  intro ⟨x, y⟩
  dsimp
  have h3:=
    calc x ^ 2 + y ^ 2
      _ ≥ 0 + 0 := by rel [sq_nonneg x, sq_nonneg y]
      _ = 0 := by numbers
  intro hContra
  rw [hContra] at h3
  numbers at h3


example : Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 - y ^ 2) := by
  sorry

example : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by
  sorry

example : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

example : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  sorry

def h : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | (x, y, z) => (y, z, x)

example : h ∘ h ∘ h = id := by
  sorry
