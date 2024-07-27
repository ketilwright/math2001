/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true
set_option pp.rawOnError true
open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`

-- \mapsto makes ↦
#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`

-- #check Injective ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

-- #check Surjective ∀ b, ∃ a, f a = b

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust


-- f(x) = x³ is 1:1
example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  dsimp [Injective]
  intro x y hxy
  calc x
    _ = x - 12 + 12 := by ring
    _ = y - 12 + 12 := by rw [hxy]
    _ = y := by ring

/-
example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry
-/

/-
example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry
-/
example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]; push_neg
  use 0; use 42
  constructor; numbers; numbers


example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x y hxy
  -- 3 * x - 1 = 3 * y - 1

  calc x
    _ = (3 * x - 1 - 2) / 3 + 1 := by ring
    _ = (3 * y - 1 - 2) / 3 + 1 := by rw [hxy]
    _ = y := by ring


/-

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry
-/

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x y hxy
  -- 3 * x - 1 = 3 * y - 1
  have h1: 3 * x = 3 * y := by addarith [hxy]
  cancel 3 at h1
/-
example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry
-/

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro b; use b / 2; ring


/-
example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry
-/

/-
example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry
-/

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]; push_neg
  use 1
  intro a
  have h1: Odd 1 := by use 0; ring
  have h2: Even (2 * a) := by use a; ring
  intro hContra
  have h3: Even 1 := by rw [←hContra]; apply h2
  have h4: ¬ Even 1 := (odd_iff_not_even 1).mp h1
  contradiction

/-
example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry
-/


theorem sq_ne_two (n : ℤ) : n ^ 2 ≠ 2 := by
  intro hn
  obtain ⟨hn1, hn2⟩ : -2 < n ∧ n < 2
  · apply abs_lt_of_sq_lt_sq'
    ·
      calc n ^ 2
        _ = 2 := hn
        _ < 4 := by numbers
        _ = 2 ^ 2 := by ring
    ·
      numbers
  interval_cases n <;> norm_num at hn

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp [Surjective]; push_neg
  use 2
  intro a
  intro hContra
  have h1:= sq_ne_two a -- (n : ℤ) : n ^ 2 ≠ 2 := by
  norm_cast at h1 -- appears to acknowledge the contradiction


inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

example : ¬ Injective h := by
  dsimp [Injective]; push_neg
  use Musketeer.athos, Musketeer.aramis

  constructor
  ·
    have h1: h athos = jack := rfl
    have h2: h aramis = jack := rfl
    rw [h1, h2];
  ·
    exhaust




example : Surjective h := by
  dsimp [Surjective]
  intro b
  cases b
  · -- suppose b = meg
    use porthos; rfl

  · -- suppose b = jack
    use athos; exhaust --rfl

/-
example : ¬ Surjective h := by
  sorry
-/

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp [Injective]
  intro a b hab
  cases a
  · cases b
    · rfl
    · contradiction
  · cases b
    · contradiction
    · rfl

/-
example : ¬ Injective l := by
  sorry
-/

/-
example : Surjective l := by
  sorry
-/
example : ¬ Surjective l := by
  dsimp [Surjective]; push_neg
  use Musketeer.athos
  intro a; intro hContra
  cases a
  ·
    --have h1: l meg = aramis := by rfl
    contradiction
  ·
    contradiction

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  · -- →
    -- Suppose f is an injection
    intro h1
    dsimp [Injective] at h1
    intro a b hab
    intro hContra
    have h2: a = b := by apply h1 hContra
    contradiction
  · -- ← Suppose ∀ (x1 x2 : X), x1 ≠ x2 → f x1 ≠ f x2
    intro h3
    dsimp [Injective]
    intro a b hab
    have h4: a ≠ b → f a ≠ f b := by apply h3
    exhaust -- no "contrapos :-("


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f; intro hf
  intro a b hab
  dsimp at hab -- gets rid of fun ↦ gibberish
  have h1: f a = f b := by addarith [hab]
  apply hf h1

/-
example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry
-/

/-
example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  sorry

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  sorry

example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  sorry

example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  sorry
-/
