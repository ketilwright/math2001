/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init
set_option pp.funBinderTypes true

open Function


def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := 2 * b
def h (c : ℝ) : ℝ := 2 * c + 6

example : g ∘ f = h := by
  ext x
  calc (g ∘ f) x = g (f x) := by rfl
    _ = 2 * (x + 3) := by rfl
    _ = 2 * x + 6 := by ring
    _ = h x := by rfl


def s (x : ℝ) : ℝ := 5 - x

example : s ∘ s = id := by
  ext x
  dsimp [s]
  ring


def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id


inductive Humour
  | melancholic
  | choleric
  | phlegmatic
  | sanguine
  deriving DecidableEq

open Humour


def p : Humour → Humour
  | melancholic => choleric
  | choleric => sanguine
  | phlegmatic => phlegmatic
  | sanguine => melancholic


def q : Humour → Humour
  | melancholic => sanguine
  | choleric => melancholic
  | phlegmatic => phlegmatic
  | sanguine => choleric

example : Inverse p q := by
  constructor
  · ext x
    cases x <;> exhaust
  · ext x
    cases x <;> exhaust


theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rfl
      _ = f x := by apply hg
      _ = f (id x) := by rfl
  · -- prove `f ∘ g = id`
    ext y
    apply hg


theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl


theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H


/-! # Exercises -/


def a : Humour → Humour
  | melancholic => sanguine
  | choleric => choleric
  | phlegmatic => phlegmatic
  | sanguine => melancholic

def b : Humour → Humour
  | melancholic => phlegmatic
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => sanguine

def c : Humour → Humour
  | melancholic => sanguine
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => phlegmatic

example : b ∘ a = c := by
  ext x
  cases x <;> exhaust


def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  ·
    ext x;
    calc (v ∘ u) x
      _ = v (u x) := by rfl
      _ = ((5 * x + 1) - 1) / 5 := by rw [u, v]
      _ = x := by ring

  .
    ext x
    calc (u ∘ v) x
      _ = u ( v x) := rfl
      _ = 5 * ((x - 1) / 5) + 1 := by rw [u, v]
      _ = x := by ring


example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  intro a b hab
  apply hf (hg hab)


example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  -- let z be arbitrary
  intro z
  -- Since g is onto there is y with g(y) = z
  obtain ⟨y, hy⟩ := hg z
  -- Since f is onto there is x with f(x) = y
  obtain ⟨x, hx⟩ := hf y
  -- Therefore g ∘ f (x) = g (f (x)) = g (y) = z
  use x
  calc g ( f (x))
    _ = g y := by rw [hx]
    _ = z := by rw [hy]


example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at hf
  -- Since f is onto, from AOC there is a function g with
  -- ∀b,f (g (b)) = b
  choose g hg using hf
  use g
  ext x
  calc (f ∘ g) x
    _ = f ( g (x)) := by rfl
    _ = x := by rw [hg]

example {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at h
  dsimp [Inverse]
  obtain ⟨hl, hr⟩ := h
  constructor
  · apply hr
  · apply hl

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
  g1 = g2 := byx
  ext y
  -- Since f has an inverse, f is 1:1 (and onto)
  obtain ⟨hInj_f, hSur_f⟩ := bijective_of_inverse h1
  -- Since f = g₁⁻¹, (f ∘ g₁) = identity
  obtain ⟨_, h4⟩ := h1
  -- Since f = g₂⁻¹, (f ∘ g₂) = identity
  obtain ⟨_, h6⟩ := h2
  -- Thus (f ∘ g₁) = (f ∘ g₂)
  have h7: ∀ y: Y, (f ∘ g1) y = (f ∘ g2) y := by
    intro y₁; rw [h4, h6]
  -- Since f is 1:1 and ∀ y, (f ∘ g₁) y = (f ∘ g₂) y
  -- g₁(y) = g₂(y)
  apply hInj_f (h7 y)
