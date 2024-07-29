/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function


def p (x : ℝ) : ℝ := 2 * x - 5

example : Bijective p := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x1 x2 hx
    dsimp [p] at hx
    calc x1 = ((2 * x1 - 5) + 5) / 2 := by ring
      _ = ((2 * x2 - 5) + 5) / 2 := by rw [hx]
      _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    use (y + 5) / 2
    calc p ((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 := by rfl
      _ = y := by ring



def a (t : ℝ) : ℝ := t ^ 3 - t

example : ¬ Bijective a := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor
  · calc a 0 = 0 ^ 3 - 0 := by rfl
      _ = 1 ^ 3 - 1 := by numbers
      _ = a 1 := by rfl
  · numbers


inductive Celestial
  | sun
  | moon
  deriving DecidableEq

inductive Subatomic
  | proton
  | neutron
  | electron
  deriving DecidableEq

open Celestial Subatomic


def f : Celestial → Subatomic
  | sun => proton
  | moon => electron


example : ¬ Bijective f := by
  dsimp [Bijective]
  push_neg
  right
  dsimp [Surjective]
  push_neg
  use neutron
  intro x
  cases x <;> exhaust


example {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- if `f` is bijective then `∀ y, ∃! x, f x = y`
    intro h y
    obtain ⟨h_inj, h_surj⟩ := h
    obtain ⟨x, hx⟩ := h_surj y
    use x
    dsimp
    constructor
    · apply hx
    · intro x' hx'
      apply h_inj
      calc f x' = y := by rw [hx']
        _ = f x := by rw [hx]
  · -- if `∀ y, ∃! x, f x = y` then `f` is bijective
    intro h
    constructor
    · -- `f` is injective
      intro x1 x2 hx1x2
      obtain ⟨x, hx, hx'⟩ := h (f x1)
      have hxx1 : x1 = x
      · apply hx'
        rfl
      have hxx2 : x2 = x
      · apply hx'
        rw [hx1x2]
      calc x1 = x := by rw [hxx1]
        _ = x2 := by rw [hxx2]
    · -- `f` is surjective
      intro y
      obtain ⟨x, hx, hx'⟩ := h y
      use x
      apply hx

/-
  Celestial: sun & moon
-/
example : ∀ f : Celestial → Celestial, Injective f → Bijective f := by
  intro f hf
  constructor
  · -- `f` is injective by assumption
    apply hf
  -- show that `f` is surjective
  match h_sun : f sun, h_moon : f moon with
  | sun, sun =>
    have : sun = moon
    · apply hf
      rw [h_sun, h_moon]
    contradiction
  | sun, moon =>
    intro y
    cases y
    · use sun
      apply h_sun
    · use moon
      apply h_moon
  | moon, sun =>
    dsimp [Surjective]
    intro y
    cases y
    · use moon; apply h_moon
    · use sun; apply h_sun

  | moon, moon =>
    intro y
    cases y
    ·
      dsimp [Injective] at hf
      rw [←h_moon] at h_sun
      have : sun = moon := by apply hf h_sun
      contradiction
    · use moon; apply h_moon


example : ¬ ∀ f : ℕ → ℕ, Injective f → Bijective f := by
  push_neg
  use fun n ↦ n + 1
  constructor
  · -- the function is injective
    intro n1 n2 hn
    addarith [hn]
  · -- the function is not bijective
    dsimp [Bijective]
    push_neg
    right
    -- specifically, it's not surjective
    dsimp [Surjective]
    push_neg
    use 0
    intro n
    apply ne_of_gt
    extra

/-! # Exercises -/


example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  · -- Proof of injectivity
    intro x y hf
    dsimp at hf -- 4 - 3 * x = 4 - 3 * y
    have h1: - 3 * x = - 3 * y := by addarith [hf] -- addarith only works after dsimp
    cancel -3 at h1
  · -- surjective
    intro x
    dsimp
    use (4 - x) / 3
    ring

/-
example : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry
-/

/-
example : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  sorry
-/

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]; push_neg; left
  dsimp [Injective]; push_neg
  use 0; use -2
  constructor
  · numbers
  · numbers

inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro e₁; intro e₂; intro he
    cases e₁ <;> cases e₂ <;> exhaust
  · dsimp [Surjective]
    intro e₂
    cases e₂
    · use earth; rfl
    · use air; rfl
    · use fire; rfl
    · use water; rfl


example : ∀ f : Subatomic → Subatomic, Injective f → Bijective f := by
  intro f
  intro hfInj
  dsimp [Bijective]
  ·
    constructor
    · -- f is injective by assumption
      apply hfInj
    ·

      dsimp [Surjective]
      match hProt : f proton, hNeut : f neutron, hElec : f electron with
      -- my pet chimpanzee could do this
      | proton, neutron, electron =>
        intro b; cases b
        · use proton; apply hProt
        · use neutron; apply hNeut
        · use electron; apply hElec
      | proton, electron, neutron =>
        intro b; cases b
        · use proton; apply hProt
        · use electron; apply hElec
        · use neutron; use hNeut
      | neutron, proton, electron =>
        intro b; cases b
        · use neutron; apply hNeut
        · use proton; apply hProt
        · use electron; apply hElec
      | neutron, electron, proton =>
        intro b; cases b
        · use electron; apply hElec
        · use proton; apply hProt
        · use neutron; apply hNeut
      | electron, neutron, proton =>
        intro b; cases b
        · use electron; apply hElec
        · use neutron; apply hNeut
        · use proton; apply hProt
      | electron, proton, neutron =>
        intro b; cases b
        · use neutron; apply hNeut
        · use electron; apply hElec
        · use proton; apply hProt
      -- The following are all the non 1:1 cases

      | electron, electron, electron =>
        have _ : neutron = proton := by
          rw [←hProt] at hNeut
          apply hfInj hNeut
        contradiction
      -- the chimpanzee ran out of patience

      | electron, electron, neutron => sorry
      | electron, electron, proton => sorry
      | electron, neutron, electron => sorry
      | electron, neutron, neutron => sorry
      | electron, proton, electron => sorry
      | electron, proton, proton => sorry
      | neutron, electron, electron => sorry
      | neutron, electron, neutron => sorry
      | neutron, neutron, electron => sorry
      | neutron, neutron, neutron => sorry
      | neutron, neutron, proton => sorry
      | neutron, proton, neutron => sorry
      | neutron, proton, proton => sorry
      | proton, electron, electron => sorry
      | proton, electron, proton => sorry
      | proton, neutron, neutron => sorry
      | proton, neutron, proton => sorry
      | proton, proton, electron => sorry
      | proton, proton, neutron => sorry
      | proton, proton, proton => sorry

example : ∀ f : Element → Element, Injective f → Bijective f := by
  sorry
