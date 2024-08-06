/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Set Function


#check {3, 4, 5} -- `{3, 4, 5} : Set ℕ`
#check {n : ℕ | 8 < n} -- `{n | 8 < n} : Set ℕ`
#check {k : ℕ | ∃ a, a ^ 2 = k} -- `{k | ∃ a, a ^ 2 = k} : Set ℕ`


#check {{3, 4}, {4, 5, 6}} -- `{{3, 4}, {4, 5, 6}} : Set (Set ℕ)`
#check {s : Set ℕ | 3 ∈ s} -- `{s | 3 ∈ s} : Set (Set ℕ)`



example : {n : ℕ | Nat.Even n} ∉ {s : Set ℕ | 3 ∈ s} := by
  dsimp
  rw [← Nat.odd_iff_not_even]
  use 1
  numbers


def p (s : Set ℕ) : Set ℕ := {n : ℕ | n + 1 ∈ s}

#check @p -- `p : Set ℕ → Set ℕ`


example : ¬ Injective p := by
  dsimp [Injective, p]
  push_neg
  use {0}, ∅
  dsimp
  constructor
  · ext x
    dsimp
    suffices x + 1 ≠ 0 by exhaust
    apply ne_of_gt
    extra
  · ext
    push_neg
    use 0
    dsimp
    exhaust


def q (s : Set ℤ) : Set ℤ := {n : ℤ | n + 1 ∈ s}

example : Injective q := by
  dsimp [Injective, q]
  intro s t hst
  ext k
  have hk : k - 1 ∈ {n | n + 1 ∈ s} ↔ k - 1 ∈ {n | n + 1 ∈ t} := by rw [hst]
  dsimp at hk
  conv at hk => ring
  apply hk



example : ¬ ∃ f : X → Set X, Surjective f := by
  intro h
  obtain ⟨f, hf⟩ := h
  let s : Set X := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf s
  by_cases hxs : x ∈ s
  · have hfx : x ∉ f x := hxs
    rw [hx] at hfx
    contradiction
  · have hfx : ¬ x ∉ f x := hxs
    rw [hx] at hfx
    contradiction

/-! # Exercises -/


def r (s : Set ℕ) : Set ℕ := s ∪ {3}



example : ¬ Injective r := by
  dsimp [Injective]; push_neg
  use {3}, ∅
  constructor
  ·
    calc r {3}
      _ = {3, 3} := rfl
      _ = {3} := pair_eq_singleton 3
      _ = ∅ ∪ {3} := by rw [empty_union {3}]
      _ = r ∅ := rfl
  ·
    apply singleton_ne_empty 3

namespace Int

def U : ℕ → Set ℤ
  | 0 => univ
  | n + 1 => {x : ℤ | ∃ y ∈ U n, x = 2 * y}





example (n : ℕ) : U n = {x : ℤ | (2:ℤ) ^ n ∣ x} := by
  simple_induction n with k hk
  · rw [U]
    ext n
    constructor
    ·
      intro nInℕ
      dsimp [· ∣ ·]
      use n
      ring
    ·
      intro _
      dsimp
  · -- U (k + 1) = {x | 2 ^ (k + 1) ∣ x}
    rw [U]

    ext x
    dsimp

    constructor
    ·
      intro h1 --  ∃ y ∈ U k, x = 2 * y
      obtain ⟨y, ⟨h2, h3⟩⟩ := h1

      have h4: 2 ^ k ∣ y := by
        rw [hk] at h2
        apply h2
      obtain ⟨c, hc⟩ := h4
      rw [hc] at h3
      have h5: 2 * ((2 ^ k) * c) = 2 ^ (k + 1) * c := by ring
      rw [h5] at h3
      use c
      apply h3
    · -- Suppose 2ᵏ⁺¹ ∣ x
      intro h6
      obtain ⟨c, hc⟩ := h6 -- hc: x = 2 ^ (k + 1) * c
      have h7: 2 ^ k ∣ x := by
        use 2 * c
        calc x
          _ = 2 ^ (k + 1) * c := hc
          _ = 2 ^ k * (2 * c) := by ring
      have h8: x ∈ U k := by
        rw [hk]
        apply h7

      have h9: 2 ^ k ∈ U k := by rw [hk]; use 1; ring

      have h10: 2 ^ k * c ∈ U k := by rw [hk]; use c; ring
      use 2 ^ k * c

      constructor
      ·
        apply h10

      ·
        rw [hc]; ring
