/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain h1 | h2 := h
    ·
      obtain ⟨h3, h4⟩ := h1
      constructor
      · apply h3
      · left; apply h4
    ·
      obtain ⟨h5, h6⟩ := h2
      constructor
      · apply h5
      · right; apply h6

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


  -- Problem: Work out the truth table for P ↔ (¬ P ∨ Q)

  -- from the ground up:
  -- P → (¬ P ∨ Q)

  -- P   Q  (¬ P ∨ Q)  P → (¬ P ∨ Q)
  -- T   T       T       T
  -- F   T       T       T
  -- T   F       F       F
  -- F   F       T       T

  -- P   Q  (¬ P ∨ Q)  (¬ P ∨ Q) → P
  -- T   T       T       T
  -- F   T       T       F
  -- T   F       F       T
  -- F   F       T       F

  -- Thus
  -- P   Q   [P → (¬ P ∨ Q)] ∧ [(¬ P ∨ Q) → P]
  --                         T
  --                         F
  --                         F
  --                         F

#truth_table P ↔ (¬ P ∨ Q)

example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨h1, h2⟩ := h; left; apply h1

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1 h3
  · apply h2 h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro h3
  obtain ⟨h4, h5⟩ := h1
  have h6: ¬ Q := by apply h4 h3
  contradiction


example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain h3 | h3 := h1
  · apply h3
  · apply h2 h3

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro h3
    obtain ⟨h4, h5⟩ := h3
    constructor
    · apply h1 h4
    · apply h5
  · intro h6
    obtain ⟨h7, h8⟩ := h6
    constructor
    · apply h2 h7
    · apply h8



example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro h1
    obtain ⟨h2, h3⟩ := h1
    apply h2
  ·
    intro h1
    constructor; apply h1; apply h1

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h1
    obtain h2 | h2 := h1
    · right; apply h2
    · left;  apply h2
  · intro h1
    obtain h2 | h2 := h1
    · right; apply h2
    · left; apply h2


example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by exact not_or

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1 x (h2 x)

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  ·
    intro h1
    obtain ⟨x, hx⟩ := h1
    obtain ⟨h2, h3⟩ := h x
    use x
    apply h2 hx
  ·
    intro h1
    obtain ⟨x, hx⟩ := h1
    obtain ⟨h2, h3⟩ := h x
    use x
    apply h3 hx



example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  ·
    intro h1
    obtain ⟨x, hx⟩ := h1
    obtain ⟨y, hy⟩ := hx
    use y, x;
    apply hy
  ·
    intro h1
    obtain ⟨y, hy⟩ := h1
    obtain ⟨x, hx⟩ := hy
    use x, y
    apply hx


example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  ·
    intro h1 -- ∀ (x : α) (y : β), P x y
    intro y
    intro x
    apply h1 x y

  ·
    intro h2
    intro x y
    apply h2 y x



example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  ·
    intro h1
    obtain ⟨h2, h3⟩ := h1
    obtain ⟨x, hx⟩ := h2
    use x
    constructor
    · apply hx
    · apply h3
  · intro h4
    obtain ⟨x, hx⟩ := h4
    obtain ⟨hpx, hq⟩ := hx
    constructor
    · use x; apply hpx
    · apply hq
