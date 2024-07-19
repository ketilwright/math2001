/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

open Nat



def pascal : ℕ → ℕ → ℕ
  | a, 0 => 1
  | 0, b + 1 => 1
  | a + 1, b + 1 => pascal (a + 1) b + pascal a (b + 1)
termination_by _ a b => a + b


#eval pascal 2 4 -- infoview displays `15`
#eval pascal 3 4 -- 35

theorem pascal_le (a b : ℕ) : pascal a b ≤ (a + b)! := by
  -- Strong induction relative to a + b
  match a, b with
  | a, 0 =>
      calc pascal a 0 = 1 := by rw [pascal]
        _ ≤ (a + 0)! := by apply factorial_pos
  | 0, b + 1 =>
      calc pascal 0 (b + 1) = 1 := by rw [pascal]
        _ ≤ (0 + (b + 1))! := by apply factorial_pos
  | a + 1, b + 1 =>
      have IH1 := pascal_le (a + 1) b -- inductive hypothesis
      have IH2 := pascal_le a (b + 1) -- inductive hypothesis
      calc pascal (a + 1) (b + 1) = pascal (a + 1) b + pascal a (b + 1) := by rw [pascal]
        _ ≤ (a + 1 + b) ! + (a + (b + 1)) ! := by rel [IH1, IH2]
        _ ≤ (a + b) * (a + b + 1) ! + (a + 1 + b) ! + (a + (b + 1)) !  := by extra
        _ = ((a + b + 1) + 1) * (a + b + 1)! := by ring
        _ = ((a + b + 1) + 1)! := by rw [factorial, factorial, factorial]
        _ = (a + 1 + (b + 1))! := by ring
termination_by _ a b => a + b


theorem pascal_eq (a b : ℕ) : pascal a b * a ! * b ! = (a + b)! := by
  match a, b with
  | a, 0 =>
    -- it appears _ is just a. Why?
    calc pascal _ 0 * a ! * 0! = 1 * a ! * 0! := by rw [pascal]
      _ = 1 * a ! * 1 := by rw [factorial]
      _ = (a + 0)! := by ring
  | 0, b + 1 =>
    calc pascal 0 (b + 1) * 0 ! * (b + 1)! = 1 * 0 ! * (b + 1)! := by rw [pascal]
      _ = 1 * 1 * (b + 1)! := by rw [factorial, factorial]
      _ = (0 + (b + 1))! := by ring
  | a + 1, b + 1 =>
    have IH1 := pascal_eq (a + 1) b -- inductive hypothesis
    have IH2 := pascal_eq a (b + 1) -- inductive hypothesis
    calc
      pascal (a + 1) (b + 1) * (a + 1)! * (b + 1)!
        = (pascal (a + 1) b + pascal a (b + 1)) * (a + 1)! * (b + 1)! := by rw [pascal]
      _ = pascal (a + 1) b * (a + 1)! * (b + 1)!
          + pascal a (b + 1) * (a + 1)! * (b + 1)! := by ring
      _ = pascal (a + 1) b * (a + 1)! * ((b + 1) * b !)
          + pascal a (b + 1) * ((a + 1) * a !) * (b + 1)! := by rw [factorial, factorial]
      _ = (b + 1) * (pascal (a + 1) b * (a + 1)! * b !)
          + (a + 1) * (pascal a (b + 1) * a ! * (b + 1)!) := by ring
      _ = (b + 1) * ((a + 1) + b) !
          + (a + 1) * (a + (b + 1)) ! := by rw [IH1, IH2]
      _ = ((1 + a + b) + 1) * (1 + a + b) ! := by ring
      _ = ((1 + a + b) + 1) ! := by rw [factorial]
      _ = ((a + 1) + (b + 1)) ! := by ring
termination_by _ a b => a + b


example (a b : ℕ) : (pascal a b : ℚ) = (a + b)! / (a ! * b !) := by
  have ha := factorial_pos a -- this is an integer theorem, and a ∈ Q
  have hb := factorial_pos b
  field_simp [ha, hb]
  norm_cast
  calc pascal a b * (a ! * b !) = pascal a b * a ! * b ! := by ring
    _ = (a + b)! := by apply pascal_eq

-- #eval (pascal 6 4 : ℚ) = (10 !) / (6 ! * 4 !) -- true

/-! # Exercises -/


theorem pascal_symm (m n : ℕ) : pascal m n = pascal n m := by
  match m, n with
  | 0, 0 =>
    rw [pascal];
  | a + 1, 0 =>
    rw [pascal, pascal]
  | 0, b + 1 =>
    rw [pascal, pascal]
  | a + 1, b + 1 =>
    -- pascal (a + 1) b + pascal a (b + 1)
    -- ihs not used :(. Does this qualify
    -- as an inductive proof?
    have ih1: _ := pascal_symm (a + 1) b
    have ih2: _ := pascal_symm a ( b + 1)
    have h1:=
      calc (pascal (a + 1) (b + 1)) * ((a + 1) !) * ((b + 1) !)
        _ = ((a + 1) + (b + 1)) ! := pascal_eq (a + 1) (b + 1)
        _ = ((b + 1) + (a + 1)) ! := by ring
        _ = (pascal (b + 1) (a + 1)) * ((b + 1) !) * ((a + 1) !) := by rw [pascal_eq]
        _ = (pascal (b + 1) (a + 1)) * ((a + 1) !) * ((b + 1) !) := by ring

    cancel ((b + 1) !) at h1
    cancel ((a + 1) !) at h1

termination_by _ a b => a + b

-- I don't get why we need this "match blah blah" at all.
-- Why not just this?
theorem pascal_symm' (m n : ℕ) : pascal m n = pascal n m := by
  have h1:=
      calc (pascal m n) * (m !) * (n !)
        _ = (m + n) ! := pascal_eq m n
        _ = (n + m) ! := by ring
        _ = (pascal n m) * (n !) * (m !) := by rw [pascal_eq]
        _ = (pascal n m) * (m !) * (n !) := by ring

  cancel (n !) at h1; cancel (m !) at h1

example (a : ℕ) : pascal a 1 = a + 1 := by
  simple_induction a with j hj
  · rw [pascal];
  · rw [pascal, pascal, ←hj]
    ring
