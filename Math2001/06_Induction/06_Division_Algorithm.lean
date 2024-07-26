/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs
-- added for next to last so I don't need to reinvent
-- the wheel
import Library.Theory.ModEq.Lemmas
math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`



theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    -- ih: fmod (n + d) d + d * fdiv (n + d) d = n + d
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    -- 0 ≤ fmod (n + d) d
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/

theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by

  rw [fmod]
  split_ifs with h1 h2 h3<;> push_neg at *
  · -- suppose n ⬝ d < 0
    have ih := lt_fmod_of_neg (n + d) hd
    apply ih
  · -- suppose 0 ≤ d ⬝ (n - d)
    have ih := lt_fmod_of_neg (n - d) hd
    apply ih
  · -- suppose n = d
    apply hd
  · -- Suppose n ≠ d.
    -- Then we can equivalently prove d ≤ n
    apply lt_of_le_of_ne
    have h4: 0 ≤ - d * (n - d) := by addarith [h2]
    -- Since -d > 0 we can cancel it from the
    -- preceding inequality. Thus 0 ≤ n - d
    apply Int.neg_pos_of_neg at hd
    cancel (-d) at h4
    have h8: d ≤ n := by addarith [h4]
    ·
      apply h8
    ·
      apply Ne.symm h3

termination_by _ n d hd => 2 * n - d



def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1



theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 /-h3-/<;> push_neg
  · -- Suppose 0 < n
    have ih₁: T (1 - n) = (1 - n) ^ 2 := T_eq (1 - n)
    calc T (1 - n) + 2 * n - 1
      _ = (1 - n) ^ 2 + 2 * n - 1 := by rw [ih₁]
      _ = 1 - 2 * n + n ^ 2 + 2 * n - 1 := by ring
      _ = n ^ 2 := by ring
  · -- goal: T (-n) = n ^ 2
    have ih₂: T (-n) = (-n) ^ 2 := T_eq (-n)
    calc  T (-n)
      _ = (-n) ^ 2 := by rw [ih₂]
      _ = n ^ 2 := by ring
  · -- Suppose 0 is not less than n and 0 is not less than (-n).
    -- This can only be true when n = 0
    have h3: n ≤ 0 := Int.not_lt.mp h1
    have h4: - n ≤ 0 := Int.not_lt.mp h2
    have h5: n ≥ 0 := Int.nonneg_of_neg_nonpos h4
    rw [le_antisymm h3 h5]; numbers

  termination_by _ n => 3 * n - 1





theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
  (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
  (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨hr1, hr2, hr3⟩ := hr
  obtain ⟨hs1, hs2, hs3⟩ := hs
  -- Since zmod is symmetric and transitive, we have r ≡ₛ b
  -- This might be cheating (I had to import ModEq.Lemmas
  -- for this to work)
  have h4: r ≡ a [ZMOD b] := Int.ModEq.symm hr3
  have h5: r ≡ s [ZMOD b] := Int.ModEq.trans h4 hs3
  -- Since r ≡ₛ b there is c ∈ ℤ with r - s = b ⬝ c
  obtain ⟨c, hc⟩ := h5
  -- From which it follows that -b < r - s < b
  have h6:=
    calc -b
        _ < -s := Int.neg_lt_neg hs2
        _ ≤ -s + r := by addarith[hr1]
        _ = r - s := by ring

  have h7:=
    calc r - s
      _ ≤ r := by addarith [hs1]
      _ < b := hr2
  -- Then since r - s = bc: -b < b ⬝ c < b
  rw [hc] at h6; rw [hc] at h7
  -- Since bc < b, c < 1
  have h8: c < 1 := (mul_lt_iff_lt_one_right h).mp h7
  have h9: -b = (-1) * b := by ring
  rw [h9, Int.mul_comm]  at h6
  cancel b at h6
  -- Similarly since -b < bc, -1 < c
  -- Since -1 < c < 1, c = 0
  obtain h10 | h10 := eq_or_ne c 0
  ·
  -- Since c = 0, bc = 0 = r - s, so r = s
    have h11: b * 0 = 0 := by ring
    rw [h10, h11] at hc
    calc r
      _ = (r - s) + s := by ring
      _ = 0 + s := by rw [hc]
      _ = s := by ring
  · -- we can exclude cases where c ≠ 0
    -- which lead to contradictions
    obtain h12 | h12 := Ne.lt_or_lt h10
    ·
      have h13: ¬ c < 0 := Int.not_lt.mpr h6
      contradiction
    ·
      have h14: ¬ c < 1 := Int.not_lt.mpr h12
      contradiction


example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by

  use (fmod a b)
  constructor
  ·
    constructor
    · -- 0 ≤ fmod a b
      apply fmod_nonneg_of_pos a h
    ·
      constructor
      · -- fmod a b < b
        apply fmod_lt_of_pos a h
      · -- a ≡ fmod a b [ZMOD b]
        use fdiv a b
        calc a - fmod a b
          _ = (fmod a b + b * fdiv a b) - fmod a b := by rw [fmod_add_fdiv a b]
          _ = b * fdiv a b := by ring
  · -- Let y ∈ Z be arbitrary, and assume 0 ≤ y < b and a ≡ y [ZMOD b]
    -- we need to prove y = a % b, which is y = fmod a b
    intro y hy
    obtain ⟨hy1, hy2, ⟨c, hc⟩⟩ := hy

    apply uniqueness a b
    · apply h -- b > 0
    · constructor
      · apply hy1 -- y ≥ 0
      · constructor
        · apply hy2 -- y < b
        · -- Since b ∣ a - y, we have a ≡ y [ZMOD b]
          use c; apply hc
    · constructor
      · -- Since b > 0, a % b ≥ 0
        calc 0
          _ ≤ fmod a b := fmod_nonneg_of_pos a h
      ·
        constructor
        · -- Since b > 0, a % b < b
          calc fmod a b
            _ < b := fmod_lt_of_pos a h
        · -- Since a % b + b * a / b = a, we can use a / b
          -- as witness
          use fdiv a b
          calc a - fmod a b
            _ = fmod a b + b * fdiv a b - fmod a b := by rw [fmod_add_fdiv a b]
            _ = b * fdiv a b := by ring
