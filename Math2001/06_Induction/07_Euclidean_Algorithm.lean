/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

namespace Euclid
open Int


@[decreasing] theorem lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b := by
  have H : 0 ≤ fmod a b
  · apply fmod_nonneg_of_pos
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b) := by
  have H : 0 ≤ fmod a (-b)
  · apply fmod_nonneg_of_pos
    addarith [h1]
  have h2 : 0 < -b := by addarith [h1]
  calc b < 0 := h1
    _ ≤ fmod a (-b) := H

@[decreasing] theorem upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b := by
  apply fmod_lt_of_pos
  addarith [h1]

@[decreasing] theorem upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b := by
  apply fmod_lt_of_pos
  apply h1

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b

theorem gcd_nonneg (a b : ℤ) : 0 ≤ gcd a b := by
  rw [gcd]
  split_ifs with h1 h2 ha <;> push_neg at *
  · -- case `0 < b`
    have IH := gcd_nonneg b (fmod a b) -- inductive hypothesis
    apply IH
  · -- case `b < 0`
    have IH := gcd_nonneg b (fmod a (-b)) -- inductive hypothesis
    apply IH
  · -- case `b = 0`, `0 ≤ a`
    apply ha
  · -- case `b = 0`, `a < 0`
    addarith [ha]
termination_by _ a b => b

--#eval fmod 42 0
--#eval fmod 0 (-42) == 0
-- #eval fmod 42 0 -- 42


theorem gcd_zero_zero : gcd 0 0 = 0 := by rfl




theorem gcd_zero (a: ℤ) (aNonNeg: a > 0) : gcd 0 a = a  := by
  rw [gcd, if_pos aNonNeg]
  have h1: fmod 0 a = 0 := zero_fmod a
  --have h2: ¬ 0 < fmod 0 a := Eq.not_gt h1
  --have h3: ¬ fmod 0 a < 0 := Eq.not_gt (id h1.symm)
  rw [gcd, if_neg (Eq.not_gt (zero_fmod a)), if_neg (Eq.not_gt (zero_fmod a).symm)]
  have h4: 0 ≤ a := by exact Int.le_of_lt aNonNeg
  rw [if_pos h4]



theorem gcd_zero' (a: ℤ) (aNeg: a < 0) : gcd 0 a = -a  := by
  have h1: ¬ 0 < a := by exact lt_asymm aNeg
  rw [gcd, if_neg h1, if_pos aNeg]
  have h2: fmod 0 (-a) = 0 := by exact zero_fmod (-a)
  have h3: ¬fmod 0 (-a) < 0 := by exact Eq.not_gt (id h2.symm)
  have h4: ¬0 < fmod 0 (-a) := by exact Eq.not_gt h2
  have h5: ¬ 0 ≤ a := by exact Int.not_le.mpr aNeg
  rw [gcd, if_neg h3, if_neg h4, if_neg h5]


theorem gcd_symm (a b: ℤ) : gcd a b = gcd b a := by
  -- let lhs: ℤ := gcd a b
  -- set rhs: ℤ := gcd b a
  -- rw [gcd]
  obtain ha | ha := le_or_gt a 0
  ·  -- a ≤ 0
    obtain ha_lt0 | ha_eq0 := lt_or_eq_of_le ha
    · -- a < 0
      obtain hb_le0 | h3 := le_or_gt b 0
      · -- b ≤ 0
        obtain hb_lt0 | h4 := lt_or_eq_of_le hb_le0
        · -- b < 0
          have h42: ¬ 0 < b := by exact Int.not_lt.mpr hb_le0
          --
          rw [gcd, if_neg (not_lt.mpr hb_le0), if_pos hb_lt0] --, if_neg h42, if_pos hb_lt0]

          -- rw [gcd]
          -- fmod a -b

          sorry
        · -- b = 0
          sorry
      · -- b > 0
        sorry
    · -- a = 0
      obtain h5 | h5 := le_or_gt b 0
      · -- b ≤ 0
        obtain h6 | h6 := lt_or_eq_of_le h5
        · -- b < 0
          sorry
        · -- b = 0
          sorry
      · -- b > 0
        sorry

  · -- a > 0
    obtain h7 | h7 := le_or_gt b 0
    · -- b ≤ 0
      obtain h8 | h8 := lt_or_eq_of_le h7
      · -- b < 0
        sorry
      · -- b = 0
        sorry
    · -- b > 0
      sorry




theorem gcd_dvd (a b : ℤ) : gcd a b ∣ b ∧ gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 h3<;> push_neg at *
  · -- suppose 0 < b
    obtain ⟨IH_right, IH_left⟩ := gcd_dvd b (fmod a b) -- inductive hypothesis
    constructor
    · -- prove that `gcd b (fmod a b) ∣ b`
      apply IH_left
    · -- prove that `gcd b (fmod a b) ∣ a`
      obtain ⟨c, hc⟩ := IH_left   -- b = gcd b (fmod a b) * c
      obtain ⟨d, hd⟩ := IH_right  -- fmod a b = gcd b (fmod a b) * d
      use (fdiv a b) * c + d
      calc a
        _ = fmod a b + b * fdiv a b := by rw [fmod_add_fdiv a b]
        _ = gcd b (fmod a b) * d + b * fdiv a b := by rw [hd.symm]
        _ = gcd b (fmod a b) * d + gcd b (fmod a b) * c * fdiv a b := by rw [hc.symm]
        _ = gcd b (fmod a b) * (fdiv a b * c + d) := by ring
  · -- case `b < 0`
    constructor
    · -- prove that `gcd b (fmod a (-b)) ∣ b`
      obtain ⟨IH_right, IH_left⟩ := gcd_dvd b (fmod a (-b)) -- inductive hypothesis
      apply IH_left
    · -- prove that `gcd b (fmod a (-b)) ∣ a`
      obtain ⟨IH_right, IH_left⟩ := gcd_dvd b (fmod a (-b)) -- inductive hypothesis
      obtain ⟨c, hc⟩ := IH_left   -- b = gcd b (fmod a (-b)) * c
      obtain ⟨d, hd⟩ := IH_right  -- fmod a (-b) = gcd b (fmod a (-b)) * d
      use d - c * fdiv a (-b)
      calc a
        _ = fmod a (-b) + -b * fdiv a (-b) := by rw [fmod_add_fdiv a (-b)]
        _ = gcd b (fmod a (-b)) * d + -b * fdiv a (-b) := by rw [←hd]
        _ = gcd b (fmod a (-b)) * d + -(gcd b (fmod a (-b)) * c) * fdiv a (-b) := by rw [←hc]
        _ = gcd b (fmod a (-b)) * d - (gcd b (fmod a (-b)) * c) * fdiv a (-b) := by ring
        _ = gcd b (fmod a (-b)) * (d - c * fdiv a (-b)) := by ring
  · -- 0 ≤ a, 0 ≤ b and b ≤ 0
    -- since 0 ≤ b and b ≤ 0, b = 0
    constructor
    · -- prove that `a ∣ b`
      use 0; rw[Int.le_antisymm h1 h2]; ring
    · -- prove that `gcd a b ∣ a`
      use 1; ring
  · -- case `b = 0`, `a < 0`
    constructor
    · -- prove that `-a ∣ b`
      use 0; rw [Int.le_antisymm h1 h2]; ring
    · -- prove that `-a ∣ a`
      use -1; ring

termination_by gcd_dvd a b => b



mutual
theorem gcd_dvd_right (a b : ℤ) : gcd a b ∣ b := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    apply gcd_dvd_left b (fmod a b) -- inductive hypothesis
  · -- case `b < 0`
    apply gcd_dvd_left b (fmod a (-b)) -- inductive hypothesis
  · -- case `b = 0`, `0 ≤ a`
    have hb : b = 0 := le_antisymm h1 h2
    use 0
    calc b = 0 := hb
      _ = a * 0 := by ring
  · -- case `b = 0`, `a < 0`
    have hb : b = 0 := le_antisymm h1 h2
    use 0
    calc b = 0 := hb
      _ = -a * 0 := by ring

theorem gcd_dvd_left (a b : ℤ) : gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH1 := gcd_dvd_left b (fmod a b) -- inductive hypothesis
    have IH2 := gcd_dvd_right b (fmod a b) -- inductive hypothesis
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    use l + k * q
    calc a = r + b * q := by rw [H]
      _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l + k * q) := by ring
  · -- case `b < 0`
    have IH1 := gcd_dvd_left b (fmod a (-b)) -- inductive hypothesis
    have IH2 := gcd_dvd_right b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    use l - k * q
    calc a = r + (-b) * q := by rw [H]
      _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l - k * q) := by ring
  · -- case `b = 0`, `0 ≤ a`
    use 1
    ring
  · -- case `b = 0`, `a < 0`
    use -1
    ring

end
termination_by gcd_dvd_right a b => b ; gcd_dvd_left a b => b


theorem gcd_symm1 (a b: ℤ) : gcd a b = gcd b a := by
  --apply Nat.gcd_comm _ _
  apply Int.dvd_antisymm
  ·
    exact gcd_nonneg a b
  ·
    exact gcd_nonneg b a
  · -- gcd a b ∣ gcd b a
    --dsimp [. ∣ .]
    have h1: gcd a b ∣ a := by exact gcd_dvd_left a b
    have h2: gcd b a ∣ b := by exact gcd_dvd_left b a
    obtain ⟨c, hc⟩ := gcd_dvd_left a b
    obtain ⟨d, hd⟩ := gcd_dvd_right a b
    dsimp [. ∣ .]
    sorry
  ·

    sorry



mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b))
  else if 0 ≤ a then
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b


#eval L (-21) 15 -- infoview displays `2`
#eval R (-21) 15 -- infoview displays `3`


theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH := L_mul_add_R_mul b (fmod a b) -- inductive hypothesis
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b < 0`
    have IH := L_mul_add_R_mul b (fmod a (-b)) -- inductive hypothesis
    have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b = 0`, `0 ≤ a`
    ring
  · -- case `b = 0`, `a < 0`
    ring
termination_by L_mul_add_R_mul a b => b


#eval L 7 5 -- infoview displays `-2`
#eval R 7 5 -- infoview displays `3`
#eval gcd 7 5 -- infoview displays `1`


theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  use L a b, R a b
  apply L_mul_add_R_mul

/-! # Exercises -/


theorem gcd_maximal {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨t, u, htu⟩ := bezout a b
  use (t * x + u * y)
  calc gcd a b
    _ = t * a + u * b := by rw [htu]
    _ = t * (d * x) + u * (d * y) := by rw [hx, hy]
    _ = d * (t * x + u * y) := by ring
