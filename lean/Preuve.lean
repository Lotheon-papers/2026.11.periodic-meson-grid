import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Tests de proximité à une grille périodique
Formalisation jointe aux manuscrits français et anglais.
Voir README.md pour les versions, les références et la portée des énoncés.
-/
namespace AuditV10

noncomputable def cell (m u : ℝ) : ℤ := ⌊m/(2*u)+1/2⌋
noncomputable def quantize (m u : ℝ) : ℝ := 2*u*(cell m u : ℝ)
noncomputable def err (m u : ℝ) : ℝ := m - quantize m u

theorem half_step_bound (m u : ℝ) (hu : 0 < u) : |err m u| ≤ u := by
  let x : ℝ := m/(2*u)+1/2
  have hlo : (cell m u : ℝ) ≤ x := Int.floor_le x
  have hhi : x < (cell m u : ℝ)+1 := Int.lt_floor_add_one x
  have hm : (m/(2*u))*(2*u) = m := div_mul_cancel₀ m (by positivity)
  have hl := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2*u by positivity)
  have hh := mul_le_mul_of_nonneg_right hhi.le (show 0 ≤ 2*u by positivity)
  have hx : x*(2*u) = m+u := by
    dsimp [x]
    rw [add_mul, hm]
    ring
  rw [hx] at hl hh
  rw [abs_le]
  unfold err quantize
  constructor <;> nlinarith only [hl, hh]

theorem nearest (m u : ℝ) (hu : 0 < u) (k : ℤ) :
    |err m u| ≤ |m - 2*u*(k : ℝ)| := by
  have hb := half_step_bound m u hu
  have he := abs_le.mp hb
  rcases lt_trichotomy k (cell m u) with hk | hk | hk
  · have hn : (k:ℝ)+1 ≤ (cell m u:ℝ) := by
      exact_mod_cast (show k+1 ≤ cell m u by omega)
    have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*u by positivity)
    have hright : u ≤ m-2*u*(k:ℝ) := by
      unfold err quantize at he
      nlinarith only [he.1, hh]
    exact hb.trans (hright.trans (le_abs_self _))
  · subst k
    rfl
  · have hn : (cell m u:ℝ)+1 ≤ (k:ℝ) := by
      exact_mod_cast (show cell m u+1 ≤ k by omega)
    have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*u by positivity)
    have hleft : u ≤ -(m-2*u*(k:ℝ)) := by
      unfold err quantize at he
      nlinarith only [he.2, hh]
    exact hb.trans (hleft.trans (neg_le_abs _))

noncomputable def d (m : ℝ) : ℝ := |err m 35|

theorem distance_shift_bound (m t : ℝ) : d (m+t) ≤ d m + |t| := by
  let k := cell m 35
  have hn := nearest (m+t) 35 (by norm_num) k
  have hr : m+t-2*35*(k:ℝ) = (m-2*35*(k:ℝ))+t := by ring
  rw [hr] at hn
  exact hn.trans (abs_add_le (m-2*35*(k:ℝ)) t)

private theorem anchor_distance (m center : ℝ) (k : ℤ) (hc : center = 70*(k:ℝ))
    (hg : 0 ≤ center-m) (hh : center-m ≤ 35) : d m = center-m := by
  have hcell : cell m 35 = k := by
    unfold cell
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  unfold d err quantize
  rw [hcell]
  have he : m-2*35*(k:ℝ) = -(center-m) := by linarith
  rw [he, abs_neg, abs_of_nonneg hg]

private theorem anchor_change (m center t : ℝ) (k : ℤ) (hc : center = 70*(k:ℝ))
    (hg : 0 ≤ center-m) (hh : center-m ≤ 35) :
    d (m+t)-d m ≤ |t-(center-m)|-(center-m) := by
  have h := nearest (m+t) 35 (by norm_num) k
  have he : m+t-2*35*(k:ℝ) = t-(center-m) := by linarith
  rw [he] at h
  rw [anchor_distance m center k hc hg hh]
  exact sub_le_sub_right h _

private theorem two_anchor_increase (g h t : ℝ) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (ht : 0 ≤ t) (hupper : t ≤ 2*(g+h)) :
    |t-g|-g + (|t-h|-h) ≤ t := by
  rcases le_total t g with htg | hgt <;> rcases le_total t h with hth | hht
  · rw [abs_of_nonpos (sub_nonpos.mpr htg), abs_of_nonpos (sub_nonpos.mpr hth)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr htg), abs_of_nonneg (sub_nonneg.mpr hht)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hgt), abs_of_nonpos (sub_nonpos.mpr hth)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hgt), abs_of_nonneg (sub_nonneg.mpr hht)]
    linarith

theorem joint_phase_interval
    (a b c x e t : ℝ)
    (ha : 134.9763 ≤ a ∧ a ≤ 134.9773)
    (hb : 547.845 ≤ b ∧ b ≤ 547.879)
    (hc : 957.72 ≤ c ∧ c ≤ 957.84)
    (he : 1799 ≤ e ∧ e ≤ 1819)
    (ht : 0 ≤ t ∧ t ≤ 12.0454) :
    d (a+t)+d (b+t)+d (c+t)+d (x+t)+d (e+t) ≤
      d a+d b+d c+d x+d e := by
  have pa := anchor_change a 140 t 2 (by norm_num)
    (by linarith [ha.2]) (by linarith [ha.1])
  have pb := anchor_change b 560 t 8 (by norm_num)
    (by linarith [hb.2]) (by linarith [hb.1])
  have pc := anchor_change c 980 t 14 (by norm_num)
    (by linarith [hc.2]) (by linarith [hc.1])
  have pe := anchor_change e 1820 t 26 (by norm_num)
    (by linarith [he.2]) (by linarith [he.1])
  have px := distance_shift_bound x t
  rw [abs_of_nonneg ht.1] at px
  rw [abs_of_nonpos (by linarith [ht.2,hb.2])] at pb
  rw [abs_of_nonpos (by linarith [ht.2,hc.2])] at pc
  have hpair := two_anchor_increase (140-a) (1820-e) t
    (by linarith [ha.2]) (by linarith [he.2]) ht.1 (by linarith [ht.2,ha.2,he.2])
  linarith

theorem joint_observed_sums
    (a b c x e : ℝ)
    (ha : 134.9763 ≤ a ∧ a ≤ 134.9773)
    (hb : 547.845 ≤ b ∧ b ≤ 547.879)
    (hc : 957.72 ≤ c ∧ c ≤ 957.84)
    (he : 1799 ≤ e ∧ e ≤ 1819) :
    40.3037 ≤ d a+d b+d c+d x+d e ∧
      34.281 ≤ d b+d c+d x := by
  have da := anchor_distance a 140 2 (by norm_num)
    (by linarith [ha.2]) (by linarith [ha.1])
  have db := anchor_distance b 560 8 (by norm_num)
    (by linarith [hb.2]) (by linarith [hb.1])
  have dc := anchor_distance c 980 14 (by norm_num)
    (by linarith [hc.2]) (by linarith [hc.1])
  have de := anchor_distance e 1820 26 (by norm_num)
    (by linarith [he.2]) (by linarith [he.1])
  have dx : 0 ≤ d x := abs_nonneg _
  constructor <;> linarith [ha.2,hb.2,hc.2,he.2]

theorem common_full_periods (a e : ℝ)
    (ha : 134.9763 ≤ a ∧ a ≤ 134.9773) (he : 1799 ≤ e ∧ e ≤ 1819) :
    a ≤ 140 ∧ 1750 ≤ e ∧ e-a ≤ 1684.0237 := by
  exact ⟨by linarith [ha.2], by linarith [he.1], by linarith [ha.1,he.2]⟩

theorem probability_bound_arithmetic :
    (0.01347 : ℚ) < (46/1684.0237)^5*(40.3037^5-5*(40.3037-35)^5)/120 ∧
    (0.13684 : ℚ) < (46/1684.0237)^3*34.281^3/6 ∧
    (0.17207 : ℚ) < 12.0454/70 := by norm_num

private theorem cell_value (m u : ℝ) (k : ℤ)
    (lo : (k : ℝ) ≤ m/(2*u)+1/2) (hi : m/(2*u)+1/2 < (k : ℝ)+1) :
    cell m u = k :=
  Int.floor_eq_iff.mpr ⟨lo,hi⟩

private theorem err_value (m u : ℝ) (k : ℤ)
    (lo : (k : ℝ) ≤ m/(2*u)+1/2) (hi : m/(2*u)+1/2 < (k : ℝ)+1) :
    err m u = m-2*u*(k : ℝ) := by
  unfold err quantize
  rw [cell_value m u k lo hi]

#print axioms half_step_bound
#print axioms nearest
#print axioms distance_shift_bound
#print axioms joint_phase_interval
#print axioms joint_observed_sums
#print axioms common_full_periods
#print axioms probability_bound_arithmetic

/-- The grid distance over one turn, measured from an anchor g below 70k. -/
theorem one_turn_distance (m g t : ℝ) (k : ℤ) (hm : m = 70*(k:ℝ)-g)
    (hg : 0 ≤ g ∧ g ≤ 35) (ht : 0 ≤ t ∧ t ≤ 70) :
    d (m+t) = if t ≤ g then g-t else if t < g+35 then t-g else 70+g-t := by
  by_cases hlo : t ≤ g
  · rw [if_pos hlo]
    have hc := anchor_distance (m+t) (70*(k:ℝ)) k rfl
      (by linarith [ht.1]) (by linarith [hg.2, ht.1])
    rw [hc]
    linarith
  · rw [if_neg hlo]
    by_cases hhi : t < g+35
    · rw [if_pos hhi]
      have h := err_value (m+t) 35 k
        (by norm_num; linarith [hg.2, ht.1]) (by norm_num; linarith)
      unfold d
      rw [h, abs_of_nonneg (by linarith)]
      linarith
    · rw [if_neg hhi]
      have h := anchor_distance (m+t) (70*(k:ℝ)+70) (k+1) (by push_cast; ring)
        (by linarith [hg.1, ht.2]) (by linarith)
      rw [h]
      linarith

set_option maxHeartbeats 500000 in
/-- Exact acceptance arc for the mass quintuplet that attains the M3 bound. -/
theorem sharp_phase_arc (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 70) :
    d (134.9773+t)+d (547.879+t)+d (957.84+t)+d (1260+t)+d (1819+t) ≤ 40.3037
      ↔ t ≤ 12.0454 ∨ t = 70 := by
  rw [one_turn_distance 134.9773 5.0227 t 2 (by norm_num) (by norm_num) ht,
      one_turn_distance 547.879 12.121 t 8 (by norm_num) (by norm_num) ht,
      one_turn_distance 957.84 22.16 t 14 (by norm_num) (by norm_num) ht,
      one_turn_distance 1260 0 t 18 (by norm_num) (by norm_num) ht,
      one_turn_distance 1819 1 t 26 (by norm_num) (by norm_num) ht]
  by_cases h0 : t ≤ 0
  · rw [if_pos (show t ≤ 5.0227 by linarith),
        if_pos (show t ≤ 12.121 by linarith),
        if_pos (show t ≤ 22.16 by linarith),
        if_pos (show t ≤ 0 by linarith),
        if_pos (show t ≤ 1 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h1 : t ≤ 1
  · rw [if_pos (show t ≤ 5.0227 by linarith),
        if_pos (show t ≤ 12.121 by linarith),
        if_pos (show t ≤ 22.16 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_pos (show t < (0:ℝ)+35 by linarith),
        if_pos (show t ≤ 1 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h2 : t ≤ 5.0227
  · rw [if_pos (show t ≤ 5.0227 by linarith),
        if_pos (show t ≤ 12.121 by linarith),
        if_pos (show t ≤ 22.16 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_pos (show t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_pos (show t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h3 : t ≤ 12.121
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_pos (show t < (5.0227:ℝ)+35 by linarith),
        if_pos (show t ≤ 12.121 by linarith),
        if_pos (show t ≤ 22.16 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_pos (show t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_pos (show t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h4 : t ≤ 22.16
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_pos (show t < (5.0227:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 12.121 by linarith),
        if_pos (show t < (12.121:ℝ)+35 by linarith),
        if_pos (show t ≤ 22.16 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_pos (show t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_pos (show t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h5 : t < 35
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_pos (show t < (5.0227:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 12.121 by linarith),
        if_pos (show t < (12.121:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 22.16 by linarith),
        if_pos (show t < (22.16:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_pos (show t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_pos (show t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h6 : t < 36
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_pos (show t < (5.0227:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 12.121 by linarith),
        if_pos (show t < (12.121:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 22.16 by linarith),
        if_pos (show t < (22.16:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_neg (show ¬ t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_pos (show t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h7 : t < 40.0227
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_pos (show t < (5.0227:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 12.121 by linarith),
        if_pos (show t < (12.121:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 22.16 by linarith),
        if_pos (show t < (22.16:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_neg (show ¬ t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_neg (show ¬ t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h8 : t < 47.121
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_neg (show ¬ t < (5.0227:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 12.121 by linarith),
        if_pos (show t < (12.121:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 22.16 by linarith),
        if_pos (show t < (22.16:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_neg (show ¬ t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_neg (show ¬ t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  by_cases h9 : t < 57.16
  · rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
        if_neg (show ¬ t < (5.0227:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 12.121 by linarith),
        if_neg (show ¬ t < (12.121:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 22.16 by linarith),
        if_pos (show t < (22.16:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 0 by linarith),
        if_neg (show ¬ t < (0:ℝ)+35 by linarith),
        if_neg (show ¬ t ≤ 1 by linarith),
        if_neg (show ¬ t < (1:ℝ)+35 by linarith)]
    constructor
    · intro hs
      exact Or.inl (by linarith [ht.1, ht.2])
    · rintro (hs | he) <;> linarith [ht.1, ht.2]
  rw [if_neg (show ¬ t ≤ 5.0227 by linarith),
      if_neg (show ¬ t < (5.0227:ℝ)+35 by linarith),
      if_neg (show ¬ t ≤ 12.121 by linarith),
      if_neg (show ¬ t < (12.121:ℝ)+35 by linarith),
      if_neg (show ¬ t ≤ 22.16 by linarith),
      if_neg (show ¬ t < (22.16:ℝ)+35 by linarith),
      if_neg (show ¬ t ≤ 0 by linarith),
      if_neg (show ¬ t < (0:ℝ)+35 by linarith),
      if_neg (show ¬ t ≤ 1 by linarith),
      if_neg (show ¬ t < (1:ℝ)+35 by linarith)]
  constructor
  · intro hs
    exact Or.inr (by linarith [ht.1, ht.2])
  · rintro (hs | he) <;> linarith [ht.1, ht.2]

theorem sharp_phase_value_at_zero :
    d 134.9773+d 547.879+d 957.84+d 1260+d 1819 = 40.3037 := by
  have h := fun m g k hm hg => one_turn_distance m g 0 k hm hg (by norm_num)
  have h1 := h 134.9773 5.0227 2 (by norm_num) (by norm_num)
  have h2 := h 547.879 12.121 8 (by norm_num) (by norm_num)
  have h3 := h 957.84 22.16 14 (by norm_num) (by norm_num)
  have h4 := h 1260 0 18 (by norm_num) (by norm_num)
  have h5 := h 1819 1 26 (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4 h5 ⊢
  linarith

theorem strict_constants_for_derivative_bounds :
    (5 : ℚ)*49^4 < 47^5/2 ∧ 49^5*(70/1600) < 47^5/2 ∧
    49^3*35^3/6 < 1600*47^2*28^2/2 ∧ 49^2*35 < 1600*47^2 := by
  norm_num

private def pos (x : ℚ) : ℚ := max x 0

private def raw2Small (y a e : ℚ) : ℚ :=
  (48^2*y^2 - 96*(pos (y-a))^2 + 96*(pos (y-e))^2 + (pos (y-2*a))^2
    - 2*(pos (y-a-e))^2 + (pos (y-2*e))^2)/2

private def raw3Small (y a e : ℚ) : ℚ :=
  (48^3*y^3 - 3*48^2*(pos (y-a))^3 + 3*48^2*(pos (y-e))^3
    + 3*48*(pos (y-2*a))^3 - 6*48*(pos (y-a-e))^3 + 3*48*(pos (y-2*e))^3
    - (pos (y-3*a))^3 + 3*(pos (y-2*a-e))^3 - 3*(pos (y-a-2*e))^3
    + (pos (y-3*e))^3)/6

private def widthQ (a e : ℚ) : ℚ := 1680+a-e

private def m2H (e : ℚ) : ℚ :=
  raw3Small 34.281 5.0227 e - widthQ 5.0227 e * raw2Small (34.281-e) 5.0227 e

theorem m2_root_bracket_arithmetic :
    m2H 14.7028877559324 < 0 ∧ 0 < m2H 14.7028877559326 := by
  norm_num [m2H, raw3Small, raw2Small, widthQ, pos, max_def]

theorem m2_value_bracket_arithmetic :
    let e : ℚ := 14.7028877559325
    let p := raw3Small 34.281 5.0227 e / (widthQ 5.0227 e)^3
    let error := (3/1600 : ℚ)*10^(-13 : ℤ)
    (0.15504888347310 : ℚ) < p-error ∧ p+error < 0.15504888347311 := by
  norm_num [raw3Small, widthQ, pos, max_def]

#print axioms m2_root_bracket_arithmetic
#print axioms m2_value_bracket_arithmetic
#print axioms one_turn_distance
#print axioms sharp_phase_arc
#print axioms sharp_phase_value_at_zero
#print axioms strict_constants_for_derivative_bounds

end AuditV10

namespace ControleV11

def knots : List (ℤ × ℤ) :=
  [(0,48), (5022700000,-1), (1000000000,1), (35000000000,-48)]

def volumeNumerator (degree : ℕ) : ℕ → ℤ → ℤ
  | 0, y => max y 0 ^ degree
  | n+1, y =>
    (knots.map fun (k, w) => w * volumeNumerator degree n (y-k)).sum

def denom5 : ℤ := 120 * 1684022700000^5
def denom3 : ℤ := 6 * 1684022700000^3

set_option maxHeartbeats 600000 in
theorem exact_m1_witness :
    volumeNumerator 5 5 40303700000 * 6771887131105517591313698384755949535 =
    117271815670703024016458494058250829 * denom5 := by decide

set_option maxHeartbeats 600000 in
theorem m1_threshold_bracket :
    20 * volumeNumerator 5 5 50001088928 < denom5 ∧
    denom5 < 20 * volumeNumerator 5 5 50001088930 := by decide

set_option maxHeartbeats 600000 in
theorem conditional_size_arithmetic :
    3245930589 * denom3 < 10000000000 * volumeNumerator 3 3 (50001088928 - 6022700000) ∧
    10000000000 * volumeNumerator 3 3 (50001088930 - 6022700000) < 3245930591 * denom3 := by decide

#print axioms exact_m1_witness
#print axioms m1_threshold_bracket
#print axioms conditional_size_arithmetic

end ControleV11

namespace Calibration

/-- Algebra for the simplex part of the distribution, with n = k + 2. -/
theorem small_tail_inflation (k : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    let alpha := q^(k+2)/((k+2).factorial : ℝ)
    let beta := q^k/(k.factorial : ℝ)
    beta/alpha = ((k:ℝ)+2)*((k:ℝ)+1)/q^2 ∧ alpha < beta := by
  dsimp
  have hfactorial : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hnext : (0 : ℝ) < (k:ℝ)+1 := by positivity
  have hnext2 : (0 : ℝ) < (k:ℝ)+2 := by positivity
  have hpow : 0 < q^k := pow_pos hq _
  have hq2 : 0 < q^2 := pow_pos hq _
  have hfac : ((k+2).factorial : ℝ) =
      ((k:ℝ)+2)*((k:ℝ)+1)*(k.factorial : ℝ) := by
    simp only [show k+2 = (k+1)+1 by omega, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  rw [hfac, pow_add]
  constructor
  · field_simp [ne_of_gt hfactorial, ne_of_gt hnext, ne_of_gt hnext2,
      ne_of_gt hpow, ne_of_gt hq2]
    ring
  · apply (div_lt_div_iff₀ (by positivity) hfactorial).2
    have hqle : q^2 ≤ 1 := by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hq1)]
    have hnk : 0 ≤ (k:ℝ) := by positivity
    have hnorm : q^2 < ((k:ℝ)+2)*((k:ℝ)+1) := by nlinarith [sq_nonneg (k:ℝ)]
    calc
      q^k*q^2*(k.factorial : ℝ) = (q^k*(k.factorial : ℝ))*q^2 := by ring
      _ < (q^k*(k.factorial : ℝ))*(((k:ℝ)+2)*((k:ℝ)+1)) :=
        mul_lt_mul_of_pos_left hnorm (mul_pos hpow hfactorial)
      _ = q^k*(((k:ℝ)+2)*((k:ℝ)+1)*(k.factorial : ℝ)) := by ring

theorem n5_example :
    (1:ℚ)/((Nat.factorial 3 : ℕ) : ℚ) = 1/6 ∧ ((1:ℚ)/((Nat.factorial 3 : ℕ) : ℚ))/((1:ℚ)/((Nat.factorial 5 : ℕ) : ℚ)) = 20 := by
  norm_num [Nat.factorial_succ]

#print axioms small_tail_inflation
#print axioms n5_example

end Calibration

namespace PhaseMeasure

open Set MeasureTheory
open AuditV10 (d)

noncomputable def score (a b c x e t : ℝ) : ℝ :=
  d (a+t) + d (b+t) + d (c+t) + d (x+t) + d (e+t)

/-- The uniform phase probability, parametrized by the negative translation. -/
noncomputable def probability (a b c x e : ℝ) : ℝ :=
  (volume {t : ℝ | t ∈ Icc 0 70 ∧ score a b c x e t ≤ score a b c x e 0}).toReal / 70

theorem lower_bound (a b c x e : ℝ)
    (ha : 134.9763 ≤ a ∧ a ≤ 134.9773)
    (hb : 547.845 ≤ b ∧ b ≤ 547.879)
    (hc : 957.72 ≤ c ∧ c ≤ 957.84)
    (he : 1799 ≤ e ∧ e ≤ 1819) :
    60227 / 350000 ≤ probability a b c x e := by
  let arc : Set ℝ := {t | t ∈ Icc 0 70 ∧ score a b c x e t ≤ score a b c x e 0}
  have hsub : Icc (0 : ℝ) 12.0454 ⊆ arc := by
    intro t ht
    refine ⟨⟨ht.1, by linarith [ht.2]⟩, ?_⟩
    simpa [score] using AuditV10.joint_phase_interval a b c x e t ha hb hc he ht
  have hfinite : volume arc ≠ ⊤ := by
    have hle : volume arc ≤ volume (Icc (0 : ℝ) 70) :=
      measure_mono (fun _ ht => ht.1)
    rw [Real.volume_Icc] at hle
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hmeasure := ENNReal.toReal_mono hfinite (measure_mono hsub)
  rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (by norm_num)] at hmeasure
  change 60227 / 350000 ≤ (volume arc).toReal / 70
  linarith

theorem exact_witness : probability 134.9773 547.879 957.84 1260 1819 =
    60227 / 350000 := by
  have hs : score 134.9773 547.879 957.84 1260 1819 0 = 40.3037 := by
    simpa [score] using AuditV10.sharp_phase_value_at_zero
  have heq : {t : ℝ | t ∈ Icc 0 70 ∧
        score 134.9773 547.879 957.84 1260 1819 t ≤
          score 134.9773 547.879 957.84 1260 1819 0} =
      Icc 0 12.0454 ∪ {70} := by
    ext t
    change (t ∈ Icc 0 70 ∧
        score 134.9773 547.879 957.84 1260 1819 t ≤
          score 134.9773 547.879 957.84 1260 1819 0) ↔
      t ∈ Icc 0 12.0454 ∪ {70}
    rw [hs]
    constructor
    · rintro ⟨ht, h⟩
      rcases (AuditV10.sharp_phase_arc t ht).mp h with hlow | hend
      · exact Or.inl ⟨ht.1, hlow⟩
      · exact Or.inr hend
    · rintro (ht | ht)
      · have hturn : t ∈ Icc (0 : ℝ) 70 := ⟨ht.1, by linarith [ht.2]⟩
        exact ⟨hturn, (AuditV10.sharp_phase_arc t hturn).mpr (Or.inl ht.2)⟩
      · have hend : t = 70 := ht
        have hturn : t ∈ Icc (0 : ℝ) 70 := by rw [hend]; exact ⟨by norm_num, le_rfl⟩
        exact ⟨hturn, (AuditV10.sharp_phase_arc t hturn).mpr (Or.inr hend)⟩
  unfold probability
  have hvol : volume (Icc (0 : ℝ) 12.0454 ∪ {70}) = volume (Icc (0 : ℝ) 12.0454) := by
    apply le_antisymm
    · calc
        _ ≤ volume (Icc (0 : ℝ) 12.0454) + volume ({70} : Set ℝ) := measure_union_le _ _
        _ = _ := by rw [Real.volume_singleton, add_zero]
    · exact measure_mono (fun _ ht => Or.inl ht)
  rw [heq, hvol, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by norm_num)]
  norm_num

#print axioms lower_bound
#print axioms exact_witness

end PhaseMeasure

namespace Optimisation

open Set

/-- Rectangle argument for M1, with the derivative hypotheses established
    analytically from the volume bounds in the paper. -/
theorem rectangle_minimum {P : ℝ → ℝ → ℝ} {a₀ a₁ e₀ e₁ a e : ℝ}
    (ha : a ∈ Icc a₀ a₁) (he : e ∈ Icc e₀ e₁)
    (hA : ContinuousOn (fun x => P x e) (Icc a₀ a₁))
    (hA' : ∀ x ∈ Ioo a₀ a₁, 0 < deriv (fun y => P y e) x)
    (hE : ContinuousOn (P a₀) (Icc e₀ e₁))
    (hE' : ∀ x ∈ Ioo e₀ e₁, 0 < deriv (P a₀) x) :
    P a₀ e₀ ≤ P a e := by
  have hmonoA := strictMonoOn_of_deriv_pos (convex_Icc a₀ a₁) hA
    (by simpa only [interior_Icc] using hA')
  have hmonoE := strictMonoOn_of_deriv_pos (convex_Icc e₀ e₁) hE
    (by simpa only [interior_Icc] using hE')
  have ha₀ : a₀ ∈ Icc a₀ a₁ := ⟨le_rfl, ha.1.trans ha.2⟩
  have he₀ : e₀ ∈ Icc e₀ e₁ := ⟨le_rfl, he.1.trans he.2⟩
  exact (hmonoE.monotoneOn he₀ he he.1).trans (hmonoA.monotoneOn ha₀ ha ha.1)

/-- Root bracket for M2 once the analytic formula establishes continuity
    and strict monotonicity of the derivative numerator. -/
theorem unique_bracketed_root {H : ℝ → ℝ} {e₀ e₁ l u : ℝ}
    (hl : e₀ ≤ l) (hlu : l ≤ u) (hu : u ≤ e₁)
    (hcont : ContinuousOn H (Icc e₀ e₁))
    (hmono : StrictMonoOn H (Icc e₀ e₁))
    (hs₁ : H l < 0) (hs₂ : 0 < H u) :
    ∃! r, r ∈ Icc e₀ e₁ ∧ H r = 0 := by
  have hsub : Icc l u ⊆ Icc e₀ e₁ := Icc_subset_Icc hl hu
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Icc hlu (hcont.mono hsub) ⟨hs₁.le, hs₂.le⟩
  refine ⟨r, ⟨hsub hr, hzero⟩, ?_⟩
  intro y hy
  exact hmono.injOn hy.1 (hsub hr) (hy.2.trans hzero.symm)

/-- A continuous objective with derivative of the sign of H attains its
    global minimum at the unique root of strictly increasing H. -/
theorem minimum_at_root {P H : ℝ → ℝ} {e₀ e₁ r e : ℝ}
    (hr : r ∈ Icc e₀ e₁) (he : e ∈ Icc e₀ e₁) (hzero : H r = 0)
    (hP : ContinuousOn P (Icc e₀ e₁))
    (hH : StrictMonoOn H (Icc e₀ e₁))
    (hneg : ∀ x ∈ Ioo e₀ e₁, H x < 0 → deriv P x < 0)
    (hpos : ∀ x ∈ Ioo e₀ e₁, 0 < H x → 0 < deriv P x) :
    P r ≤ P e := by
  rcases le_total e r with her | hre
  · have hsubset : Icc e₀ r ⊆ Icc e₀ e₁ := Icc_subset_Icc le_rfl hr.2
    have hanti := strictAntiOn_of_deriv_neg (convex_Icc e₀ r) (hP.mono hsubset) (by
      rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Ioo e₀ e₁ := ⟨hx.1, hx.2.trans_le hr.2⟩
      apply hneg x hx'
      rw [← hzero]
      exact hH ⟨hx'.1.le, hx'.2.le⟩ hr hx.2)
    exact hanti.antitoneOn ⟨he.1, her⟩ ⟨hr.1, le_rfl⟩ her
  · have hsubset : Icc r e₁ ⊆ Icc e₀ e₁ := Icc_subset_Icc hr.1 le_rfl
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc r e₁) (hP.mono hsubset) (by
      rw [interior_Icc]
      intro x hx
      have hx' : x ∈ Ioo e₀ e₁ := ⟨hr.1.trans_lt hx.1, hx.2⟩
      apply hpos x hx'
      rw [← hzero]
      exact hH hr ⟨hx'.1.le, hx'.2.le⟩ hx.1)
    exact hmono.monotoneOn ⟨le_rfl, hr.2⟩ ⟨hre, he.2⟩ hre

#print axioms rectangle_minimum
#print axioms unique_bracketed_root
#print axioms minimum_at_root

end Optimisation

namespace SimplexVolume

open Set MeasureTheory
open scoped BigOperators ENNReal

def simplex (n : ℕ) (q : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ q}

theorem simplex_measurable (n : ℕ) (q : ℝ) : MeasurableSet (simplex n q) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩
    {x | ∑ i, x i ≤ q})
  apply MeasurableSet.inter
  · have h : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i} := by
      ext x
      simp
    rw [h]
    exact MeasurableSet.iInter (fun i : Fin n =>
      measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
      measurable_const

theorem simplex_empty {n : ℕ} {q : ℝ} (hq : q < 0) : simplex n q = ∅ := by
  ext x
  constructor
  · intro hx
    have hn : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx.1 i)
    exact False.elim ((not_le_of_gt hq) (hn.trans hx.2))
  · intro hx
    exact False.elim hx

theorem volume_simplex (n : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    volume (simplex n q) = ENNReal.ofReal (q^n / (n.factorial : ℝ)) := by
  induction n generalizing q with
  | zero =>
    have hs : simplex 0 q = Icc (0 : Fin 0 → ℝ) 0 := by
      ext x
      have hx : x = 0 := funext (fun i => Fin.elim0 i)
      subst x
      simp [simplex, hq]
    rw [hs, Real.volume_Icc_pi]
    simp
  | succ n ih =>
    let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
    have hpre := hp.measure_preimage (simplex_measurable (n+1) q).nullMeasurableSet
    rw [← hpre, Measure.volume_eq_prod, Measure.prod_apply ((simplex_measurable (n+1) q).preimage
      split.symm.measurable)]
    have hslice (t : ℝ) :
        Prod.mk t ⁻¹' (split.symm ⁻¹' simplex (n+1) q) =
          if 0 ≤ t then simplex n (q-t) else ∅ := by
      ext x
      have hf : split.symm (t, x) = Fin.cons t x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [split, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        · simp [split, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      change (split.symm (t, x) ∈ simplex (n+1) q) ↔ _
      rw [hf]
      by_cases ht : 0 ≤ t
      · simp only [ht, if_true, simplex, mem_setOf_eq, Fin.forall_fin_succ,
          Fin.cons_zero, Fin.cons_succ, true_and, Fin.sum_univ_succ]
        exact and_congr_right (fun _ => by constructor <;> intro h <;> linarith)
      · simp [ht, simplex, Fin.forall_fin_succ, Fin.sum_univ_succ]
    let f : ℝ → ℝ := fun t => (q-t)^n / (n.factorial : ℝ)
    have heq (t : ℝ) :
        volume (Prod.mk t ⁻¹' (split.symm ⁻¹' simplex (n+1) q)) =
          (Icc (0 : ℝ) q).indicator (fun u => ENNReal.ofReal (f u)) t := by
      rw [hslice]
      by_cases h0 : 0 ≤ t
      · rw [if_pos h0]
        by_cases hq' : t ≤ q
        · have hm : t ∈ Icc (0 : ℝ) q := ⟨h0, hq'⟩
          rw [ih _ (sub_nonneg.mpr hq'), indicator_of_mem hm]
        · rw [simplex_empty (sub_neg.mpr (lt_of_not_ge hq')), measure_empty,
            indicator_of_not_mem (show t ∉ Icc (0 : ℝ) q from fun h => hq' h.2)]
      · rw [if_neg h0, measure_empty, indicator_of_not_mem (show t ∉ Icc (0 : ℝ) q from fun h => h0 h.1)]
    simp_rw [heq]
    rw [lintegral_indicator measurableSet_Icc]
    have hfcont : Continuous f := by
      unfold f
      fun_prop
    have hfi : Integrable f (volume.restrict (Icc (0 : ℝ) q)) :=
      hfcont.continuousOn.integrableOn_compact isCompact_Icc
    have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) q)] f := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg,
        ← restrict_Ioc_eq_restrict_Icc, ← intervalIntegral.integral_of_le hq]
    congr 1
    unfold f
    rw [intervalIntegral.integral_div,
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n) q, sub_self, sub_zero,
        integral_pow]
    simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm, div_div]

/-- Lower-tail volume in the unit cube, which has volume one. -/
theorem unit_cube_lower_tail (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (h₁ : q ≤ 1) :
    volume {x : Fin n → ℝ | (∀ i, x i ∈ Icc 0 1) ∧ ∑ i, x i ≤ q} =
      ENNReal.ofReal (q^n / (n.factorial : ℝ)) := by
  rw [← volume_simplex n q hq]
  congr 1
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ q) ↔
    ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ q)
  refine ⟨fun h => ⟨fun i => (h.1 i).1, h.2⟩, ?_⟩
  intro h
  refine ⟨fun i => ⟨h.1 i, ?_⟩, h.2⟩
  have hterm : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ i)
  exact hterm.trans (h.2.trans h₁)

#print axioms volume_simplex
#print axioms unit_cube_lower_tail

end SimplexVolume

namespace OnePeriod

open Set MeasureTheory

/-- Rescale the grid error from one period to the unit interval. -/
theorem folded_error (P s : ℝ) (hP : 0 < P) (hs : s ∈ Icc (0 : ℝ) 1) :
    2 * |AuditV10.err (P*s) (P/2)| / P = min (2*s) (2*(1-s)) := by
  have h2 : 2*(P/2) = P := by ring
  have harg : (P*s)/(2*(P/2)) + 1/2 = s+1/2 := by
    rw [h2]
    field_simp
  by_cases hhalf : s < 1/2
  · have hcell : AuditV10.cell (P*s) (P/2) = 0 := by
      unfold AuditV10.cell
      rw [harg]
      apply Int.floor_eq_iff.mpr
      exact ⟨by norm_num; linarith [hs.1], by norm_num; linarith⟩
    have habs : 0 ≤ P*s := mul_nonneg hP.le hs.1
    unfold AuditV10.err AuditV10.quantize
    rw [hcell, h2]
    simp only [Int.cast_zero, mul_zero, sub_zero, abs_of_nonneg habs]
    rw [min_eq_left (by linarith)]
    field_simp
    ring
  · have hcell : AuditV10.cell (P*s) (P/2) = 1 := by
      unfold AuditV10.cell
      rw [harg]
      apply Int.floor_eq_iff.mpr
      exact ⟨by norm_num; linarith, by norm_num; linarith [hs.2]⟩
    have hneg : P*s-P ≤ 0 := by
      linarith [mul_le_mul_of_nonneg_left hs.2 hP.le]
    unfold AuditV10.err AuditV10.quantize
    rw [hcell, h2]
    simp only [Int.cast_one, mul_one, abs_of_nonpos hneg]
    rw [min_eq_right (by linarith)]
    field_simp
    ring

/-- The reduced distance on a single uniform period is uniform on [0,1]. -/
theorem folded_volume (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    volume {s : ℝ | s ∈ Icc 0 1 ∧ min (2*s) (2*(1-s)) ≤ q} =
      ENNReal.ofReal q := by
  by_cases h₁ : q = 1
  · subst q
    have heq : {s : ℝ | s ∈ Icc 0 1 ∧ min (2*s) (2*(1-s)) ≤ 1} = Icc 0 1 := by
      ext s
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        rcases le_total s (1/2) with hl | hr
        · exact (min_le_left _ _).trans (by linarith)
        · exact (min_le_right _ _).trans (by linarith)
    rw [heq, Real.volume_Icc, sub_zero]
  · have hq₁ : q < 1 := lt_of_le_of_ne hq.2 h₁
    have heq : {s : ℝ | s ∈ Icc 0 1 ∧ min (2*s) (2*(1-s)) ≤ q} =
        Icc 0 (q/2) ∪ Icc (1-q/2) 1 := by
      ext s
      change ((0 ≤ s ∧ s ≤ 1) ∧ min (2*s) (2*(1-s)) ≤ q) ↔
        (0 ≤ s ∧ s ≤ q/2) ∨ (1-q/2 ≤ s ∧ s ≤ 1)
      rw [min_le_iff]
      constructor
      · rintro ⟨⟨h0, h1⟩, h | h⟩
        · exact Or.inl ⟨h0, by linarith⟩
        · exact Or.inr ⟨by linarith, h1⟩
      · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
        · exact ⟨⟨h0, by linarith⟩, Or.inl (by linarith)⟩
        · exact ⟨⟨by linarith, h1⟩, Or.inr (by linarith)⟩
    have hdis : Disjoint (Icc (0 : ℝ) (q/2)) (Icc (1-q/2) 1) := by
      rw [Set.disjoint_left]
      intro x hx hy
      linarith [hx.2, hy.1]
    rw [heq, measure_union hdis measurableSet_Icc, Real.volume_Icc, Real.volume_Icc, sub_zero]
    rw [← ENNReal.ofReal_add (by linarith [hq.1]) (by linarith [hq.1])]
    congr 1
    ring

#print axioms folded_error
#print axioms folded_volume

end OnePeriod

namespace SimplexVolume

open Set MeasureTheory

/-- Ratio of the two exact unit-cube lower-tail probabilities at a common
threshold q in the simplex regime, with k = n - 2. -/
theorem cube_tail_ratio (k : ℕ) (q : ℝ) (hq : 0 < q) (h₁ : q ≤ 1) :
    let alpha := (volume {x : Fin (k+2) → ℝ |
      (∀ i, x i ∈ Icc 0 1) ∧ ∑ i, x i ≤ q}).toReal
    let beta := (volume {x : Fin k → ℝ |
      (∀ i, x i ∈ Icc 0 1) ∧ ∑ i, x i ≤ q}).toReal
    beta/alpha = ((k:ℝ)+2)*((k:ℝ)+1)/q^2 ∧ alpha < beta := by
  dsimp
  rw [unit_cube_lower_tail (k+2) q hq.le h₁, unit_cube_lower_tail k q hq.le h₁,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  exact Calibration.small_tail_inflation k q hq h₁

#print axioms cube_tail_ratio

end SimplexVolume
