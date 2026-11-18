import FourierTensor.Tensor.CenterCache.Rate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Compare the saving at the cached exponent with the exact published value
`OAI.PowerSaving.theta`. All decimal endpoints denote rational numbers. -/
namespace FourierTensor.ExponentComparison

open OAI.PowerSaving
open scoped BigOperators
noncomputable section

private theorem log_million :
    13.81551054 < Real.log paperM ∧ Real.log paperM < 13.81551058 := by
  have lo := Real.sum_range_le_log_div (x := (1/9:ℝ)) (by norm_num) (by norm_num) 5
  have hi := Real.log_div_le_sum_range_add (x := (1/9:ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at lo hi
  have mul_eq : paperM = ((2:ℝ)^3 * (5/4))^6 := by norm_num [paperM]
  rw [mul_eq,Real.log_pow,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

/-- The saving ratio is between 142420.49 and 142420.50. The denominator uses
the bundled definition of the published exponent before decimal rounding. -/
theorem saving_ratio :
    142420.49 < (1-CenterCacheRate.exponent)/(1-theta) ∧
    (1-CenterCacheRate.exponent)/(1-theta) < 142420.50 := by
  let q : ℝ := paperDelta/(paperM*paperW)
  have hq : 0<q := by norm_num [q,paperM,paperDelta,paperW]
  have hsub : 0<1-q := by norm_num [q,paperM,paperDelta,paperW]
  have hlog := log_million
  have hM : 0<Real.log paperM := by linarith [hlog.1]
  have he : paperMultiplier=paperM*(1-q) := by
    norm_num [q,paperM,paperDelta,paperW,paperMultiplier]
  have hd : 1-theta = -Real.log (1-q) / Real.log paperM := by
    rw [theta,he,Real.log_mul (by norm_num [paperM]) hsub.ne']
    field_simp
    ring
  have hLo : q ≤ -Real.log (1-q) := by
    linarith [Real.log_le_sub_one_of_pos hsub]
  have hHi : -Real.log (1-q) ≤ q/(1-q) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hsub)
    rw [Real.log_inv] at h
    calc
      _ ≤ (1-q)⁻¹-1 := h
      _ = q/(1-q) := by field_simp; ring
  have hpos : 0 < -Real.log (1-q) := lt_of_lt_of_le hq hLo
  have hs : 1-CenterCacheRate.exponent = 3/100000000 := by
    norm_num [CenterCacheRate.exponent,CenterCacheRate.epsilon]
  rw [hd,hs,div_div_eq_mul_div]
  constructor
  · apply (lt_div_iff₀ hpos).2
    calc
      _ ≤ 142420.49*(q/(1-q)) := by gcongr
      _ < (3/100000000:ℝ)*13.81551054 := by norm_num [q,paperM,paperDelta,paperW]
      _ < _ := by linarith [hlog.1]
  · apply (div_lt_iff₀ hpos).2
    calc
      _ < (3/100000000:ℝ)*13.81551058 := by linarith [hlog.2]
      _ < 142420.50*q := by norm_num [q,paperM,paperDelta,paperW]
      _ ≤ _ := by gcongr

end
end FourierTensor.ExponentComparison
