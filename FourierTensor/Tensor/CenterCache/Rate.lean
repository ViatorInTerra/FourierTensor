import work_in_progress.OriginalGroupedResidualCertificate
import work_in_progress.OriginalGroupedAllowanceBound

/-!
# Arithmetic rate of the center-cache histogram

This module checks the twelve modified counts, their exact rank deficit,
and a strict padded moment at exponent `1 - 3 / 100000000`. It also bounds
the numerical grouped allowance built from those counts, including every
padding and spectator term.

The finite table is used by `CenterCacheCensus` to price the emitted
instructions. `CenterCacheCharge` identifies the resulting integer
recurrence with the one evaluated here.
-/

namespace FourierTensor.CenterCacheRate

open FourierSchur
open OriginalGroupedResidualCertificate
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 2000000

def invocations : ℕ := 3 * 4060 ^ 2

def savedPerInvocation : ℕ := 32 + 4

def eliminatedCalls : ℕ := invocations * savedPerInvocation

def count (i : Fin 12) : ℕ :=
  if i.val = 3 then 3115400400 else count32 i

def saving : ℕ := 86374064000

def epsilon : ℝ := 3 / 100000000

def exponent : ℝ := 1 - epsilon

def weight (i : Fin 12) : ℝ := (count i : ℝ) / (roles32 : ℝ)

def paddedWeight (i : Fin 12) : ℝ := (count i : ℝ) / (padded32 : ℝ)

def paddedMoment (z : ℝ) : ℝ := padding32 + moment paddedWeight point32 z

theorem saved_counts :
    invocations = 49450800 ∧ savedPerInvocation = 36 ∧
    eliminatedCalls = 1780228800 := by
  norm_num [invocations, savedPerInvocation, eliminatedCalls]

theorem count_eq_sub (i : Fin 12) :
    count i = count32 i - if i.val = 3 then eliminatedCalls else 0 := by
  fin_cases i <;>
    norm_num [count, count32, eliminatedCalls, invocations, savedPerInvocation]

theorem modified_rank32 : count 3 = 3115400400 := by
  norm_num [count]

theorem unchanged_count (i : Fin 12) (hi : i ≠ 3) : count i = count32 i := by
  have hval : i.val ≠ 3 := by
    intro h
    exact hi (Fin.ext h)
  simp [count, hval]

theorem count_positive (i : Fin 12) : 0 < count i := by
  fin_cases i <;> norm_num [count, count32]

theorem total_count : (∑ i, count i) = 2615907775843600 := by
  norm_num [count, count32, Fin.sum_univ_succ]

theorem saving_eq : saving = saving32 + 32 * eliminatedCalls := by
  norm_num [saving, saving32, eliminatedCalls, invocations, savedPerInvocation]

theorem exact_rank_deficit :
    (∑ i, count i * rho32 i) + saving = roles32 * order32 := by
  norm_num [count, count32, rho32, saving, roles32, order32, Fin.sum_univ_succ]

theorem exponents_pos_lt : 0 < exponent ∧ exponent < 1 := by
  norm_num [exponent, epsilon]

theorem weight_nonnegative (i : Fin 12) : 0 ≤ weight i := by
  unfold weight
  positivity

theorem first_moment_eq :
    firstMoment weight point32 = 1 - (655 : ℝ) / 150000840704 := by
  norm_num [firstMoment, weight, point32, count, count32, rho32,
    roles32, order32, Fin.sum_univ_succ]

/-- A supplied dyadic ceiling bounds the logarithm. It need not be minimal. -/
theorem dyadic_log_bound (u r k : ℕ) (hu : 0 < u) (hr : 0 < r)
    (hceiling : u ≤ r * 2 ^ k) :
    Real.log ((u : ℝ) / (r : ℝ)) ≤ (7 : ℝ) / 10 * k := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpower : (u : ℝ) ≤ (r : ℝ) * (2 : ℝ) ^ k := by
    exact_mod_cast hceiling
  have hratio : (u : ℝ) / (r : ℝ) ≤ (2 : ℝ) ^ k :=
    (div_le_iff₀ hr').mpr (by simpa [mul_comm] using hpower)
  have hlog := Real.log_le_log (div_pos hu' hr') hratio
  rw [Real.log_pow] at hlog
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hupper := mul_le_mul_of_nonneg_left log_two_upper hk
  nlinarith

def dyadicExponent : Fin 12 → ℕ :=
  ![15, 11, 11, 10, 6, 6, 6, 6, 1, 1, 1, 1]

theorem dyadic_ceiling (i : Fin 12) :
    order32 ≤ rho32 i * 2 ^ dyadicExponent i := by
  fin_cases i <;> norm_num [order32, rho32, dyadicExponent]

theorem point_log_bound (i : Fin 12) :
    Real.log (1 / point32 i) ≤ (7 : ℝ) / 10 * dyadicExponent i := by
  have he : 1 / point32 i = (order32 : ℝ) / (rho32 i : ℝ) := by
    unfold point32
    field_simp
  rw [he]
  exact dyadic_log_bound order32 (rho32 i) (dyadicExponent i)
    (by norm_num [order32]) (ranges32 i).1 (dyadic_ceiling i)

def logarithmicCap (i : Fin 12) : ℝ :=
  min (1 - point32 i) (((7 : ℝ) / 10 * dyadicExponent i) * point32 i)

theorem point_logarithmic_cap (i : Fin 12) :
    point32 i * Real.log (1 / point32 i) ≤ logarithmicCap i := by
  apply le_min
  · exact log_reciprocal_moment_le _ (point32_pos_le i).1
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (point_log_bound i) (point32_pos_le i).1.le

theorem logarithmic_cap_sum :
    (∑ i, weight i * logarithmicCap i) =
      (87143565787 : ℝ) / 750004203520 := by
  norm_num [weight, logarithmicCap, point32, dyadicExponent, count, count32,
    rho32, roles32, order32, Fin.sum_univ_succ]

theorem logarithmic_moment_bound :
    logMoment weight point32 ≤ (87143565787 : ℝ) / 750004203520 := by
  have h : logMoment weight point32 ≤ ∑ i, weight i * logarithmicCap i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (point_logarithmic_cap i) (weight_nonnegative i)
  simpa only [logarithmic_cap_sum] using h

def margin : ℝ :=
  (655 : ℝ) / 150000840704 -
    epsilon * (87143565787 / 750004203520) / (1 - 11 * epsilon)

def paddedMargin : ℝ := (roles32 : ℝ) / (padded32 : ℝ) * margin

theorem exact_margin : margin = (16517298641 : ℝ) / 18750098900465320960 := by
  norm_num [margin, epsilon]

theorem exact_padded_margin :
    paddedMargin = (3403306798484845 : ℝ) / 7205757025892190348378112 := by
  norm_num [paddedMargin, margin, roles32, padded32, epsilon]

theorem padded_margin_positive : 0 < paddedMargin := by
  rw [exact_padded_margin]
  norm_num

theorem moment_bound : moment weight point32 exponent ≤ 1 - margin := by
  have h := moment_perturb_bound weight point32 epsilon 11
    weight_nonnegative point32_pos_le (by norm_num [epsilon])
    log32_upper (by norm_num [epsilon])
  change moment weight point32 exponent ≤ _ at h
  rw [first_moment_eq] at h
  have he : 0 ≤ epsilon := by norm_num [epsilon]
  have hd : 0 ≤ 1 - 11 * epsilon := by norm_num [epsilon]
  have hlog := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left logarithmic_moment_bound he) hd
  have htotal := h.trans (add_le_add_right hlog _)
  simpa [margin, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htotal

theorem padded_moment_factor (z : ℝ) :
    paddedMoment z = (1 - (roles32 : ℝ) / (padded32 : ℝ)) +
      (roles32 : ℝ) / (padded32 : ℝ) * moment weight point32 z := by
  unfold paddedMoment moment
  rw [Finset.mul_sum]
  congr 1
  · norm_num [padding32, roles32, padded32]
  · apply Finset.sum_congr rfl
    intro i _
    unfold paddedWeight weight
    norm_num [roles32, padded32]
    ring

theorem strict_padded_margin : paddedMoment exponent ≤ 1 - paddedMargin := by
  rw [padded_moment_factor]
  have h := mul_le_mul_of_nonneg_left moment_bound
    (show (0 : ℝ) ≤ (roles32 : ℝ) / (padded32 : ℝ) by positivity)
  unfold paddedMargin
  nlinarith

theorem padded_moment_lt_one : paddedMoment exponent < 1 := by
  exact strict_padded_margin.trans_lt (sub_lt_self _ padded_margin_positive)

theorem zero_moment :
    paddedMoment 0 = (98067401202807 : ℝ) / 35184372088832 := by
  norm_num [paddedMoment, moment, padding32, paddedWeight,
    count, count32, roles32, padded32, Fin.sum_univ_succ]

theorem zero_moment_gt_one : 1 < paddedMoment 0 := by
  rw [zero_moment]
  norm_num

/-- The original inventory does not have a contracting moment at this exponent. -/
theorem original_padded_moment_lower :
    1 + (271353806171 : ℝ) / 18446744073709551616000 ≤
      paddedMoment32 exponent := by
  have log_two_lower : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  let lower : Fin 12 → ℝ := fun i => if i.val = 5 ∨ i.val = 7 then 5 / 2 else 0
  have lower_log (i : Fin 12) : lower i ≤ Real.log (1 / point32 i) := by
    by_cases hi : i.val = 5 ∨ i.val = 7
    · have hrho : rho32 i ≤ 1024 := by
        fin_cases i <;> norm_num [rho32] at *
      have hr : (0 : ℝ) < rho32 i := by exact_mod_cast (ranges32 i).1
      have hsmall : (rho32 i : ℝ) ≤ 1024 := by exact_mod_cast hrho
      have hratio : (32 : ℝ) ≤ 1 / point32 i := by
        change (32 : ℝ) ≤ 1 / ((rho32 i : ℝ) / (32768 : ℝ))
        rw [one_div_div]
        exact (le_div_iff₀ hr).mpr (by nlinarith)
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 32) hratio
      rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow] at hlog
      dsimp only [lower]
      rw [if_pos hi]
      norm_num at hlog
      rw [one_div, Real.log_inv]
      linarith
    · simp only [lower, if_neg hi]
      exact Real.log_nonneg
        ((le_div_iff₀ (point32_pos_le i).1).mpr (by simpa using (point32_pos_le i).2))
  have hlog : (15141034125 : ℝ) / 300001681408 ≤ logMoment weight32 point32 := by
    have hsum : (∑ i, weight32 i * (point32 i * lower i)) ≤
        logMoment weight32 point32 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (lower_log i) (point32_pos_le i).1.le)
        (weight32_nonneg i)
    norm_num [lower, weight32, point32, count32, rho32, roles32, order32,
      Fin.sum_univ_succ] at hsum
    exact hsum
  have lower_power (i : Fin 12) :
      point32 i + epsilon * (point32 i * Real.log (1 / point32 i)) ≤
        (point32 i) ^ exponent := by
    let x := point32 i
    let y := epsilon * Real.log (1 / x)
    have hx : 0 < x := (point32_pos_le i).1
    have hlogx : Real.log (1 / x) = -Real.log x := by
      simp [one_div, Real.log_inv]
    have he : Real.log x * (1 - epsilon) = Real.log x + y := by
      dsimp [y]
      rw [hlogx]
      ring
    change x + epsilon * (x * Real.log (1 / x)) ≤ x ^ (1 - epsilon)
    rw [Real.rpow_def_of_pos hx, he, Real.exp_add, Real.exp_log hx]
    calc
      x + epsilon * (x * Real.log (1 / x)) = x * (y + 1) := by dsimp [y]; ring
      _ ≤ x * Real.exp y := mul_le_mul_of_nonneg_left (Real.add_one_le_exp y) hx.le
  have hmoment : firstMoment weight32 point32 + epsilon * logMoment weight32 point32 ≤
      moment weight32 point32 exponent := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (lower_power i) (weight32_nonneg i))
    calc
      _ = ∑ i, weight32 i *
          (point32 i + epsilon * (point32 i * Real.log (1 / point32 i))) := by
        unfold firstMoment logMoment
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := hsum
  rw [firstMoment32_eq] at hmoment
  have he := mul_le_mul_of_nonneg_left hlog (show 0 ≤ epsilon by norm_num [epsilon])
  have hactive : 1 + (6584819 : ℝ) / 240001345126400000 ≤
      moment weight32 point32 exponent := by
    norm_num [epsilon] at he hmoment
    linarith
  rw [paddedMoment32_factor]
  have hp := mul_le_mul_of_nonneg_left hactive
    (show (0 : ℝ) ≤ (roles32 : ℝ) / (padded32 : ℝ) by positivity)
  norm_num [roles32, padded32] at hp ⊢
  linarith

theorem original_padded_moment_gt_one : 1 < paddedMoment32 exponent := by
  exact lt_of_lt_of_le (by norm_num) original_padded_moment_lower

/-- The extra kind is the original independent padding family. -/
def rank : Option (Fin 12) → ℕ
  | none => order32
  | some i => rho32 i

def multiplicity : Option (Fin 12) → ℕ
  | none => padded32 - roles32
  | some i => count i

theorem rank_positive (i : Option (Fin 12)) : 0 < rank i := by
  cases i with
  | none => norm_num [rank, order32]
  | some i => exact (ranges32 i).1

theorem rank_le_order (i : Option (Fin 12)) : rank i ≤ order32 := by
  cases i with
  | none => exact le_rfl
  | some i => exact (ranges32 i).2.1.le

theorem grouped_moment_eq (z : ℝ) :
    (∑ i, (multiplicity i : ℝ) / (2 : ℝ) ^ 50 *
      ((rank i : ℝ) / (order32 : ℝ)) ^ z) = paddedMoment z := by
  rw [Fintype.sum_option]
  simp only [rank, multiplicity]
  norm_num only [order32, Nat.cast_ofNat, div_self (by norm_num : (32768 : ℝ) ≠ 0),
    Real.one_rpow, mul_one]
  rfl

def scheme : OriginalGroupedRecursionRAM.Scheme (Option (Fin 12)) :=
  OriginalGroupedRecursionRAM.groupedScheme order32 50 (50 + order32)
    rank multiplicity (by decide) (Nat.le_add_right _ _) rank_le_order

/-- A bound for the numerical recurrence, with no semantic word premise. -/
theorem allowance_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      (OriginalGroupedRecursionRAM.allowance scheme n : ℝ) ≤
        C * (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ exponent := by
  apply OriginalGroupedAllowanceBound.grouped_allowance_bound
    order32 50 (50 + order32) rank multiplicity
    (by norm_num [order32]) (by decide) (Nat.le_add_right _ _) le_rfl
    rank_le_order
  · intro i hi
    exact False.elim ((Nat.ne_of_gt (rank_positive i)) hi)
  · exact exponents_pos_lt.1.le
  · rw [grouped_moment_eq]
    exact padded_moment_lt_one

end
end FourierTensor.CenterCacheRate
