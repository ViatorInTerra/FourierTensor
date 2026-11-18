import FourierTensor.Tensor.Workspace
import FourierTensor.DFT.LengthSelection
import work_in_progress.OriginalAllLengthSubstitution

/-! Work of the all-length Fourier compiler with the certified tensor
profile. The estimate uses the compiled layer count and the size of its
selected working transform. The direct branch is included in the bill. -/
namespace FourierTensor.AllLengthAsymptotics

open FourierSchur OAI.PowerSaving OAI.PowerSaving.Selection
open OAI.PowerSaving.Skies OAI.PowerSaving.Slant Real Filter Asymptotics
open scoped BigOperators
noncomputable section

def rate (n : ℕ) : ℝ :=
  (n : ℝ) * (Tm n)^CenterCacheRate.exponent * (Qm n)^(2-CenterCacheRate.exponent)

/-- Truncating each logarithm below at one makes the envelope positive at
all positive lengths, including length one. -/
def guardedRate (n : ℕ) : ℝ :=
  (n : ℝ) * (max 1 (Tm n))^CenterCacheRate.exponent *
    (max 1 (Qm n))^(2-CenterCacheRate.exponent)

theorem guardedRate_eventually : guardedRate =ᶠ[atTop] rate := by
  filter_upwards [Ttop.eventually_ge_atTop 1, Qtop.eventually_ge_atTop 1] with n ht hq
  simp only [guardedRate,rate,max_eq_right ht,max_eq_right hq]

private theorem length_le_rate (n : ℕ) (ht : 1 ≤ Tm n) (hq : 1 ≤ Qm n) :
    (n : ℝ) ≤ rate n := by
  calc
    (n : ℝ) = n*1*1 := by ring
    _ ≤ rate n := by
      unfold rate
      gcongr
      · exact one_le_rpow ht CenterCacheRate.exponents_pos_lt.1.le
      · exact one_le_rpow hq (by linarith [CenterCacheRate.exponents_pos_lt.2])

private theorem density_bound (n : ℕ) (ht : 1 ≤ Tm n) (hq : 1 ≤ Qm n)
    (hcount : ((barge n).l : ℝ)+1 ≤ 12*(Tm n/Qm n)) :
    (WorkspaceExecutor.density (barge n).l : ℝ) + 1 ≤ 100*(Tm n/Qm n)^CenterCacheRate.exponent := by
  let z := CenterCacheRate.exponent
  have he : 0 < Tm n := by linarith
  have heq : 0 < Qm n := by linarith
  have hratio : 1 ≤ Tm n/Qm n := (le_div_iff₀ heq).2 (by
    rw [one_mul]; exact (log_le_sub_one_of_pos he).trans (by linarith))
  have hratio0 : 0 ≤ Tm n/Qm n := le_trans zero_le_one hratio
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg
    (by positivity : (0 : ℝ) ≤ (barge n).l + 1) z)
  have hp : (((barge n).l : ℝ)+1)^z ≤ (12*(Tm n/Qm n))^z :=
    Real.rpow_le_rpow (by positivity) hcount CenterCacheRate.exponents_pos_lt.1.le
  have h12 : (12:ℝ)^z ≤ 12 := by
    simpa only [rpow_one] using (rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 12)
      CenterCacheRate.exponents_pos_lt.2.le)
  rw [mul_rpow (by norm_num) hratio0] at hp
  have hmul := mul_le_mul_of_nonneg_right h12 (rpow_nonneg hratio0 z)
  have hone := one_le_rpow hratio CenterCacheRate.exponents_pos_lt.1.le
  change (⌈(((barge n).l:ℝ)+1)^z⌉₊:ℝ)+1 ≤ 100*(Tm n/Qm n)^z
  change 1 ≤ (Tm n/Qm n)^z at hone
  linarith

private theorem leg_bound (n : ℕ) (hn : 0 < n) (ht : 1 ≤ Tm n) (hq : 1 ≤ Qm n)
    (hcount : ((barge n).l : ℝ)+1 ≤ 12*(Tm n/Qm n)) :
    (OriginalWorkingSubstitution.leg WorkspaceExecutor.density n : ℝ) ≤ 10^40 * rate n := by
  have hv : ((barge n).vol : ℝ) ≤ 4*n := by exact_mod_cast (barge_spec n hn).upper.le
  unfold OriginalWorkingSubstitution.leg
  push_cast
  calc
    _ ≤ (10^32*Qm n^2) * ((4*n)*(100*(Tm n/Qm n)^CenterCacheRate.exponent)) :=
      mul_le_mul (score_lim n n hn le_rfl (by omega) ht hq)
        (mul_le_mul hv (density_bound n ht hq hcount) (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = (4*100*10^32)*rate n := by
      have hq0 : 0 < Qm n := by linarith
      rw [rate,div_rpow (by linarith) hq0.le,rpow_sub hq0,Real.rpow_two]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) ((Nat.cast_nonneg n).trans
      (length_le_rate n ht hq))

/-- The integer allowance includes synchronized work, stack preparation
and the polynomial direct fallback on lengths failing the ports test. -/
theorem wind_eventually (d : ℕ) : ∀ᶠ n in atTop,
    (OriginalAllLengthSubstitution.fairwind WorkspaceExecutor.density d n:ℝ)+1 ≤ 10^41*rate n := by
  have hid (n : ℕ) : n ≤ id n ∧ id n ≤ 2*n := ⟨le_rfl,by dsimp; omega⟩
  filter_upwards [docks_ev hid,polylog_ev hid d,eventually_gt_atTop 0,
    Ttop.eventually_ge_atTop 1,Qtop.eventually_ge_atTop 1,LengthSelectionBound.axes_eventually]
    with n hports hstack hn ht hq hcount
  change Ports n at hports
  change ((stackN n : ℝ)+2)^d ≤ n at hstack
  unfold OriginalAllLengthSubstitution.fairwind OriginalArbitraryLengthSubstitution.Bench.surf
  rw [if_pos hports,Nat.add_zero]
  push_cast
  have h := leg_bound n hn ht hq hcount
  have hN := length_le_rate n ht hq
  have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  linarith

theorem wind_bigO (d : ℕ) :
    (fun n => ((OriginalAllLengthSubstitution.fairwind WorkspaceExecutor.density d n+1:ℕ):ℝ))
      =O[atTop] rate := by
  refine isBigO_iff.mpr ⟨10^41,?_⟩
  filter_upwards [wind_eventually d,Ttop.eventually_ge_atTop 1,Qtop.eventually_ge_atTop 1]
    with n h ht hq
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg
    ((Nat.cast_nonneg n).trans (length_le_rate n ht hq))]
  exact_mod_cast h

/-- Any positive slack in the exponent of the first logarithm absorbs the
iterated-logarithm factor. -/
theorem rate_little_speed {v : ℝ} (hv : CenterCacheRate.exponent < v) :
    rate =o[atTop] speed v := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [Ttop.eventually_ge_atTop 1,Qtop.eventually_ge_atTop 1,
    dwarf Ttop 2 (p:=v-CenterCacheRate.exponent) (sub_pos.mpr hv) hc] with n ht hq hsmall
  have he : 0 < Tm n := by linarith
  have hsecond : (Qm n)^(2-CenterCacheRate.exponent) ≤ Qm n ^ 2 := by
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le hq
      (show 2-CenterCacheRate.exponent ≤ (2:ℝ) by linarith [CenterCacheRate.exponents_pos_lt.1])
  rw [Real.norm_of_nonneg ((Nat.cast_nonneg n).trans (length_le_rate n ht hq)),
    Real.norm_of_nonneg (show 0 ≤ speed v n by unfold speed; positivity)]
  calc
    rate n ≤ ((n:ℝ)*Tm n^CenterCacheRate.exponent)*(c*Tm n^(v-CenterCacheRate.exponent)) :=
      mul_le_mul_of_nonneg_left (hsecond.trans hsmall) (by positivity)
    _ = c*((n:ℝ)*(Tm n^CenterCacheRate.exponent * Tm n^(v-CenterCacheRate.exponent))) := by ring
    _ = c*speed v n := by
      rw [← rpow_add he,show CenterCacheRate.exponent+(v-CenterCacheRate.exponent)=v by ring]
      rfl

theorem rate_little_paper : rate =o[atTop] paperTime := by
  have h : CenterCacheRate.exponent < alpha := by
    norm_num [CenterCacheRate.exponent,CenterCacheRate.epsilon,alpha]
  exact (rate_little_speed (h.trans alpha_theta)).trans_isBigO speed_paper

/-- Enlarge the constant on the finite initial interval of Fourier lengths.
Thus the elementary real envelope applies to the same bill at every positive
length, including those served by the direct transform. -/
theorem uniformize (W : ℕ → ℕ) (hW : (fun n => (W n:ℝ)) =O[atTop] rate) :
    ∃ C : ℝ, 0<C ∧ ∀ n, 0<n → (W n:ℝ) ≤ C*guardedRate n := by
  obtain ⟨c,hc⟩ := isBigO_iff.mp hW
  have he : ∀ᶠ n in atTop, (W n:ℝ) ≤ c*guardedRate n := by
    filter_upwards [hc,guardedRate_eventually,Ttop.eventually_ge_atTop 1,
      Qtop.eventually_ge_atTop 1] with n h hg ht hq
    rw [hg]
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg
      ((Nat.cast_nonneg n).trans (length_le_rate n ht hq))] using h
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.1 he
  let s : ℝ := ∑ j ∈ Finset.range k, (W j:ℝ)
  let C : ℝ := max c (s+1)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  have hsc : s+1 ≤ C := le_max_right _ _
  refine ⟨C,by linarith,?_⟩
  intro n hn
  have hg : 1 ≤ guardedRate n := by
    have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    have h1 := one_le_rpow (le_max_left 1 (Tm n)) CenterCacheRate.exponents_pos_lt.1.le
    have h2 : 1 ≤ (max 1 (Qm n))^(2-CenterCacheRate.exponent) :=
      one_le_rpow (le_max_left _ _) (by linarith [CenterCacheRate.exponents_pos_lt.2])
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN h1) h2
  by_cases h : k ≤ n
  · exact (hk n h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hw : (W n:ℝ) ≤ s := Finset.single_le_sum (fun j _ => Nat.cast_nonneg (W j))
      (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
    exact (show (W n:ℝ) ≤ C by linarith).trans (le_mul_of_one_le_right (by linarith) hg)

end
end FourierTensor.AllLengthAsymptotics
