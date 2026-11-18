import vendor.OpenAIUniformFourierBundle

/-! The actual radix selector appends odd primes in increasing order, then
one power of two. Its volume controls a factorial in the number of prime
axes, giving a factor of log log N beyond the bit-length bound. -/
namespace FourierTensor.LengthSelectionBound

open OAI.PowerSaving OAI.PowerSaving.Selection Filter Real
noncomputable section

/-- After testing candidates below `p`, each chosen radix was at least its
one-based position. In particular their product dominates the factorial. -/
theorem scanned_factorial (N p : ℕ) :
    (reap N p).l ≤ p-1 ∧ (reap N p).l.factorial ≤ (reap N p).vol := by
  induction p with
  | zero => simp [reap,Cart.empty]
  | succ p ih =>
    rw [reap]
    split
    · rename_i h
      have hp : 2<p := h.1.2
      have hk : (reap N p).l+1 ≤ p := by omega
      change (reap N p).l+1 ≤ p+1-1 ∧ ((reap N p).l+1).factorial ≤ (reap N p).vol*p
      constructor
      · omega
      · rw [Nat.factorial_succ,Nat.mul_comm]
        exact Nat.mul_le_mul ih.2 hk
    · exact ⟨by omega,ih.2⟩

theorem half_power (n : ℕ) (hn : 0<n) :
    let s := (bed n).l/2
    s^s ≤ 2*n := by
  let s := (bed n).l/2
  have hl : s+s ≤ (bed n).l := by dsimp [s]; omega
  have hf : (bed n).l.factorial ≤ (bed n).vol :=
    (scanned_factorial (2*n) (harvestN n+1)).2
  have ht : (bed n).vol ≤ 2*n := (reap_baler _ _ (by omega : 0<2*n)).top
  calc
    s^s ≤ (s+1)^s := Nat.pow_le_pow_left (by omega) _
    _ ≤ s.factorial*(s+1)^s := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ ≤ (s+s).factorial := Nat.factorial_mul_pow_le_factorial
    _ ≤ (bed n).l.factorial := Nat.factorial_le hl
    _ ≤ 2*n := hf.trans ht

/-- Number of axes in the compiler's selected integer layout, including
the final dyadic radix and one extra unit for the rounded tensor profile. -/
theorem axes_eventually : ∀ᶠ n : ℕ in atTop,
    ((barge n).l : ℝ)+1 ≤ 12*(Skies.Tm n / Skies.Qm n) := by
  have hd := Skies.dwarf Skies.Ttop 2 (p:=1) (c:=1) (by norm_num) (by norm_num)
  filter_upwards [hd,eventually_gt_atTop 0,Skies.Ttop.eventually_ge_atTop 1,
    Skies.Qtop.eventually_ge_atTop 1] with n hsmall hn ht hq
  let s := (bed n).l/2
  let t := Skies.Tm n
  let q := Skies.Qm n
  have hq0 : 0<q := by dsimp [q]; linarith
  have ht0 : 0<t := by dsimp [t]; linarith
  have hq2 : q^2 ≤ t := by simpa only [q,t,Skies.Qm,one_mul,Real.rpow_one] using hsmall
  have hqt : q ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hsq : (s:ℝ)*q ≤ 4*t := by
    by_cases h : (s:ℝ)^2 ≤ t
    · nlinarith only [h, hq2, sq_nonneg ((s:ℝ)-q), ht0]
    · have hs : 0<(s:ℝ) := by
        have hh : 0≤(s:ℝ) := by positivity
        nlinarith
      have hl := Real.log_le_log ht0 (le_of_lt (lt_of_not_ge h))
      rw [Real.log_pow] at hl
      have hk : (s:ℝ)^s ≤ 2*(n:ℝ) := by exact_mod_cast half_power n hn
      have hl' := Real.log_le_log (pow_pos hs _) hk
      rw [Real.log_pow,Real.log_mul (by norm_num) (by exact_mod_cast hn.ne')] at hl'
      have hproduct : (s:ℝ)*q ≤ (s:ℝ)*((2:ℝ)*Real.log (s:ℝ)) := mul_le_mul_of_nonneg_left hl hs.le
      change q ≤ _ at hl
      change _ ≤ Real.log 2+t at hl'
      have ht1 : 1≤t := ht
      nlinarith only [hproduct,hl',ht1,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlen : (barge n).l+1 ≤ 2*s+3 := by
    change (bed n).l+1+1 ≤ 2*((bed n).l/2)+3
    omega
  have hlen' : ((barge n).l:ℝ)+1 ≤ 2*(s:ℝ)+3 := by exact_mod_cast hlen
  change _ ≤ 12*(t/q)
  rw [← mul_div_assoc,le_div_iff₀ hq0]
  nlinarith [mul_le_mul_of_nonneg_right hlen' hq0.le]

end
end FourierTensor.LengthSelectionBound
