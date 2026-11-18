import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Power-law induction for grouped residual calls and whole padded roles.
This certificate concerns a supplied recurrence. It does not construct the
full-role network or assert the square-root density target. -/
namespace FourierSchur.GroupedResidualRecurrence
open scoped BigOperators
noncomputable section

theorem residual_power (m r f k : ℕ) (hm : 0 < m) (hfk : m*f ≤ k)
    (a : ℝ) (ha : 0 ≤ a) :
    ((r*f : ℕ) : ℝ)^a ≤ ((r : ℝ)/(m : ℝ))^a*(k : ℝ)^a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hfk' : (m : ℝ)*f ≤ k := by exact_mod_cast hfk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hb : ((r*f : ℕ) : ℝ) ≤ ((r : ℝ)/(m : ℝ))*(k : ℝ) := by
    rw [Nat.cast_mul]
    have hf : (f : ℝ) ≤ (k : ℝ)/(m : ℝ) :=
      (le_div_iff₀ hm').mpr (by nlinarith [hfk'])
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hf hr
  calc
    ((r*f : ℕ) : ℝ)^a ≤ (((r : ℝ)/(m : ℝ))*(k : ℝ))^a :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hb ha
    _ = ((r : ℝ)/(m : ℝ))^a*(k : ℝ)^a :=
      Real.mul_rpow (by positivity) (Nat.cast_nonneg _)

theorem padding_contraction (beta L : ℝ) (hb : 0 < beta) (hL : L < 1) :
    (1-beta)+beta*L < 1 := by nlinarith

theorem rational_margin :
    (1-(73 : ℝ)/19906842167500) +
      ((8 : ℝ)/100000000000)*(21/500)/
        (1-14*((8 : ℝ)/100000000000)) < 1 := by norm_num

theorem power_bound {I : Type*} [Fintype I]
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K)
    (rho : I → ℕ) (hrho : ∀ i, rho i ≤ m)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (gamma a A D : ℝ) (hg : 0 ≤ gamma) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (step : ℕ → ℕ)
    (hstep : ∀ k, K ≤ k → m*step k < k)
    (M : ℝ) (hM : M = gamma + ∑ i, weight i*((rho i : ℝ)/(m : ℝ))^a)
    (hMlt : M < 1) (hgap : A ≤ D*(1-M))
    (T : ℕ → ℝ)
    (hbase : ∀ k, k < K → T k ≤ D*(k : ℝ)^a)
    (hrec : ∀ k, K ≤ k → T k ≤ A + gamma*T (m*step k) +
      ∑ i, weight i*T (rho i*step k)) :
    ∀ k, T k ≤ D*(k : ℝ)^a := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < K
    · exact hbase k hk
    have hkK : K ≤ k := Nat.le_of_not_gt hk
    have hs := hstep k hkK
    have hk1 : 1 ≤ k := le_trans hK hkK
    have hp : 1 ≤ (k : ℝ)^a :=
      Real.one_le_rpow (by exact_mod_cast hk1) ha
    have hp0 : 0 ≤ (k : ℝ)^a := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hpad : gamma*T (m*step k) ≤ gamma*(D*(k : ℝ)^a) := by
      apply mul_le_mul_of_nonneg_left _ hg
      exact le_trans (ih _ hs) (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hs.le) ha) hD)
    have hsum : (∑ i, weight i*T (rho i*step k)) ≤
        ∑ i, weight i*(D*(((rho i : ℝ)/(m : ℝ))^a*(k : ℝ)^a)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have hi : rho i*step k < k := lt_of_le_of_lt
        (Nat.mul_le_mul_right _ (hrho i)) hs
      exact le_trans (ih _ hi) (mul_le_mul_of_nonneg_left
        (residual_power m (rho i) (step k) k hm hs.le a ha) hD)
    have hfactor : gamma*(D*(k : ℝ)^a) +
        (∑ i, weight i*(D*(((rho i : ℝ)/(m : ℝ))^a*(k : ℝ)^a))) =
        D*(k : ℝ)^a*M := by
      rw [hM, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i _
        ring
    have hbudget : A + D*(k : ℝ)^a*M ≤ D*(k : ℝ)^a := by
      have hslack : A ≤ D*(k : ℝ)^a*(1-M) := by
        have hnonneg : 0 ≤ D*(1-M) := mul_nonneg hD (by linarith)
        have := mul_le_mul_of_nonneg_left hp hnonneg
        nlinarith
      nlinarith
    calc
      T k ≤ A + gamma*T (m*step k) + ∑ i, weight i*T (rho i*step k) := hrec k hkK
      _ ≤ A + gamma*(D*(k : ℝ)^a) +
          ∑ i, weight i*(D*(((rho i : ℝ)/(m : ℝ))^a*(k : ℝ)^a)) := by linarith
      _ = A + D*(k : ℝ)^a*M := by rw [add_assoc, hfactor]
      _ ≤ D*(k : ℝ)^a := hbudget

end
end FourierSchur.GroupedResidualRecurrence
