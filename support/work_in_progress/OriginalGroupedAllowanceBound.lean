import work_in_progress.OriginalGroupedRecursionRAM
import work_in_progress.GroupedResidualRecurrence

/-! A profile bound for the actual grouped recursion allowance. All child
copies occur with their full multiplicities. This theorem does not replace
the open RAM body: it bounds the allowance used when that body is closed. -/
namespace FourierSchur.OriginalGroupedAllowanceBound
open OAI.PowerSaving OAI.PowerSaving.RAM OriginalGroupedRecursionRAM
open scoped BigOperators
noncomputable section

theorem grouped_allowance_bound {σ : Type} [Fintype σ]
    (u a cutoff : ℕ) (rho weights : σ → ℕ)
    (hu : 0 < u) (ha : 0 < a) (hcut : a ≤ cutoff)
    (hcutu : a+u ≤ cutoff) (hrho : ∀ t, rho t ≤ u)
    (hzero : ∀ t, rho t=0 → weights t=0)
    (z : ℝ) (hz : 0 ≤ z)
    (hM : (∑ t, (weights t : ℝ)/(2:ℝ)^a*((rho t:ℝ)/(u:ℝ))^z) < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ,
      (allowance (groupedScheme u a cutoff rho weights ha hcut hrho) k : ℝ) ≤
        C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  let s := groupedScheme u a cutoff rho weights ha hcut hrho
  let M : ℝ := ∑ t, (weights t : ℝ)/(2:ℝ)^a*((rho t:ℝ)/(u:ℝ))^z
  have hgap : 0 < 1-M := sub_pos.mpr hM
  let C : ℝ := 1+(1-M)⁻¹
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (1-M)⁻¹ := inv_nonneg.mpr hgap.le
    dsimp [C]
    linarith
  have hCG : 1 ≤ C*(1-M) := by
    dsimp only [C]
    rw [add_mul,inv_mul_cancel₀ hgap.ne']
    linarith
  have H (k : ℕ) (hk : 0 < k) :
      (allowance s k : ℝ) ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
      have hp : 1 ≤ (k:ℝ)^z := Real.one_le_rpow hk1 hz
      by_cases hK : cutoff ≤ k
      · have hak : a ≤ k := hcut.trans hK
        let f := (k-a)/u
        have hf : 0 < f := by
          have hh : 1 ≤ (k-a)/u := (Nat.le_div_iff_mul_le hu).mpr (by omega)
          exact hh
        have huf : u*f ≤ k := by
          have hh := Nat.div_mul_le_self (k-a) u
          dsimp [f]
          rw [Nat.mul_comm] at hh
          exact hh.trans (Nat.sub_le _ _)
        have hq : (2:ℝ)^k=(2:ℝ)^(k-a)*(2:ℝ)^a := by
          rw [← pow_add,Nat.sub_add_cancel hak]
        have ht (t : σ) :
            (s.count k t:ℝ)*(allowance s (s.order k t):ℝ) ≤
              (2:ℝ)^k*C*(k:ℝ)^z*
                ((weights t:ℝ)/(2:ℝ)^a*((rho t:ℝ)/(u:ℝ))^z) := by
          by_cases hw : weights t=0
          · have hc : s.count k t=0 := by simp [s,groupedScheme,hw]
            simp [hw,hc]
          · have hr : 0 < rho t := Nat.pos_of_ne_zero (fun h => hw (hzero t h))
            have hj : 0 < s.order k t := Nat.mul_pos hr hf
            have hjk : s.order k t < k :=
              grouped_order_strict u a cutoff rho weights ha hcut hrho k hK t
            have hv : (s.count k t:ℝ)*(2:ℝ)^(s.order k t) =
                (weights t:ℝ)*(2:ℝ)^(k-a) := by
              exact_mod_cast grouped_child_volume u a cutoff rho weights ha hcut hrho k hK t
            have hrp : (s.order k t:ℝ)^z ≤ ((rho t:ℝ)/(u:ℝ))^z*(k:ℝ)^z :=
              GroupedResidualRecurrence.residual_power u (rho t) f k hu huf z hz
            calc
              _ ≤ (s.count k t:ℝ)*(C*(2:ℝ)^(s.order k t)*(s.order k t:ℝ)^z) :=
                mul_le_mul_of_nonneg_left (ih _ hjk hj) (Nat.cast_nonneg _)
              _ = C*((weights t:ℝ)*(2:ℝ)^(k-a))*(s.order k t:ℝ)^z := by
                calc
                  _ = C*((s.count k t:ℝ)*(2:ℝ)^(s.order k t))*(s.order k t:ℝ)^z := by ring
                  _ = _ := by rw [hv]
              _ ≤ C*((weights t:ℝ)*(2:ℝ)^(k-a))*
                  (((rho t:ℝ)/(u:ℝ))^z*(k:ℝ)^z) := by
                apply mul_le_mul_of_nonneg_left hrp
                positivity
              _ = _ := by rw [hq]; field_simp
        have hs : (∑ t, (s.count k t:ℝ)*(allowance s (s.order k t):ℝ)) ≤
            (2:ℝ)^k*C*(k:ℝ)^z*M := by
          dsimp only [M]
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun t _ => ht t
        rw [allowance_eq]
        unfold childCharge
        push_cast
        calc
          _ ≤ (2:ℝ)^k+(2:ℝ)^k*C*(k:ℝ)^z*M := by linarith
          _ ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
            have hh : 1 ≤ C*(k:ℝ)^z*(1-M) := by
              have := mul_le_mul_of_nonneg_left hp (show 0 ≤ C*(1-M) by linarith)
              nlinarith
            have hb : 0 ≤ (2:ℝ)^k := by positivity
            nlinarith
      · have hb : allowance s k=2^k := by
          rw [allowance_eq]
          simp [childCharge,s,groupedScheme,hK]
        rw [hb,Nat.cast_pow,Nat.cast_ofNat]
        calc
          _ = 1*(2:ℝ)^k*1 := by ring
          _ ≤ _ := by gcongr
  refine ⟨C,hC,fun k => ?_⟩
  by_cases hk : k=0
  · subst k
    have hb : allowance s 0=1 := by
      rw [allowance_eq]
      have hh : ¬cutoff≤0 := by omega
      simp [childCharge,s,groupedScheme,hh]
    dsimp only [s] at hb
    rw [hb]
    simpa using hC
  · apply (H k (Nat.pos_of_ne_zero hk)).trans
    gcongr
    simp

end
end FourierSchur.OriginalGroupedAllowanceBound
