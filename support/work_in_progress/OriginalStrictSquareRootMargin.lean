import work_in_progress.OriginalGroupedAllowanceBound
import work_in_progress.OriginalPolylogDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
The strict finite square-root margin pays the final compiler's logarithms.
This module supplies integration of an ACTUAL charged finite inventory; it
does not assert that the current physical executor has that margin.
Zero-rank terms, full-order terms, finite exceptional orders and +1 routing
are retained.  Continuity selects a strictly subhalf exponent, rather than
silently using a square-root profile with unpaid logarithmic factors.
-/
namespace FourierSchur.OriginalStrictSquareRootMargin
open Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 800000

variable {σ : Type} [Fintype σ]

def finiteMoment (u a : ℕ) (rho weights : σ → ℕ) (z : ℝ) : ℝ :=
  ∑ t, (weights t : ℝ)/(2:ℝ)^a*((rho t:ℝ)/(u:ℝ))^z

theorem moment_continuous_at_half (u a : ℕ) (rho weights : σ → ℕ) :
    ContinuousAt (finiteMoment u a rho weights) (1/2:ℝ) := by
  unfold finiteMoment
  classical
  have H (s : Finset σ) : ContinuousAt
      (fun z : ℝ => ∑ t ∈ s, (weights t:ℝ)/(2:ℝ)^a*((rho t:ℝ)/(u:ℝ))^z)
      (1/2:ℝ) := by
    induction s using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) (1/2))
    | @insert t s ht ih =>
      simp only [Finset.sum_insert ht]
      exact (continuousAt_const.mul (Real.continuousAt_const_rpow' (by norm_num))).add ih
  exact H Finset.univ

theorem subhalf_of_strict_sqrt (u a : ℕ) (rho weights : σ → ℕ)
    (hM : finiteMoment u a rho weights (1/2) < 1) :
    ∃ z : ℝ, 0<z ∧ z<1/2 ∧ finiteMoment u a rho weights z<1 := by
  have he : ∀ᶠ z in 𝓝 (1/2:ℝ), finiteMoment u a rho weights z<1 :=
    (moment_continuous_at_half u a rho weights).eventually (gt_mem_nhds hM)
  obtain ⟨l,v,hlv,hsub⟩ := he.exists_Ioo_subset
  have hmax : max l 0 < (1/2:ℝ) := max_lt hlv.1 (by norm_num)
  refine ⟨(max l 0+1/2)/2,?_,?_,?_⟩
  · have h0 : 0≤max l 0 := le_max_right _ _
    linarith
  · linarith
  · apply hsub
    constructor
    · have hl : l≤max l 0 := le_max_left _ _
      linarith
    · linarith [hlv.2]

def powerProfile (z : ℝ) (k : ℕ) : ℕ := Nat.ceil (((k:ℝ)+1)^z)

theorem powerProfile_monotone (z : ℝ) (hz : 0≤z) : Monotone (powerProfile z) := by
  intro k l hkl
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow (by positivity) _ hz
  exact_mod_cast Nat.add_le_add_right hkl 1

theorem powerProfile_bound (z : ℝ) (hz : 0≤z) (k : ℕ) :
    (powerProfile z k:ℝ)+1 ≤ 3*((k:ℝ)+2)^z := by
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg
    (by positivity : 0≤(k:ℝ)+1) z)
  have hm : ((k:ℝ)+1)^z ≤ ((k:ℝ)+2)^z :=
    Real.rpow_le_rpow (by positivity) (by linarith) hz
  have hbase : (1:ℝ)≤(k:ℝ)+2 := by have hk := Nat.cast_nonneg (α:=ℝ) k; linarith
  have h1 : 1≤((k:ℝ)+2)^z := Real.one_le_rpow hbase hz
  unfold powerProfile
  linarith

theorem powerProfile_bigO (z : ℝ) (hz : 0≤z) :
    (fun k : ℕ => (powerProfile z k:ℝ)+1) =O[atTop]
      (fun k => ((k:ℝ)+2)^z) := by
  apply IsBigO.of_bound 3
  apply Filter.Eventually.of_forall
  intro k
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  exact powerProfile_bound z hz k

theorem subhalf_log_absorption (z : ℝ) (hz : z<1/2) :
    (fun k : ℕ => ((k:ℝ)+2)^z*Real.log ((k:ℝ)+2)^2) =o[atTop]
      (fun k => Real.sqrt ((k:ℝ)+2)) := by
  have ht : Tendsto (fun k : ℕ => (k:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hl := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (show (0:ℝ)<1/2-z by linarith)).comp_tendsto ht
  have hp := (isBigO_refl (fun k : ℕ => ((k:ℝ)+2)^z) atTop).mul_isLittleO hl
  have he (k : ℕ) : ((k:ℝ)+2)^z*((k:ℝ)+2)^(1/2-z)=Real.sqrt ((k:ℝ)+2) := by
    rw [← Real.rpow_add (by positivity)]
    have hsum : z+(1/2-z)=(1/2:ℝ) := by ring
    rw [hsum,Real.sqrt_eq_rpow]
  simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_two,he] using hp

theorem weighted_powerProfile_littleO (z : ℝ) (hz : 0≤z) (hhalf : z<1/2) :
    (fun k : ℕ => ((powerProfile z k:ℝ)+1)*Real.log ((k:ℝ)+2)^2)
      =o[atTop] (fun k => Real.sqrt ((k:ℝ)+1)) := by
  have H := (powerProfile_bigO z hz).mul
    (isBigO_refl (fun k : ℕ => Real.log ((k:ℝ)+2)^2) atTop)
  exact (H.trans_isLittleO (subhalf_log_absorption z hhalf)).trans_isBigO
    OriginalPolylogDensity.shifted_sqrt_bigO

theorem powerProfile_sqrtLog (z : ℝ) (hz : 0≤z) (hhalf : z<1/2) :
    ∃ c : ℝ, OriginalSchurDensitySufficiency.SqrtLogProfile (powerProfile z) c :=
  OriginalPolylogDensity.sqrtLogProfile_of_weighted_bigO
    (weighted_powerProfile_littleO z hz hhalf).isBigO

/-- This is the exact profile side of the charged grouped recurrence.
An actual native OpenBody is still required to obtain a RAM executor. -/
theorem allowance_profile_of_strict_sqrt
    (u a cutoff : ℕ) (rho weights : σ → ℕ)
    (hu : 0<u) (ha : 0<a) (hcut : a≤cutoff) (hcutu : a+u≤cutoff)
    (hrho : ∀ t,rho t≤u) (hzero : ∀ t,rho t=0 → weights t=0)
    (hM : finiteMoment u a rho weights (1/2)<1) :
    ∃ (z : ℝ) (c : ℕ) (C : ℝ),
      0<z ∧ z<1/2 ∧ Monotone (powerProfile z) ∧
      OriginalSchurDensitySufficiency.SqrtLogProfile (powerProfile z) C ∧
      ∀ k : ℕ,
        OriginalGroupedRecursionRAM.allowance
          (OriginalGroupedRecursionRAM.groupedScheme u a cutoff rho weights ha hcut hrho) k+1 ≤
        c*(2^k*powerProfile z k+1) := by
  obtain ⟨z,hz,hhalf,hm⟩ := subhalf_of_strict_sqrt u a rho weights hM
  obtain ⟨B,hB,hbound⟩ := OriginalGroupedAllowanceBound.grouped_allowance_bound
    u a cutoff rho weights hu ha hcut hcutu hrho hzero z hz.le hm
  obtain ⟨c,hc⟩ := exists_nat_ge B
  have hc1 : 1≤c := Nat.one_le_cast.mp (hB.trans hc)
  obtain ⟨C,hC⟩ := powerProfile_sqrtLog z hz.le hhalf
  refine ⟨z,c,C,hz,hhalf,powerProfile_monotone z hz.le,hC,fun k => ?_⟩
  have hp : ((k:ℝ)+1)^z ≤ (powerProfile z k:ℝ) := Nat.le_ceil _
  have he : (OriginalGroupedRecursionRAM.allowance
      (OriginalGroupedRecursionRAM.groupedScheme u a cutoff rho weights ha hcut hrho) k:ℝ) ≤
      (c:ℝ)*((2:ℝ)^k*(powerProfile z k:ℝ)) := by
    apply (hbound k).trans
    rw [← mul_assoc]
    gcongr
  have hn : OriginalGroupedRecursionRAM.allowance
      (OriginalGroupedRecursionRAM.groupedScheme u a cutoff rho weights ha hcut hrho) k ≤
      c*(2^k*powerProfile z k) := by exact_mod_cast he
  rw [mul_add,mul_one]
  omega

end
end FourierSchur.OriginalStrictSquareRootMargin
