import work_in_progress.OriginalSchurDensitySufficiency
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The analytic end of the original polylogarithmic density argument.

An eventual polylogarithmic bound on a complete paid tensor profile implies
the all-order `SqrtLogProfile` required by the checked all-length compiler.
The finite exceptional orders are absorbed by a single constant. The extra
`+1` and the two synchronized-layer logarithms are retained throughout.

This file does not construct a fast tensor executor. Its final theorem still
requires the two actual uniform RAM execution certificates; a bound on local
Schur slices or the final middle bank does not supply those certificates.
-/

namespace FourierSchur.OriginalPolylogDensity

open Filter Asymptotics Real
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.PowerSaving.Skies
open OriginalSectorSubstitution OriginalCompilerRootBridge
open OriginalSchurDensitySufficiency
noncomputable section
set_option maxHeartbeats 800000

/-- The profile pays complete execution work; `+1` also pays linear routing. -/
def PolylogProfile (profile : ℕ → ℕ) : Prop :=
  ∃ a : ℕ, (fun k : ℕ => (profile k : ℝ)+1) =O[atTop]
    (fun k => Real.log ((k : ℝ)+2)^a)

/-- The tensor-density expression used in the original manuscript. -/
def paperTensorPrice (k : ℕ) : ℝ :=
  1 + Real.log ((k : ℝ)+2)^3 * Real.log (Real.log ((k : ℝ)+3))

/-- The paper's third logarithm costs at most one extra logarithmic power. -/
theorem paperTensorPrice_bigO_log :
    paperTensorPrice =O[atTop] (fun k : ℕ => Real.log ((k : ℝ)+2)^4) := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with k hk
  have h2 : 0 < (k : ℝ)+2 := by positivity
  have h3 : 0 < (k : ℝ)+3 := by positivity
  have hlog3 : 0 < Real.log ((k : ℝ)+3) := Real.log_pos
    (by nlinarith [Nat.cast_nonneg (α:=ℝ) k])
  have hinner : Real.log ((k : ℝ)+3) ≤ (k : ℝ)+2 := by
    have h := Real.log_le_sub_one_of_pos h3
    linarith
  have hthird : Real.log (Real.log ((k : ℝ)+3)) ≤ Real.log ((k : ℝ)+2) :=
    Real.log_le_log hlog3 hinner
  have hthird0 : 0 ≤ Real.log (Real.log ((k : ℝ)+3)) := by
    apply Real.log_nonneg
    exact hk.trans (Real.log_le_log h2 (by linarith))
  have hpow : 1 ≤ Real.log ((k : ℝ)+2)^4 := one_le_pow₀ hk
  rw [Real.norm_of_nonneg (by unfold paperTensorPrice; positivity),
    Real.norm_of_nonneg (by positivity)]
  unfold paperTensorPrice
  have hmul := mul_le_mul_of_nonneg_left hthird
    (show 0 ≤ Real.log ((k : ℝ)+2)^3 by positivity)
  nlinarith [show Real.log ((k : ℝ)+2)^3 * Real.log ((k : ℝ)+2) =
    Real.log ((k : ℝ)+2)^4 by ring]

theorem polylogProfile_of_paper_bound {profile : ℕ → ℕ}
    (hp : (fun k : ℕ => (profile k : ℝ)+1) =O[atTop] paperTensorPrice) :
    PolylogProfile profile :=
  ⟨4,hp.trans paperTensorPrice_bigO_log⟩

/-- Every fixed shifted logarithmic power is negligible against a square root. -/
theorem shifted_log_power_littleO_sqrt (a : ℕ) :
    (fun k : ℕ => Real.log ((k : ℝ)+2)^a) =o[atTop]
      (fun k => Real.sqrt ((k : ℝ)+2)) := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_rpow_atTop (a : ℝ)
    (by norm_num : (0 : ℝ) < 1/2)).comp_tendsto ht
  simpa only [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using h

/-- Removing the harmless shift in the square root costs a fixed factor. -/
theorem shifted_sqrt_bigO :
    (fun k : ℕ => Real.sqrt ((k : ℝ)+2)) =O[atTop]
      (fun k => Real.sqrt ((k : ℝ)+1)) := by
  apply Asymptotics.IsBigO.of_bound 2
  apply Filter.Eventually.of_forall
  intro k
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (4*((k : ℝ)+1)) := Real.sqrt_le_sqrt
      (by nlinarith [Nat.cast_nonneg (α:=ℝ) k])
    _ = 2*Real.sqrt ((k : ℝ)+1) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

/-- The two logarithms from synchronized execution preserve the saving. -/
theorem weighted_profile_littleO {profile : ℕ → ℕ}
    (hp : PolylogProfile profile) :
    (fun k : ℕ => ((profile k : ℝ)+1)*Real.log ((k : ℝ)+2)^2)
      =o[atTop] (fun k => Real.sqrt ((k : ℝ)+1)) := by
  obtain ⟨a,ha⟩ := hp
  have hm := ha.mul (isBigO_refl
    (fun k : ℕ => Real.log ((k : ℝ)+2)^2) atTop)
  have he : (fun k : ℕ => Real.log ((k : ℝ)+2)^a *
      Real.log ((k : ℝ)+2)^2) =
      (fun k : ℕ => Real.log ((k : ℝ)+2)^(a+2)) := by
    funext k
    exact (pow_add _ _ _).symm
  rw [he] at hm
  exact (hm.trans_isLittleO (shifted_log_power_littleO_sqrt (a+2))).trans_isBigO
    shifted_sqrt_bigO

/-- A tail bound extends to every natural order because the denominator
is strictly positive, including order zero. No small order is dropped. -/
theorem sqrtLogProfile_of_weighted_bigO {profile : ℕ → ℕ}
    (hp : (fun k : ℕ => ((profile k : ℝ)+1)*Real.log ((k : ℝ)+2)^2)
      =O[atTop] (fun k => Real.sqrt ((k : ℝ)+1))) :
    ∃ c : ℝ, SqrtLogProfile profile c := by
  obtain ⟨c,hc,hbound⟩ := bound_of_isBigO_nat_atTop hp
  refine ⟨c,hc.le,?_⟩
  intro k
  have hpos : 0 < Real.sqrt ((k : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have h := hbound (x:=k) (ne_of_gt hpos)
  rwa [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h

/-- Any complete polylogarithmic paid profile meets the checked compiler's
global density requirement, with one constant covering all orders. -/
theorem sqrtLogProfile_of_polylog {profile : ℕ → ℕ}
    (hp : PolylogProfile profile) : ∃ c : ℝ, SqrtLogProfile profile c :=
  sqrtLogProfile_of_weighted_bigO (weighted_profile_littleO hp).isBigO

/-- A complete uniform executor with a polylogarithmic paid profile yields
the all-length bound. The executor certificates remain explicit premises. -/
theorem executeOne_polylog {profile : ℕ → ℕ}
    (hExec : SuppliedTensorExecutor sc parentRoot .left false profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar false profile)
    (hmono : Monotone profile) (hp : PolylogProfile profile) :
    ∃ (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      (∀ (n : ℕ), 0<n → ∀ x : Vec n,
        (run program (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
          (⟨n,dft n x⟩ : Tape ℂ)
          (C*(OriginalAllLengthSubstitution.fairwind profile d n+1)) ((n+2)^p)) ∧
      (fun n : ℕ => ((C*(OriginalAllLengthSubstitution.fairwind profile d n+1) : ℕ) : ℝ))
        =O[atTop] OriginalSchurDensitySufficiency.flight := by
  obtain ⟨c,hc⟩ := sqrtLogProfile_of_polylog hp
  exact executeOne_sqrtLog hExec hScalar hmono hc

end
end FourierSchur.OriginalPolylogDensity
