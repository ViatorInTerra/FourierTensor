import work_in_progress.OriginalPolylogDensity
import work_in_progress.OriginalMonotoneDensity

/-! The complete conditional adaptation of the paper's analytic conclusion.
Neither monotonicity nor a separate all-order density constant is required
from the caller. Both genuine paid uniform tensor executors remain required.
The finite prefix maximum is only a work allowance for the same programs;
it is not an uncharged runtime computation or a faster circuit construction. -/

namespace FourierSchur.OriginalPolylogExecutor

open Filter Asymptotics Real
open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.PowerSaving.Skies
open OriginalSectorSubstitution OriginalCompilerRootBridge
open OriginalPolylogDensity OriginalMonotoneDensity
noncomputable section
set_option maxHeartbeats 800000

theorem prefixMax_polylog {profile : ℕ → ℕ} (hp : PolylogProfile profile) :
    PolylogProfile (prefixMax profile) := by
  obtain ⟨a,ha⟩ := hp
  exact ⟨a,prefixMax_isBigO_log profile a ha⟩

/-- The compiler's unshifted logarithm implies the protected headline form. -/
theorem flight_bigO_shifted :
    OriginalSchurDensitySufficiency.flight =O[atTop]
      (fun n : ℕ => (n : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_log hnR (show (n : ℝ) ≤ (n : ℝ)+2 by linarith)
  rw [Real.norm_of_nonneg (by unfold OriginalSchurDensitySufficiency.flight; positivity),
    Real.norm_of_nonneg (by positivity),one_mul]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) (Nat.cast_nonneg n)

/-- Any actual complete uniform tensor executors with an eventual
polylogarithmic paid profile yield one program for all positive DFT lengths.
Root preparation, routing, fallback, and the integer cap are still charged. -/
theorem executeOne_polylog {profile : ℕ → ℕ}
    (hExec : SuppliedTensorExecutor sc parentRoot .left false profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar false profile)
    (hp : PolylogProfile profile) :
    ∃ (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      (∀ (n : ℕ), 0<n → ∀ x : Vec n,
        (run program (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
          (⟨n,dft n x⟩ : Tape ℂ)
          (C*(OriginalAllLengthSubstitution.fairwind (prefixMax profile) d n+1)) ((n+2)^p)) ∧
      (fun n : ℕ =>
        ((C*(OriginalAllLengthSubstitution.fairwind (prefixMax profile) d n+1) : ℕ) : ℝ))
        =O[atTop] (fun n : ℕ => (n : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) := by
  obtain ⟨program,d,C,p,hprogram,hcost⟩ := OriginalPolylogDensity.executeOne_polylog
    (suppliedExecutor_prefixMax hExec) (suppliedExecutor_prefixMax hScalar)
    (prefixMax_monotone profile) (prefixMax_polylog hp)
  exact ⟨program,d,C,p,hprogram,hcost.trans flight_bigO_shifted⟩

/-- The manuscript's concrete logarithmic expression needs no additional
analytic premise. The existence of its fast paid executors is still open. -/
theorem executeOne_paperProfile {profile : ℕ → ℕ}
    (hExec : SuppliedTensorExecutor sc parentRoot .left false profile)
    (hScalar : SuppliedTensorExecutor sc parentRoot .scalar false profile)
    (hp : (fun k : ℕ => (profile k : ℝ)+1) =O[atTop] paperTensorPrice) :
    ∃ (program : Prog false dftInKind dftOutKind) (d C p : ℕ),
      (∀ (n : ℕ), 0<n → ∀ x : Vec n,
        (run program (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
          (⟨n,dft n x⟩ : Tape ℂ)
          (C*(OriginalAllLengthSubstitution.fairwind (prefixMax profile) d n+1)) ((n+2)^p)) ∧
      (fun n : ℕ =>
        ((C*(OriginalAllLengthSubstitution.fairwind (prefixMax profile) d n+1) : ℕ) : ℝ))
        =O[atTop] (fun n : ℕ => (n : ℝ)*Real.sqrt (Real.log ((n : ℝ)+2))) :=
  executeOne_polylog hExec hScalar (polylogProfile_of_paper_bound hp)

end
end FourierSchur.OriginalPolylogExecutor
