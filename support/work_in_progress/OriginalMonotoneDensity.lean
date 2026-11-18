import work_in_progress.OriginalSectorSubstitution
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! Monotone majorants for complete tensor execution profiles.

The original all-length compiler needs a monotone natural profile, whereas
an independently supplied executor can have arbitrary finite exceptional
costs. Taking the maximum over the orders up to `k` supplies that monotonicity
and preserves every fixed logarithmic Big-O estimate. Transport only weakens
the work allowance of the same uniform RAM program; it constructs no faster
executor and leaves its supplied inputs, arbitrary-input semantics and
polynomial integer cap intact.
-/

namespace FourierSchur.OriginalMonotoneDensity

open Filter Asymptotics
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OriginalSectorSubstitution
noncomputable section

/-- The finite prefix includes order zero and the current order. -/
def prefixMax (profile : ℕ → ℕ) (k : ℕ) : ℕ :=
  (Finset.range (k+1)).sup profile

theorem le_prefixMax (profile : ℕ → ℕ) (k : ℕ) :
    profile k ≤ prefixMax profile k :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))

theorem prefixMax_monotone (profile : ℕ → ℕ) : Monotone (prefixMax profile) := by
  intro k l hkl
  exact Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hkl 1))

theorem prefixMax_eq_self {profile : ℕ → ℕ} (hmono : Monotone profile) (k : ℕ) :
    prefixMax profile k = profile k := by
  apply Nat.le_antisymm
  · exact Finset.sup_le (fun i hi => hmono (by
      have h := Finset.mem_range.mp hi
      omega))
  · exact le_prefixMax profile k

/-- A monotone real envelope keeps its constant under the finite maximum. -/
theorem prefixMax_bound (profile : ℕ → ℕ) (bound : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hmono : Monotone bound)
    (hbound : ∀ k, (profile k : ℝ)+1 ≤ C*bound k) (k : ℕ) :
    (prefixMax profile k : ℝ)+1 ≤ C*bound k := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup (Finset.range (k+1))
    ⟨0,Finset.mem_range.mpr (by omega)⟩ profile
  change (((Finset.range (k+1)).sup profile : ℕ) : ℝ)+1 ≤ _
  rw [hmax]
  exact (hbound i).trans (mul_le_mul_of_nonneg_left (hmono (by
    have h := Finset.mem_range.mp hi
    omega)) hC)

theorem log_order_pos (k : ℕ) : 0 < Real.log ((k : ℝ)+2) := by
  apply Real.log_pos
  have h := Nat.cast_nonneg (α := ℝ) k
  linarith

theorem log_power_monotone (a : ℕ) :
    Monotone (fun k : ℕ => Real.log ((k : ℝ)+2)^a) := by
  intro k l hkl
  apply pow_le_pow_left₀ (log_order_pos k).le
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 2)

theorem prefixMax_log_bound (profile : ℕ → ℕ) (a : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k, (profile k : ℝ)+1 ≤ C*Real.log ((k : ℝ)+2)^a) (k : ℕ) :
    (prefixMax profile k : ℝ)+1 ≤ C*Real.log ((k : ℝ)+2)^a :=
  prefixMax_bound profile _ C hC (log_power_monotone a) hbound k

/-- Eventual Big-O hypotheses include arbitrary finite exceptional orders.
The logarithmic denominator is positive even at order zero, so mathlib's
natural-atTop bound absorbs those exceptions into one finite constant. -/
theorem prefixMax_isBigO_log (profile : ℕ → ℕ) (a : ℕ)
    (h : (fun k : ℕ => (profile k : ℝ)+1) =O[atTop]
      (fun k => Real.log ((k : ℝ)+2)^a)) :
    (fun k : ℕ => (prefixMax profile k : ℝ)+1) =O[atTop]
      (fun k => Real.log ((k : ℝ)+2)^a) := by
  obtain ⟨C,hC,hbound⟩ := bound_of_isBigO_nat_atTop h
  have hall (k : ℕ) : (profile k : ℝ)+1 ≤ C*Real.log ((k : ℝ)+2)^a := by
    have H := hbound (x := k) (pow_pos (log_order_pos k) a).ne'
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (pow_nonneg (log_order_pos k).le a)] at H
    exact H
  refine IsBigO.of_bound C (Filter.Eventually.of_forall (fun k => ?_))
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (pow_nonneg (log_order_pos k).le a)]
  exact prefixMax_log_bound profile a C hC.le hall k

/-- Work-profile weakening uses the same complete uniform RAM executor. -/
theorem completeExecutor_mono {cl : Paint} {m : Bool} {profile bound : ℕ → ℕ}
    (h : CompleteTensorExecutor cl m profile) (hb : ∀ k, profile k ≤ bound k) :
    CompleteTensorExecutor cl m bound :=
  Can.mono h (fun i => Nat.mul_le_mul_left (2^i.1) (hb i.1))

theorem suppliedExecutor_mono {s : Ty} {table : ℕ → T s} {cl : Paint} {m : Bool}
    {profile bound : ℕ → ℕ} (h : SuppliedTensorExecutor s table cl m profile)
    (hb : ∀ k, profile k ≤ bound k) :
    SuppliedTensorExecutor s table cl m bound :=
  Can.mono h (fun i => Nat.mul_le_mul_left (2^i.1) (hb i.1))

theorem completeExecutor_prefixMax {cl : Paint} {m : Bool} {profile : ℕ → ℕ}
    (h : CompleteTensorExecutor cl m profile) :
    CompleteTensorExecutor cl m (prefixMax profile) :=
  completeExecutor_mono h (le_prefixMax profile)

theorem suppliedExecutor_prefixMax {s : Ty} {table : ℕ → T s} {cl : Paint} {m : Bool}
    {profile : ℕ → ℕ} (h : SuppliedTensorExecutor s table cl m profile) :
    SuppliedTensorExecutor s table cl m (prefixMax profile) :=
  suppliedExecutor_mono h (le_prefixMax profile)

end
end FourierSchur.OriginalMonotoneDensity
