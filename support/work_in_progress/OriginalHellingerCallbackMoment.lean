import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A finite Hellinger / fractional-moment lift for the PAID callback ledger.
Weights include every independent bank and spectator. They need not sum to
one. The identity isolates precisely the strict reserve required by the
square-root recurrence. No input-energy bound is substituted for a bank bill.
-/
namespace FourierSchur.OriginalHellingerCallbackMoment
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

def mass (w : ι → ℝ) : ℝ := ∑ i, w i

def orderMass (w rho : ι → ℝ) : ℝ := ∑ i, w i * rho i

def moment (w rho : ι → ℝ) : ℝ := ∑ i, w i * Real.sqrt (rho i)

def defect (w rho : ι → ℝ) : ℝ :=
  ∑ i, w i * (1 - Real.sqrt (rho i)) ^ 2

theorem defect_nonneg (w rho : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ defect w rho :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem defect_identity (w rho : ι → ℝ) (hr : ∀ i, 0 ≤ rho i) :
    defect w rho = mass w + orderMass w rho - 2 * moment w rho := by
  unfold defect mass orderMass moment
  calc
    _ = ∑ i, (w i + w i * rho i - 2 * (w i * Real.sqrt (rho i))) := by
      apply Finset.sum_congr rfl
      intro i _
      have h : (1 - Real.sqrt (rho i)) ^ 2 = 1 + rho i - 2 * Real.sqrt (rho i) := by
        nlinarith [Real.sq_sqrt (hr i)]
      rw [h]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem moment_identity (w rho : ι → ℝ) (hr : ∀ i, 0 ≤ rho i) :
    moment w rho = (mass w + orderMass w rho - defect w rho) / 2 := by
  rw [defect_identity w rho hr]
  ring

/-- Strict reserve is a strict Hellinger gain above the entire excess
of paid bank mass and paid order mass. -/
theorem strict_moment_iff (w rho : ι → ℝ) (hr : ∀ i, 0 ≤ rho i) :
    moment w rho < 1 ↔ mass w + orderMass w rho - 2 < defect w rho := by
  rw [moment_identity w rho hr]
  constructor <;> intro h <;> linarith

theorem moment_margin (w rho : ι → ℝ) (epsilon : ℝ)
    (hr : ∀ i, 0 ≤ rho i)
    (hg : mass w + orderMass w rho - 2 + 2 * epsilon ≤ defect w rho) :
    moment w rho ≤ 1 - epsilon := by
  rw [moment_identity w rho hr]
  linarith

/-- A subprobability ownership ledger and subprobability order ledger
contract strictly as soon as their actual Hellinger defect is positive. -/
theorem strict_of_subprobability (w rho : ι → ℝ)
    (hr : ∀ i, 0 ≤ rho i) (ha : mass w ≤ 1)
    (hb : orderMass w rho ≤ 1) (hh : 0 < defect w rho) :
    moment w rho < 1 := by
  apply (strict_moment_iff w rho hr).2
  linarith

def affinity (mu nu : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (mu i) * Real.sqrt (nu i)

def hellinger (mu nu : ι → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (mu i) - Real.sqrt (nu i)) ^ 2

/-- The Fourier-executor moment is literally an unnormalized Hellinger
affinity of two positive physical ledgers, not just an analogy. -/
theorem affinity_eq_moment (w rho : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    affinity w (fun i => w i * rho i) = moment w rho := by
  unfold affinity moment
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.sqrt_mul (hw i)]
  calc
    _ = (Real.sqrt (w i)) ^ 2 * Real.sqrt (rho i) := by ring
    _ = _ := by rw [Real.sq_sqrt (hw i)]

theorem hellinger_identity (mu nu : ι → ℝ)
    (hm : ∀ i, 0 ≤ mu i) (hn : ∀ i, 0 ≤ nu i) :
    hellinger mu nu = mass mu + mass nu - 2 * affinity mu nu := by
  unfold hellinger mass affinity
  calc
    _ = ∑ i, (mu i + nu i - 2 * (Real.sqrt (mu i) * Real.sqrt (nu i))) := by
      apply Finset.sum_congr rfl
      intro i _
      nlinarith [Real.sq_sqrt (hm i), Real.sq_sqrt (hn i)]
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem affinity_le_root_product (mu nu : ι → ℝ)
    (hm : ∀ i, 0 ≤ mu i) (hn : ∀ i, 0 ≤ nu i) :
    affinity mu nu ≤ Real.sqrt (mass mu * mass nu) := by
  have H := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => Real.sqrt (mu i)) (fun i => Real.sqrt (nu i))
  have hms : (∑ i, Real.sqrt (mu i) ^ 2) = mass mu :=
    Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hm i))
  have hns : (∑ i, Real.sqrt (nu i) ^ 2) = mass nu :=
    Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hn i))
  rw [hms, hns] at H
  exact Real.le_sqrt_of_sq_le H

/-- Data processing in the direction needed for a coherent refinement:
splitting both positive ledgers increases their Hellinger potential.
Using this on a circuit requires genuine physical child-ledger sums. -/
theorem refinement_increases_hellinger (mu nu : ι → ℝ)
    (hm : ∀ i, 0 ≤ mu i) (hn : ∀ i, 0 ≤ nu i) :
    (Real.sqrt (mass mu) - Real.sqrt (mass nu)) ^ 2 ≤ hellinger mu nu := by
  have hm0 : 0 ≤ mass mu := Finset.sum_nonneg (fun i _ => hm i)
  have hn0 : 0 ≤ mass nu := Finset.sum_nonneg (fun i _ => hn i)
  have H := affinity_le_root_product mu nu hm hn
  rw [Real.sqrt_mul hm0] at H
  rw [hellinger_identity mu nu hm hn]
  nlinarith [Real.sq_sqrt hm0, Real.sq_sqrt hn0]

theorem callback_defect_is_hellinger (w rho : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ rho i) :
    defect w rho = hellinger w (fun i => w i * rho i) := by
  rw [hellinger_identity _ _ hw (fun i => mul_nonneg (hw i) (hr i)),
    affinity_eq_moment w rho hw, defect_identity w rho hr]
  rfl

/-- The exact present callback histogram, including all original banks.
This is a statement about this inventory, not a circuit lower bound. -/
def currentMoment : ℝ :=
  ((1960 : ℝ) + 88 * Real.sqrt (215 / 216 : ℝ) +
    91 * Real.sqrt (1 / 216 : ℝ)) / 2048

theorem current_moment_above_one : 1 < currentMoment := by
  have h1 : (997 / 1000 : ℝ) ≤ Real.sqrt (215 / 216 : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have h2 : (68 / 1000 : ℝ) ≤ Real.sqrt (1 / 216 : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  unfold currentMoment
  linarith

/-- A concrete target for a new, semantics-preserving shared-block rewrite.
This theorem does not assert that the six-call saving has been constructed. -/
theorem six_full_callback_gain_suffices :
    currentMoment - (6 / 2048 : ℝ) ≤ 1 - (1 / 200000 : ℝ) := by
  have h1 : Real.sqrt (215 / 216 : ℝ) ≤ (997683 / 1000000 : ℝ) := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 997683 / 1000000)).2
    norm_num
  have h2 : Real.sqrt (1 / 216 : ℝ) ≤ (68042 / 1000000 : ℝ) := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 68042 / 1000000)).2
    norm_num
  unfold currentMoment
  linarith

end
end FourierSchur.OriginalHellingerCallbackMoment
