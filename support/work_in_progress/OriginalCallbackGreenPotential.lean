import work_in_progress.OriginalContextualNativeTapeCensus
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
Finite Green potentials for *paid* callback types. A matrix entry is the
full spectator-expanded width times the square-root order ratio of the
corresponding child type. It is not a probability or an input norm.

The growth-versus-capacity contradiction is proved here, including its
finite dual witness. This does not supply a new physical typed executor:
each row of such an executor and its charged recurrence remain obligations.
The last section instantiates growth for the existing verified inventory.
-/
namespace FourierSchur.OriginalCallbackGreenPotential
open scoped BigOperators
noncomputable section

variable {S : Type*} [Fintype S]

def transfer (P : S → S → ℝ) (h : S → ℝ) (s : S) : ℝ :=
  ∑ t, P s t * h t

def green (P : S → S → ℝ) (cost : S → ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | n+1, s => cost s + transfer P (green P cost n) s

theorem transfer_mono (P : S → S → ℝ) (hP : ∀ s t, 0 ≤ P s t)
    (a b : S → ℝ) (hab : ∀ s, a s ≤ b s) (s : S) :
    transfer P a s ≤ transfer P b s :=
  Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hab t) (hP s t))

theorem green_nonneg (P : S → S → ℝ) (cost : S → ℝ)
    (hP : ∀ s t, 0 ≤ P s t) (hc : ∀ s, 0 ≤ cost s) (n : ℕ) (s : S) :
    0 ≤ green P cost n s := by
  induction n generalizing s with
  | zero => exact le_refl _
  | succ n ih =>
    exact add_nonneg (hc s) (Finset.sum_nonneg
      (fun t _ => mul_nonneg (hP s t) (ih t)))

/-- A finite capacity for every complete depth follows from a positive
supersolution of the *same* paid transfer equation. -/
theorem green_le_capacity (P : S → S → ℝ) (cost h : S → ℝ)
    (hP : ∀ s t, 0 ≤ P s t) (h0 : ∀ s, 0 ≤ h s)
    (hgain : ∀ s, cost s + transfer P h s ≤ h s) (n : ℕ) (s : S) :
    green P cost n s ≤ h s := by
  induction n generalizing s with
  | zero => exact h0 s
  | succ n ih =>
    change cost s + transfer P (green P cost n) s ≤ h s
    have H := transfer_mono P hP _ h ih s
    linarith [hgain s]

/-- An actual charged recursive ledger is bounded only after its physical
recurrence has been proved. Initialization, routing and control belong to
`cost`; child fees, with all spectators, belong to `P`. -/
theorem paid_work_le_green (P : S → S → ℝ) (cost : S → ℝ)
    (work : ℕ → S → ℝ) (hP : ∀ s t, 0 ≤ P s t)
    (hbase : ∀ s, work 0 s ≤ 0)
    (hstep : ∀ n s, work (n+1) s ≤ cost s + transfer P (work n) s)
    (n : ℕ) (s : S) : work n s ≤ green P cost n s := by
  induction n generalizing s with
  | zero => exact hbase s
  | succ n ih =>
    change work (n+1) s ≤ cost s + transfer P (green P cost n) s
    have H := transfer_mono P hP _ _ ih s
    linarith [hstep n s]

theorem first_excess_impossible (P : S → S → ℝ) (cost h : S → ℝ)
    (work : ℕ → S → ℝ) (hP : ∀ s t, 0 ≤ P s t) (h0 : ∀ s, 0 ≤ h s)
    (hgain : ∀ s, cost s + transfer P h s ≤ h s)
    (hbase : ∀ s, work 0 s ≤ 0)
    (hstep : ∀ n s, work (n+1) s ≤ cost s + transfer P (work n) s)
    (n : ℕ) (s : S) : ¬ h s < work n s := by
  exact not_lt_of_ge ((paid_work_le_green P cost work hP hbase hstep n s).trans
    (green_le_capacity P cost h hP h0 hgain n s))

/-- A bounded unit-source Green potential gives a uniform strict reserve,
even if an individual unweighted row sum of `P` exceeds one. -/
theorem capacity_gives_strict_reserve (P : S → S → ℝ) (h : S → ℝ) (B : ℝ)
    (hB : 0 < B) (hcap : ∀ s, h s ≤ B)
    (hgain : ∀ s, 1 + transfer P h s ≤ h s) (s : S) :
    transfer P h s ≤ (1 - 1/B) * h s := by
  have hd : h s / B ≤ 1 := (div_le_one hB).2 (hcap s)
  have he : (1 - 1/B) * h s = h s - h s/B := by ring
  rw [he]
  linarith [hgain s]

theorem source_forces_positive_capacity (P : S → S → ℝ) (h : S → ℝ)
    (hP : ∀ s t, 0 ≤ P s t) (h0 : ∀ s, 0 ≤ h s)
    (hgain : ∀ s, 1 + transfer P h s ≤ h s) (s : S) : 1 ≤ h s := by
  have hp : 0 ≤ transfer P h s := Finset.sum_nonneg
    (fun t _ => mul_nonneg (hP s t) (h0 t))
  linarith [hgain s]

/-- The dual divergence witness: a nonzero nonnegative incoming flow that
does not decrease under transfer rules out any finite positive unit-source
potential. This is a finite algebraic contradiction, with no limit theorem. -/
theorem dual_divergence_contradiction (P : S → S → ℝ) (z h : S → ℝ)
    (hz : ∀ s, 0 ≤ z s) (hzpos : 0 < ∑ s, z s) (h0 : ∀ s, 0 ≤ h s)
    (hin : ∀ t, z t ≤ ∑ s, z s * P s t)
    (hgain : ∀ s, 1 + transfer P h s ≤ h s) : False := by
  have hrow : (∑ s, z s * (1 + transfer P h s)) ≤ ∑ s, z s * h s :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hgain s) (hz s))
  have hcol : (∑ t, z t * h t) ≤ ∑ t, (∑ s, z s * P s t) * h t :=
    Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_right (hin t) (h0 t))
  have he : (∑ s, z s * (1 + transfer P h s)) =
      (∑ s, z s) + ∑ t, (∑ s, z s * P s t) * h t := by
    simp only [transfer, mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he] at hrow
  linarith

/-- Scalar Green truncation, useful for checking a one-type inventory. -/
def scalarGreen (m : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 1 + m * scalarGreen m n

theorem scalar_green_nonneg (m : ℝ) (hm : 0 ≤ m) (n : ℕ) :
    0 ≤ scalarGreen m n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact add_nonneg (show (0:ℝ) ≤ 1 by norm_num) (mul_nonneg hm ih)

theorem scalar_green_linear_growth (m : ℝ) (hm : 1 ≤ m) (n : ℕ) :
    (n : ℝ) ≤ scalarGreen m n := by
  induction n with
  | zero => norm_num [scalarGreen]
  | succ n ih =>
    have hp := scalar_green_nonneg m (zero_le_one.trans hm) n
    simp only [scalarGreen, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Positive excess yields quadratic accumulated growth before any passage
to a limit. No paid generation has been removed at a stopping line. -/
theorem scalar_green_quadratic_growth (m delta : ℝ) (hd : 0 ≤ delta)
    (hm : 1+delta ≤ m) (n : ℕ) :
    (n : ℝ) + delta * (n : ℝ) * ((n : ℝ)-1)/2 ≤ scalarGreen m n := by
  induction n with
  | zero => simp [scalarGreen]
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hl := scalar_green_linear_growth m (by linarith) n
    have hp := scalar_green_nonneg m (by linarith) n
    have hmul : (1+delta) * scalarGreen m n ≤ m * scalarGreen m n :=
      mul_le_mul_of_nonneg_right hm hp
    have hdelta : delta * (n : ℝ) ≤ delta * scalarGreen m n :=
      mul_le_mul_of_nonneg_left hl hd
    simp only [scalarGreen, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem scalar_green_no_uniform_capacity (m B : ℝ) (hm : 1 ≤ m) :
    ∃ n, B < scalarGreen m n := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact ⟨n, hn.trans_le (scalar_green_linear_growth m hm n)⟩

section VerifiedInventory
open OriginalContextualNativeTapeCensus

/-- A conservative rational lower bound for the *actual* verified native
inventory. The complete original auxiliary and spectator bill is retained. -/
theorem native_moment_gap : 1 + (1/360:ℝ) ≤ programMoment := by
  have h1 : (997/1000:ℝ) ≤ Real.sqrt (215/216:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have h2 : (68/1000:ℝ) ≤ Real.sqrt (1/216:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  rw [program_moment_eq, actual_square_root_moment]
  unfold improvedMoment
  linarith

theorem native_green_growth (n : ℕ) :
    (n:ℝ) + (n:ℝ)*((n:ℝ)-1)/720 ≤ scalarGreen programMoment n := by
  have H := scalar_green_quadratic_growth programMoment (1/360:ℝ)
    (by norm_num) native_moment_gap n
  convert H using 1; ring

/-- Hence a finite uniform capacity for the unchanged inventory cannot be
the missing premise. A successful proof must change the physical sharing
or supply genuinely different, proved inherited callback types. -/
theorem native_no_uniform_green_capacity (B : ℝ) :
    ∃ n, B < scalarGreen programMoment n :=
  scalar_green_no_uniform_capacity programMoment B program_moment_above_one.le

end VerifiedInventory
end
end FourierSchur.OriginalCallbackGreenPotential
