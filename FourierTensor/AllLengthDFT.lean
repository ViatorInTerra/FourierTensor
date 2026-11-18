import FourierTensor.DFT.Program
import FourierTensor.DFT.ExactWork
import FourierTensor.DFT.Asymptotics

/-! One uniform pair of programs computes the root order and every output of
the positive-sign DFT. Its actual work depends only on the length. -/
namespace FourierTensor.AllLengthDFT

open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.PowerSaving.RAM.Bench OAI.PowerSaving.Selection OAI.PowerSaving.Skies
open Filter Asymptotics
noncomputable section

structure Implementation where
  order : Prog false w w
  solve : Prog false dftInKind dftOutKind
  orderBudget : Ration
  transformBudget : Ration
  correct : DFTProgram order solve (AllLengthProgram.compilerBill orderBudget transformBudget)
  order_spec : ∀ n : ℕ, 0<n →
    (run order n).val=receipt n ∧ (run order n).val<8*n^3

private theorem hasImplementation : Nonempty Implementation := by
  obtain ⟨o,s,a,b,h,r⟩ := AllLengthProgram.certificate
  exact ⟨⟨o,s,a,b,h,r⟩⟩

def implementation : Implementation := Classical.choice hasImplementation

/-- Includes the integer program, one canonical-root request, and the transform. -/
def exactTime : ℕ → ℕ := AllLengthExactWork.work implementation.order implementation.solve

def allowance : ℕ → ℕ := AllLengthProgram.compilerBill
  implementation.orderBudget implementation.transformBudget

theorem running_time (n : ℕ) (x : Vec n) :
    (run implementation.order n).work + 1 +
      (run implementation.solve
        (n,root (run implementation.order n).val,(⟨n,x⟩ : Tape ℂ))).work = exactTime n :=
  AllLengthExactWork.work_eq _ _ _ _

/-- Evaluate the exact count from the length using integer instructions and
tape operations alone. The scalar arithmetic and the root are unnecessary. -/
theorem count_from_length (n : ℕ) : exactTime n =
    AllLengthExactWork.count implementation.order implementation.solve n :=
  AllLengthExactWork.work_eq_count _ _ n

theorem time_le_allowance (n : ℕ) (hn : 0<n) : exactTime n ≤ allowance n :=
  AllLengthExactWork.work_le_of_contract implementation.correct n hn

theorem allowance_bigO : (fun n => (allowance n:ℝ)) =O[atTop] AllLengthAsymptotics.rate := by
  let a := implementation.orderBudget
  let b := implementation.transformBudget
  refine IsBigO.trans (g := fun n => ((AllLengthProgram.transformBound (a.d+b.d) n+1:ℕ):ℝ))
    (isBigO_iff.mpr ⟨((a.c+b.c+1:ℕ):ℝ),Filter.Eventually.of_forall (fun n => ?_)⟩)
    (AllLengthAsymptotics.wind_bigO _)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast AllLengthProgram.compilerBill_le_fairwind a b n

theorem time_bigO : (fun n => (exactTime n:ℝ)) =O[atTop] AllLengthAsymptotics.rate := by
  apply IsBigO.trans _ allowance_bigO
  refine isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [one_mul,Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast time_le_allowance n hn

/-- Valid at each positive length, including every length on the direct branch. -/
theorem every_length_bound : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 0<n →
    (exactTime n:ℝ) ≤ C*AllLengthAsymptotics.guardedRate n :=
  AllLengthAsymptotics.uniformize _ time_bigO

/-- The native output, canonical root, validity, work and word caps and
pointwise mixed-logarithm estimate concern the same fixed program pair. -/
theorem guarantee :
    DFTProgram implementation.order implementation.solve exactTime ∧
    (∀ n : ℕ, 0<n → (run implementation.order n).val=receipt n ∧
      (run implementation.order n).val<8*n^3) ∧
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 0<n →
      (exactTime n:ℝ) ≤ C*AllLengthAsymptotics.guardedRate n :=
  ⟨AllLengthExactWork.exact_contract implementation.correct,implementation.order_spec,
    every_length_bound⟩

theorem below_published_bound : (fun n => (exactTime n:ℝ)) =o[atTop] paperTime :=
  time_bigO.trans_isLittleO AllLengthAsymptotics.rate_little_paper

theorem below_nlogn : (fun n => (exactTime n:ℝ)) =o[atTop] nlogn := by
  have h : speed 1 = nlogn := funext fun n => by
    rw [speed, Real.rpow_one]
    rfl
  rw [← h]
  exact time_bigO.trans_isLittleO
    (AllLengthAsymptotics.rate_little_speed CenterCacheRate.exponents_pos_lt.2)

theorem published_exponent_saving :
    142420.49 < (1-CenterCacheRate.exponent)/(1-theta) ∧
    (1-CenterCacheRate.exponent)/(1-theta) < 142420.50 :=
  CachedExecutor.saving_ratio

theorem upstream_lean_exponent_saving : (1-CenterCacheRate.exponent)/(1-alpha) = 1500 := by
  norm_num [CenterCacheRate.exponent,CenterCacheRate.epsilon,alpha]

end
end FourierTensor.AllLengthDFT
