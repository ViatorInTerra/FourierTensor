import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-
Compatibility with mathlib 4.29.1 for the two later prime-counting interfaces
used by the pinned OpenAI uniform Fourier compiler.

Provenance: references/openai_uniform_fourier/modern_PrimeCounting.lean
(Bolton Bailey, Ralf Stephan, Apache 2.0) supplies the cardinality interface;
references/openai_uniform_fourier/modern_Chebyshev.lean
(Alastair Irving, Terry Tao, Ruben Van de Velde, Apache 2.0) supplies pi_ge.
The immutable official Chebyshev source is mathlib4 commit
29c53517cf8e316f02ecadf525b142c15f8eb386:
https://github.com/leanprover-community/mathlib4/blob/29c53517cf8e316f02ecadf525b142c15f8eb386/Mathlib/NumberTheory/Chebyshev.lean
The proof below uses their binomial-factorization argument directly with the
prime-power product, avoiding the newer lcmUpto and Chebyshev-psi API.
-/

namespace Nat

def primesLE (n : ℕ) : Finset ℕ := primesBelow (n+1)

@[simp] theorem primesLE_card_eq_primeCounting (n : ℕ) :
    (primesLE n).card = primeCounting n := by
  exact primesBelow_card_eq_primeCounting' (n+1)

end Nat

namespace PrimeCountingCompatibility
open Finset
noncomputable section

def primeProduct (n : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE n, p^(Nat.log p n)

theorem primeProduct_pos (n : ℕ) : 0 < primeProduct n := by
  unfold primeProduct
  apply Finset.prod_pos
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact pow_pos hprime.pos _

theorem choose_dvd_primeProduct {n k : ℕ} (hk : k≤n) :
    n.choose k ∣ primeProduct n := by
  rw [← Nat.factorization_prime_le_iff_dvd
    (Nat.choose_ne_zero hk) (Nat.ne_of_gt (primeProduct_pos n))]
  intro p hp
  have hchoose := Nat.factorization_choose_le_log (n:=n) (k:=k) (p:=p)
  by_cases hpn : p≤n
  · have hmem : p ∈ Nat.primesLE n := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpn),hp⟩
    have hnonzero : ∀ q ∈ Nat.primesLE n, q^(Nat.log q n) ≠ 0 := by
      intro q hq
      have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
      exact pow_ne_zero _ hqprime.ne_zero
    change (n.choose k).factorization p ≤
      (∏ q ∈ Nat.primesLE n, q^(Nat.log q n)).factorization p
    rw [Nat.factorization_prod_apply hnonzero]
    refine hchoose.trans ?_
    calc
      Nat.log p n = (p^(Nat.log p n)).factorization p :=
        (Nat.factorization_pow_self hp).symm
      _ ≤ ∑ q ∈ Nat.primesLE n, (q^(Nat.log q n)).factorization p :=
        Finset.single_le_sum
          (f := fun q : Nat => (q^(Nat.log q n)).factorization p)
          (fun _ _ => Nat.zero_le _) hmem
  · have hlog : Nat.log p n=0 := Nat.log_of_lt (Nat.lt_of_not_ge hpn)
    rw [hlog] at hchoose
    rw [Nat.le_zero.mp hchoose]
    exact Nat.zero_le _

theorem two_pow_le_mul_primeProduct (n : ℕ) :
    2^n ≤ (n+1)*primeProduct n := by
  calc
    2^n = ∑ k ∈ Finset.range (n+1), n.choose k :=
      (Nat.sum_range_choose n).symm
    _ ≤ ∑ k ∈ Finset.range (n+1), primeProduct n := by
      apply Finset.sum_le_sum
      intro k hk
      exact Nat.le_of_dvd (primeProduct_pos n)
        (choose_dvd_primeProduct (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    _ = (n+1)*primeProduct n := by simp

theorem log_primeProduct_le (n : ℕ) :
    Real.log (primeProduct n) ≤ (Nat.primeCounting n:ℝ)*Real.log n := by
  by_cases hn : n=0
  · subst n
    simp [primeProduct,Nat.primesLE,Nat.primesBelow]
  have hnonzero : ∀ p ∈ Nat.primesLE n, (p^(Nat.log p n):ℝ) ≠ 0 := by
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact pow_ne_zero _ (by exact_mod_cast hprime.ne_zero)
  calc
    Real.log (primeProduct n) =
        ∑ p ∈ Nat.primesLE n, Real.log ((p:ℝ)^(Nat.log p n)) := by
      rw [primeProduct,Nat.cast_prod]
      simp only [Nat.cast_pow]
      exact Real.log_prod hnonzero
    _ ≤ ∑ _p ∈ Nat.primesLE n, Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hpPos : 0<(p:ℝ) := by exact_mod_cast hprime.pos
      apply Real.log_le_log (pow_pos hpPos _)
      exact_mod_cast Nat.pow_log_le_self p hn
    _ = (Nat.primeCounting n:ℝ)*Real.log n := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting]

theorem lower_numerator_le (n : ℕ) :
    (n:ℝ)*Real.log 2-Real.log ((n:ℝ)+1) ≤
      (Nat.primeCounting n:ℝ)*Real.log n := by
  have hprod := primeProduct_pos n
  have hlog : (n:ℝ)*Real.log 2 ≤
      Real.log ((n:ℝ)+1)+Real.log (primeProduct n) := by
    calc
      (n:ℝ)*Real.log 2 = Real.log ((2:ℝ)^n) := (Real.log_pow 2 n).symm
      _ ≤ Real.log (((n+1)*primeProduct n:ℕ):ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast two_pow_le_mul_primeProduct n
      _ = Real.log ((n:ℝ)+1)+Real.log (primeProduct n) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Real.log_mul (by positivity) (by exact_mod_cast Nat.ne_of_gt hprod)]
  linarith [log_primeProduct_le n]

end
end PrimeCountingCompatibility

namespace Chebyshev

/-- The exact later-mathlib Chebyshev lower bound, using the existing
binomial prime-factorization bound in mathlib 4.29.1. -/
theorem pi_ge (n : ℕ) :
    ((n:ℝ)*Real.log 2-Real.log ((n:ℝ)+1))/Real.log n ≤ Nat.primeCounting n := by
  rcases (show n=0 ∨ n=1 ∨ 1<n by omega) with rfl | rfl | hn
  · simp
  · simp
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast hn))).mpr
  exact PrimeCountingCompatibility.lower_numerator_le n

end Chebyshev
