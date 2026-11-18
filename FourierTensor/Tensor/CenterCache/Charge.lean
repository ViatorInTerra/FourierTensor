import FourierTensor.Tensor.CenterCache.Census

/-!
# Physical callback multiplicities

Grouping the emitted instruction/row pairs by rank preserves the native
child charge for every parent order and every price on child orders.
Consequently the two presentations of the recursive allowance agree
exactly, including below the cutoff.
-/

namespace FourierTensor.CenterCacheCharge
open FourierSchur OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster
open OriginalGroupedRecursionRAM OriginalGroupedWordProfile
open OriginalGroupedCensusBridge OriginalGroupedResidualCertificate
open scoped BigOperators
noncomputable section

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (P : OriginalGroupedFrameWords.Word Blocks ρ)
    (H : ∀ c : ℕ → ℝ, c 0 = 0 → wordCost P c = CenterCacheCensus.nativeCost c)

include H

private theorem rank_sum_eq (g : ℕ → ℕ) :
    (∑ q : Kind P, weight P q * g (rank P q)) =
      ∑ i, CenterCacheRate.multiplicity i * g (CenterCacheRate.rank i) := by
  let c : ℕ → ℝ := fun t => if t = 0 then 0 else (g t : ℝ)
  have hc : c 0 = 0 := by simp [c]
  have h := (wordCost_eq P c hc).symm.trans
    ((H c hc).trans (CenterCacheCensus.nativeCost_histogram c hc))
  have hw (q : Kind P) : c (rank P q) = ((weight P q * g (rank P q) : ℕ) : ℝ) := by
    by_cases hr : rank P q = 0 <;> simp [c, weight, hr]
  have hp : (∑ i, (CenterCacheRate.multiplicity i : ℝ) * c (CenterCacheRate.rank i)) =
      ((padded32 - roles32 : ℕ) : ℝ) * c order32 +
        ∑ i, (CenterCacheRate.count i : ℝ) * c (rho32 i) := by
    rw [Fintype.sum_option]
    rfl
  have hn (i : Option (Fin 12)) :
      (CenterCacheRate.multiplicity i : ℝ) * c (CenterCacheRate.rank i) =
        ((CenterCacheRate.multiplicity i * g (CenterCacheRate.rank i) : ℕ) : ℝ) := by
    simp [c, Nat.ne_of_gt (CenterCacheRate.rank_positive i)]
  rw [← hp] at h
  simp_rw [hw, hn] at h
  exact_mod_cast h

theorem childCharge_eq (k : ℕ) (τ : ℕ → ℕ) :
    childCharge (scheme P 50 (by decide)) k τ = childCharge CenterCacheRate.scheme k τ := by
  have hu : Fintype.card Blocks = order32 := card_block.trans (by decide)
  unfold childCharge scheme CenterCacheRate.scheme
  simp only [groupedScheme, hu]
  by_cases hk : 50 + order32 ≤ k
  · simp only [hk, if_true, Nat.mul_assoc]
    exact rank_sum_eq P H (fun r => 2 ^ (k - 50 - r * ((k - 50) / order32)) *
      τ (r * ((k - 50) / order32)))
  · simp [hk]

theorem allowance_eq (k : ℕ) :
    allowance (scheme P 50 (by decide)) k = allowance CenterCacheRate.scheme k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [OriginalGroupedRecursionRAM.allowance_eq, OriginalGroupedRecursionRAM.allowance_eq
      CenterCacheRate.scheme k, childCharge_eq P H]
    apply congrArg (fun a : ℕ => 2 ^ k + a)
    unfold childCharge
    apply Finset.sum_congr rfl
    intro t _
    by_cases hzero : CenterCacheRate.scheme.count k t = 0
    · simp [hzero]
    · rw [ih _ (CenterCacheRate.scheme.decreases k t (Nat.pos_of_ne_zero hzero))]

omit H in
/-- Pricing just the children of order `d*f` counts the physical spectator
copies of each positive rank-`d` instruction. -/
theorem physical_count (X : Layout Blocks) (r f d : ℕ) (hf : 0 < f) (hd : 0 < d) :
    OriginalGroupedWordRAM.wordCharge X r f (fun k => if k = d*f then 1 else 0) P =
      (Finset.univ.filter (fun q : Kind P => rank P q = d)).card *
        2 ^ (r + (X.n - d) * f) := by
  let τ := fun k : ℕ => if k = d*f then 1 else 0
  let v := 2 ^ (r + (X.n - d) * f)
  have hm (j : Fin P.length) :
      OriginalGroupedWordRAM.moveCharge X r f τ (P.get j) =
        ∑ l : ρ, if rank P (j,l) = d then v else 0 := by
    rw [moveCharge_eq]
    apply Finset.sum_congr rfl
    intro l _
    let t := rank P (j,l)
    change (if t = 0 then 0 else 2 ^ (r + (X.n - t) * f) * τ (t*f)) =
      if t = d then v else 0
    by_cases ht : t = d
    · simp [ht, τ, v, Nat.ne_of_gt hd]
    · have htf : t*f ≠ d*f := fun eq => ht (Nat.eq_of_mul_eq_mul_right hf eq)
      simp [τ, ht, htf]
  have ha : OriginalGroupedWordRAM.wordCharge X r f τ P =
      ∑ j : Fin P.length, OriginalGroupedWordRAM.moveCharge X r f τ (P.get j) := by
    symm
    rw [← Fin.sum_ofFn, List.ofFn_comp', List.ofFn_get]
    rfl
  rw [ha]
  simp_rw [hm]
  rw [← Fintype.sum_prod_type (fun q : Fin P.length × ρ => if rank P q = d then v else 0)]
  simp [Finset.sum_ite, v]
  rfl

end
end FourierTensor.CenterCacheCharge
