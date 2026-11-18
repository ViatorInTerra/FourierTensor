import FourierTensor.Tensor.CenterCache.Rate
import work_in_progress.OriginalGroupedCensusBridge

/-! # Callback census for the three center-cache stages

An arbitrary function on ranks prices the changed invocation. A point-mass
price extracts a single callback count, while the recurrence uses a power
price. Each stage has one invocation for each member of its own `Other j`.
-/

namespace FourierTensor.CenterCacheCensus

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster
open FourierSchur FourierSchur.OriginalGroupedResidualCertificate
open FourierSchur.OriginalGroupedFrameBudget
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def invocationCost (j : J) (c : ℕ → ℝ) : ℝ :=
  OriginalGroupedCensusBridge.invocationCost j c - 36 * c 32

open OriginalGroupedCensusBridge in
def shortenedCost (j : J) (c : ℕ → ℝ) : ℝ :=
  frameCost (bp j) (b0 j) c + frameCost (b0 j) (b1 j) c +
  frameCost (b1 j) (b2 j) c + frameCost (b2 j) (b4 j) c +
  frameCost (b4 j) (b5 j) c + frameCost (b5 j) (b6 j) c +
  frameCost (b6 j) (b7 j) c + frameCost (b7 j) (bend j) c

def nativeCost (c : ℕ → ℝ) : ℝ :=
  (Fintype.card (Other (0 : J)) : ℝ) * invocationCost 0 c +
  (Fintype.card (Other (1 : J)) : ℝ) * invocationCost 1 c +
  (Fintype.card (Other (2 : J)) : ℝ) * invocationCost 2 c +
  OriginalGroupedCensusBridge.frameCost (border 3) sink c

theorem center_rank (j : J) : OriginalGroupedMaskCards.stageRanks j 3 = 32 := by
  rw [OriginalGroupedMaskCards.stageRanks_eq]
  rfl

theorem belt_big (j : J) : changeSize (belt j) (big j) = 32 := by
  have hbb : belt j ⊆ big j := by
    intro x hx
    exact (in_big j x).mpr ((in_belt j x).mp hx).1
  rw [OriginalGroupedCensusBridge.changeSize_of_subset hbb, ← center_rank j]
  exact (Finset.card_sdiff_of_subset hbb).symm

theorem shortenedCost_add_free (j : J) (c : ℕ → ℝ) (hc : c 0 = 0) :
    shortenedCost j c + 30 * c 32 = invocationCost j c := by
  have hrev : changeSize (big j) (belt j) = 32 := by
    rw [OriginalGroupedCensusBridge.changeSize_symm, belt_big]
  have h : OriginalGroupedCensusBridge.frameCost (b2 j) (b3 j) c +
      OriginalGroupedCensusBridge.frameCost (b3 j) (b4 j) c =
      OriginalGroupedCensusBridge.frameCost (b2 j) (b4 j) c + 66 * c 32 := by
    simp only [b2, b3, b4, OriginalGroupedCensusBridge.stamp_cost,
      OriginalGroupedCensusBridge.changeSize_self, belt_big, hrev, hc]
    ring
  unfold shortenedCost invocationCost OriginalGroupedCensusBridge.invocationCost
  linarith only [h]

theorem invocationCost_eq (j : J) (c : ℕ → ℝ) (hc : c 0 = 0) :
    invocationCost j c =
      8120*c (OriginalGroupedMaskCards.stageRanks j 0) +
      8120*c (OriginalGroupedMaskCards.stageRanks j 1) +
      33*c (OriginalGroupedMaskCards.stageRanks j 2) +
      63*c 32 +
      33*c (OriginalGroupedMaskCards.stageRanks j 4) +
      12204360*(c (OriginalGroupedMaskCards.stageRanks j 5) +
        c (OriginalGroupedMaskCards.stageRanks j 6) +
        c (OriginalGroupedMaskCards.stageRanks j 7) +
        c (OriginalGroupedMaskCards.stageRanks j 8) +
        c (OriginalGroupedMaskCards.stageRanks j 9)) +
      4279240*c 32768 := by
  rw [invocationCost, OriginalGroupedCensusBridge.invocationCost_eq j c hc, center_rank]
  ring

theorem nativeCost_sub (c : ℕ → ℝ) :
    nativeCost c = OriginalGroupedCensusBridge.nativeCost c -
      (CenterCacheRate.eliminatedCalls : ℝ) * c 32 := by
  unfold nativeCost OriginalGroupedCensusBridge.nativeCost invocationCost
  simp only [card_other]
  norm_num [CenterCacheRate.eliminatedCalls, CenterCacheRate.invocations,
    CenterCacheRate.savedPerInvocation]
  ring

private theorem vec10 (a b c d e f g h k l : ℕ) (i : Fin 10) :
    ![a,b,c,d,e,f,g,h,k,l] i =
      match i.val with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f
      | 6 => g | 7 => h | 8 => k | _ => l := by
  fin_cases i <;> rfl

theorem rank32_invocation (j : J) :
    invocationCost j (fun r => if r = 32 then 1 else 0) = 63 := by
  rw [invocationCost_eq j _ (by norm_num)]
  fin_cases j <;> norm_num [OriginalGroupedMaskCards.stageRanks_eq, edgeRank, vec10]

theorem nativeCost_histogram (c : ℕ → ℝ) (hc : c 0 = 0) :
    nativeCost c =
      ((padded32 - roles32 : ℕ) : ℝ) * c order32 +
      ∑ i, (CenterCacheRate.count i : ℝ) * c (rho32 i) := by
  unfold nativeCost
  rw [invocationCost_eq 0 c hc, invocationCost_eq 1 c hc,
    invocationCost_eq 2 c hc, OriginalGroupedCensusBridge.closing_cost c hc]
  simp only [card_other, OriginalGroupedCensusBridge.card_spare,
    OriginalGroupedMaskCards.stageRanks_eq]
  norm_num [edgeRank, vec10, CenterCacheRate.count, count32, rho32, order32,
    padded32, roles32, Fin.sum_univ_succ, hc]
  ring

/-- Counting the pairs (emitted instruction, physical row) at a retained
rank recovers its integer multiplicity. -/
theorem word_rank_count {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (p : OriginalGroupedFrameWords.Word Blocks ρ)
    (hw : ∀ c : ℕ → ℝ, c 0 = 0 → OriginalGroupedCensusBridge.wordCost p c = nativeCost c)
    (i : Fin 12) :
    (Finset.univ.filter (fun q : OriginalGroupedWordProfile.Kind p =>
      OriginalGroupedWordProfile.rank p q = rho32 i)).card = CenterCacheRate.count i := by
  classical
  let c (r : ℕ) : ℝ := if r = rho32 i then 1 else 0
  have hc : c 0 = 0 := if_neg (Nat.ne_of_lt (ranges32 i).1)
  have ho : c order32 = 0 := if_neg (Nat.ne_of_gt (ranges32 i).2.1)
  have h := hw c hc
  rw [OriginalGroupedCensusBridge.wordCost_eq p c hc, nativeCost_histogram c hc,
    ho, mul_zero, zero_add, Finset.sum_eq_single i] at h
  · simp only [c, if_pos rfl, mul_one] at h
    rw [Finset.card_filter]
    exact_mod_cast h
  · intro j _ hji
    have hij : rho32 j ≠ rho32 i := fun he => hji (OriginalGroupedNativeInventory.rho32_injective he)
    simp only [c, if_neg hij, mul_zero]
  · simp

theorem nativeCost_moment_eq (z : ℝ) :
    nativeCost (OriginalGroupedCensusBridge.momentCost 32768 50 z) =
      CenterCacheRate.paddedMoment z := by
  rw [nativeCost_histogram _ (by simp [OriginalGroupedCensusBridge.momentCost])]
  have h (i : Fin 12) : rho32 i ≠ 0 := Nat.ne_of_gt (ranges32 i).1
  simp only [OriginalGroupedCensusBridge.momentCost, if_neg (h _),
    CenterCacheRate.paddedMoment, CenterCacheRate.paddedWeight, moment, point32]
  congr 1
  · norm_num [padded32, roles32, order32, padding32]
  · apply Finset.sum_congr rfl
    intro i _
    unfold padded32 order32
    norm_num
    ring

/-- A witness word with this arbitrary-price census has the contracting
moment used by the RAM compiler, even if its role space includes scratch. -/
theorem word_moment_lt {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (p : OriginalGroupedFrameWords.Word Blocks ρ)
    (h : ∀ c : ℕ → ℝ, c 0 = 0 → OriginalGroupedCensusBridge.wordCost p c = nativeCost c) :
    OriginalGroupedWordProfile.moment p mcol 50 CenterCacheRate.exponent < 1 := by
  rw [OriginalGroupedCensusBridge.moment_eq_wordCost, h _ (by simp [OriginalGroupedCensusBridge.momentCost])]
  exact (nativeCost_moment_eq CenterCacheRate.exponent).trans_lt CenterCacheRate.padded_moment_lt_one

end
end FourierTensor.CenterCacheCensus
