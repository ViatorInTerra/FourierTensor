import FourierTensor.Tensor.CenterCache
import FourierTensor.Tensor.CenterCache.Census

/-! A native invocation with separate scratch for the rank-thirty center contribution. -/
namespace FourierTensor.CenterCacheWord

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.Cluster
open FourierSchur Matrix Finset
open OriginalGroupedFrameWords OriginalGroupedFrameBudget OriginalGroupedCensusBridge
open OriginalNativeCenterSharing OriginalLocalizedBankSharing
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def basis (j : J) (F : StartAxes) : Box ⊕ Free → OBase Blocks :=
  Sum.elim (basisBox j F) (fun _ => basisBox j F (bc (.inl ())))

def labels (s : Lab) : Box ⊕ Free → Mask := Sum.elim s (fun _ => ∅)

def applyOriginal (g : (Box → ℂ) → Box → ℂ) (x : Box ⊕ Free → ℂ) :
    Box ⊕ Free → ℂ := Sum.elim (g (x ∘ Sum.inl)) (fun _ => 0)

private theorem gateTo {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (A : ρ → OBase α) (s t : ρ → Finset α) (M : Matrix ρ ρ ℚ)
    (cond : ∀ i k, M i k ≠ 0 → frame (A i) (t i) = frame (A k) (s k)) :
    CPath A s t (actPoint M) (fun _ => 0) := by
  refine ⟨[.localM M], ?_, ?_⟩
  · intro c hc; simp [wordCost, moveCost]
  · intro f x
    funext r i
    change ∑ k, (M r k : ℂ) * (∑ a, (digitProd (fun _ : Fin f => frame (A k) (s k))) i a * x k a) =
      ∑ a, (digitProd (fun _ : Fin f => frame (A r) (t r))) i a * (∑ k, (M r k : ℂ) * x k a)
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro k _
    by_cases h : M r k = 0
    · simp [h]
    · rw [cond r k h]; ac_rfl

private theorem orig_comp (g h : (Box → ℂ) → Box → ℂ) :
    applyOriginal h ∘ applyOriginal g = applyOriginal (h ∘ g) := by
  funext x r
  cases r <;> rfl

private theorem clear (j : J) (F : StartAxes) (s : Lab) :
    CPath (basis j F) (labels s) (labels s) (applyOriginal id) (fun _ => 0) := by
  have h := CPath.gate (A := basis j F) (s := labels s)
    (gatherMatrix (0 : Matrix Free Box ℚ)) (by
      rintro (i|i) (k|k) hk <;> simp [gatherMatrix, one_apply] at hk
      subst k; rfl)
  have he : actPoint (gatherMatrix (0 : Matrix Free Box ℚ)) = applyOriginal id := by
    funext x r
    rcases r with i|k
    · exact gather_original _ _ i
    · simpa [applyOriginal] using (gather_scratch (0 : Matrix Free Box ℚ) x k)
  rwa [he] at h

private def keep (g : (Box → ℂ) → Box → ℂ) (x : Box ⊕ Free → ℂ) :
    Box ⊕ Free → ℂ := Sum.elim (g (x ∘ Sum.inl)) (x ∘ Sum.inr)

private theorem liftOriginal {j : J} {F : StartAxes} {s t : Lab}
    {g : (Box → ℂ) → Box → ℂ} {prof : (ℕ → ℝ) → ℝ}
    (p : CPath (basisBox j F) s t g prof) :
    CPath (basis j F) (labels s) (labels t) (applyOriginal g) prof := by
  let e : Box ↪ Box ⊕ Free := Function.Embedding.inl
  have h : CPath (basis j F) (labels s) (labels t) (keep g) prof := by
    apply CPath.lift e (basis j F) (h := g) (g := keep g) (s := labels s) (t := labels t)
      (profile := prof)
    · exact p
    · intro x; rfl
    · rintro x (k|k) hk
      · exfalso
        apply hk
        rw [cover_iff]
        exact ⟨k,rfl⟩
      · rfl
    · rintro (k|k) hk
      · exfalso
        apply hk
        rw [cover_iff]
        exact ⟨k,rfl⟩
      · rfl
  have hh := (clear j F s).trans h
  have he : keep g ∘ applyOriginal id = applyOriginal g := by
    funext x r
    cases r <;> rfl
  simpa only [he, zero_add] using hh

private def mixLabel (s : Lab) (S : Mask) : Box ⊕ Free → Mask :=
  Sum.elim s (fun _ => S)

private theorem gatherScatter {η κ : Type} [Fintype η] [DecidableEq η]
    [Fintype κ] [DecidableEq κ] (B : Matrix κ η ℚ) (D : Matrix η κ ℚ) :
    actPoint (consumeMatrix D) ∘ id ∘ actPoint (gatherMatrix B) =
      fun z => Sum.elim (actPoint (1 + D*B) (z ∘ Sum.inl)) (fun _ : κ => 0) := by
  funext z r
  cases r with
  | inr k => exact consume_scratch D _ k
  | inl i =>
    simp only [Function.comp_apply, id_eq, Sum.elim_inl, consume_original,
      gather_original, gather_scratch]
    have hone : (∑ k : η, ((1 : Matrix η η ℚ) i k : ℂ) * z (.inl k)) = z (.inl i) := by
      rw [sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    simp only [actPoint, Matrix.add_apply, Rat.cast_add, _root_.add_mul,
      sum_add_distrib, Function.comp_apply, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul,
      sum_mul, mul_sum, mul_assoc, hone]
    rw [Finset.sum_comm (s := (univ : Finset η))]

private theorem sharing {j : J} {F : StartAxes} {s : Lab} {S T : Mask}
    (B : Matrix Free Box ℚ) (D : Matrix Box Free ℚ)
    (hB : ∀ k i, B k i ≠ 0 → frame (basis j F (.inr k)) S = frame (basisBox j F i) (s i))
    (hD : ∀ i k, D i k ≠ 0 → frame (basisBox j F i) (s i) = frame (basis j F (.inr k)) T) :
    CPath (basis j F) (labels s) (labels s) (applyOriginal (actPoint (1 + D * B)))
      (fun c => 30 * c (changeSize S T)) := by
  have collect := gateTo (basis j F) (labels s) (mixLabel s S) (gatherMatrix B) (by
    rintro (i|i) (k|k) hk
    · simp [gatherMatrix, one_apply] at hk; subst k; rfl
    · simp [gatherMatrix] at hk
    · exact hB i k hk
    · simp [gatherMatrix] at hk)
  have scatter := gateTo (basis j F) (mixLabel s T) (labels s) (consumeMatrix D) (by
    rintro (i|i) (k|k) hk
    · simp [consumeMatrix, one_apply] at hk; subst k; rfl
    · exact hD i k hk
    · simp [consumeMatrix] at hk
    · simp [consumeMatrix] at hk)
  have transfer := CPath.reframe (basis j F) (mixLabel s S) (mixLabel s T)
  obtain ⟨w, bill, acts⟩ := (collect.trans transfer).trans scatter
  refine ⟨w, ?_, ?_⟩
  · intro c hc
    rw [bill c hc]
    have h0 (i : Box) : changeSize (s i) (s i) = 0 := by simp [changeSize]
    simp only [zero_add, add_zero, frameCost, mixLabel, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, h0, hc, sum_const_zero, sum_const, card_univ, nsmul_eq_mul, free_card, Nat.cast_ofNat]
  · intro f x
    rw [acts]
    have he : actPoint (consumeMatrix D) ∘ id ∘ actPoint (gatherMatrix B) =
        applyOriginal (actPoint (1 + D * B)) := gatherScatter B D
    rw [he]

private def middle : Q := fromBlocks (fromBlocks 0 0 (rmat * glocal) 0 : Matrix XY XY ℚ) 0 0 0

private theorem middle_factor : targetRows * sourceRows = middle := by
  ext i k
  rcases i with ((i|i)|(i|i)) <;> rcases k with ((k|k)|(k|k)) <;>
    simp [Matrix.mul_apply, targetRows, sourceRows, middle, forward_factor]

private theorem middle_square : middle * middle = 0 := by
  simp [middle, fromBlocks_multiply]

private theorem middle_path (j : J) (F : StartAxes) :
    (CPath (basis j F) (labels (b4 j)) (labels (b4 j))
      (applyOriginal (actPoint (1 + middle))) (fun c => 30 * c 32)) ∧
    (CPath (basis j F) (labels (b4 j)) (labels (b4 j))
      (applyOriginal (actPoint (1 - middle)ᵀ)) (fun c => 30 * c 32)) := by
  have hb : ∀ i : Trip, ∀ k : Free,
      frame (basis j F (.inr k)) (big j) =
      frame (basisBox j F (bx i)) (b4 j (bx i)) := by
    intro i k
    apply frame_congr
    apply big_proj
    exact upd_same j F _ _
  have ht : ∀ i : Trip, ∀ k : Free, frame (basisBox j F (byy i)) (b4 j (byy i)) =
      frame (basis j F (.inr k)) (belt j) := by
    intro i k
    apply frame_congr
    apply belt_proj
    exact upd_same j F _ _
  have hs : belt j ⊆ big j := fun x hx => (in_big j x).mpr ((in_belt j x).mp hx).1
  have hd : changeSize (big j) (belt j) = 32 := by
    rw [changeSize_symm, changeSize_of_subset hs, ← card_sdiff_of_subset hs, belt_drop]
  have hu : changeSize (belt j) (big j) = 32 := by
    rw [changeSize_symm]; exact hd
  constructor
  · have h := sharing (j := j) (F := F) (s := b4 j) (S := big j) (T := belt j)
      sourceRows targetRows (by
        rintro k ((i|i)|(i|i)) h
        · exact hb i k
        all_goals exact False.elim (h rfl))
      (by
        rintro ((i|i)|(i|i)) k h
        · exact False.elim (h rfl)
        · exact ht i k
        all_goals exact False.elim (h rfl))
    simpa only [middle_factor, hd] using h
  · have h := sharing (j := j) (F := F) (s := b4 j) (S := belt j) (T := big j)
      targetRowsᵀ (-sourceRowsᵀ) (by
        rintro k ((i|i)|(i|i)) h
        · exact False.elim (h rfl)
        · exact (ht i k).symm
        all_goals exact False.elim (h rfl))
      (by
        rintro ((i|i)|(i|i)) k h
        · exact (hb i k).symm
        all_goals simp only [Matrix.neg_apply, Matrix.transpose_apply, sourceRows, neg_zero,
          ne_eq, not_true_eq_false] at h)
    have he : (1 : Q) + (-sourceRowsᵀ) * targetRowsᵀ = (1 - middle)ᵀ := by
      rw [Matrix.neg_mul, ← Matrix.transpose_mul, middle_factor,
        transpose_sub, transpose_one, sub_eq_add_neg]
    rw [hu, he] at h
    exact h

private def Dual (j : J) (F : StartAxes) (s t : Lab) (M : Q)
    (p : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ N : Q, M * N = 1 ∧
    CPath (basis j F) (labels s) (labels t) (applyOriginal (actPoint M)) p ∧
    CPath (basis j F) (labels s) (labels t) (applyOriginal (actPoint Nᵀ)) p

private theorem liftDual {j F s t M p} (h : CDPath j F s t M p) : Dual j F s t M p := by
  obtain ⟨N, hi, hf, hb⟩ := h
  exact ⟨N, hi, liftOriginal hf, liftOriginal hb⟩

private theorem dualTrans {j F s t u M N p q}
    (h : Dual j F s t M p) (k : Dual j F t u N q) :
    Dual j F s u (N * M) (fun c => p c + q c) := by
  obtain ⟨x, hx, f, b⟩ := h
  obtain ⟨y, hy, g, d⟩ := k
  refine ⟨x * y, ?_, ?_, ?_⟩
  · rwa [Matrix.mul_assoc, ← Matrix.mul_assoc M, hx, one_mul]
  · simpa only [OriginalGroupedPricedSharedNetwork.ap_mul, orig_comp] using f.trans g
  · simpa only [transpose_mul, OriginalGroupedPricedSharedNetwork.ap_mul, orig_comp] using b.trans d

private theorem native_product :
    (1-eV) * (1+eJ) * (1+middle) * (1+eV) * (1-eJ) = 1 + eXY := by
  have hVJ : eV * eJ = 0 := by simp [eV, eJ, giveAux, takeAux, fromBlocks_multiply]
  have hKM : middle * eV = 0 := by simp [middle, eV, takeAux, fromBlocks_multiply]
  have hKJ : middle * eJ = 0 := by simp [middle, eJ, giveAux, fromBlocks_multiply]
  have hVK : eV * middle = 0 := by simp [middle, eV, takeAux, fromBlocks_multiply]
  have hJK : eJ * middle = 0 := by simp [middle, eJ, giveAux, fromBlocks_multiply]
  have hsum : middle + eJ * eV = eXY := by
    simp [middle, eV, eJ, eXY, giveAux, takeAux, fromBlocks_multiply,
      fromBlocks_add, rg_jv]
  rw [← hsum]
  simp only [_root_.sub_mul, _root_.add_mul, _root_.mul_sub, _root_.mul_add, one_mul,
    mul_one, Matrix.mul_assoc, hVJ, hJK, hVK, hKJ, hKM, zero_VV, zero_JJ, mul_zero, zero_mul]
  abel

private theorem compiled_path (j : J) (F : StartAxes) :
    Dual j F (bp j) (bend j) (1 + eXY) (fun c =>
      frameCost (bp j) (b0 j) c + frameCost (b0 j) (b1 j) c +
      frameCost (b1 j) (b2 j) c + frameCost (b2 j) (b4 j) c +
      30 * c 32 + frameCost (b4 j) (b5 j) c + frameCost (b5 j) (b6 j) c +
      frameCost (b6 j) (b7 j) c + frameCost (b7 j) (bend j) c) := by
  have shift (s t : Lab) := liftDual (CDPath.reframe j F s t)
  have center : Dual j F (b4 j) (b4 j) (1 + middle) (fun c => 30 * c 32) :=
    ⟨1-middle, inv_one_add middle_square, middle_path j F⟩
  have h0 := dualTrans (shift (bp j) (b0 j)) (liftDual (CDPath.paired zero_JJ (sync0 j F)).2)
  have h1 := dualTrans h0 (shift (b0 j) (b1 j))
  have h2 := dualTrans (dualTrans h1 (shift (b1 j) (b2 j)))
    (liftDual (CDPath.paired zero_VV (sync2 j F)).1)
  have h4 := dualTrans (dualTrans h2 (shift (b2 j) (b4 j))) center
  have h5 := dualTrans (dualTrans h4 (shift (b4 j) (b5 j)))
    (liftDual (CDPath.paired zero_JJ (sync5 j F)).1)
  have h6 := dualTrans h5 (shift (b5 j) (b6 j))
  have h7 := dualTrans (dualTrans h6 (shift (b6 j) (b7 j)))
    (liftDual (CDPath.paired zero_VV (sync7 j F)).2)
  have ht := dualTrans h7 (shift (b7 j) (bend j))
  simpa only [one_mul, mul_one, ← Matrix.mul_assoc, native_product, add_zero] using ht

/-- A single witness supplies every original output and its own callback bill.
The first and last scalar passes accept arbitrary scratch and leave it zero. -/
theorem invocation (j : J) (F : StartAxes) (rev : Bool) :
    CPath (basis j F) (labels (bp j)) (labels (bend j))
      (applyOriginal (if rev then OriginalGroupedPricedSharedNetwork.backward
        else OriginalGroupedPricedSharedNetwork.forward)) (CenterCacheCensus.invocationCost j) := by
  obtain ⟨N, hN, H, G⟩ := compiled_path j F
  have h : N = 1-eXY := by
    calc
      N = ((1-eXY)*(1+eXY))*N := by rw [inv_one_sub zero_XX, one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hN, mul_one]
  subst N
  have hp := fun (c : ℕ → ℝ) (hc : c 0 = 0) => CenterCacheCensus.shortenedCost_add_free j c hc
  rw [OriginalGroupedPricedSharedNetwork.ap_f] at H
  rw [OriginalGroupedPricedSharedNetwork.ap_b] at G
  cases rev
  · obtain ⟨w, hw, ha⟩ := H
    exact ⟨w, fun c hc => (hw c hc).trans (by
      rw [← hp c hc]; unfold CenterCacheCensus.shortenedCost; ring), ha⟩
  · obtain ⟨w, hw, ha⟩ := G
    exact ⟨w, fun c hc => (hw c hc).trans (by
      rw [← hp c hc]; unfold CenterCacheCensus.shortenedCost; ring), ha⟩

end
end FourierTensor.CenterCacheWord
