import FourierTensor.CachedExecutor
import work_in_progress.OriginalSharedBlockCompletion

/-! Two fixed programs evaluate the positive-sign, unnormalized Fourier
transform. The first reads only the length and computes the required root
order. The bill pays for that program, a single root operation, and the
transform which uses the cached tensor executor. -/
namespace FourierTensor.AllLengthProgram

open OAI.PowerSaving OAI.PowerSaving.Selection OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OAI.PowerSaving.RAM.Bench
open OAI.PowerSaving.Slant
open FourierSchur FourierSchur.OriginalCompilerRootBridge
noncomputable section

abbrev transformBound (d n : ℕ) :=
  OriginalAllLengthSubstitution.fairwind CachedExecutor.density d n

def orderBound (d n : ℕ) := n + (stackN n + 2)^d

/-- Input length and stack preparation for the order program, one root
instruction, and the full transform allowance. Each program's constants
are fixed independently of the length and the input coefficients. -/
def compilerBill (a b : Ration) (n : ℕ) : ℕ :=
  a.c * (orderBound a.d n + 1) + 1 + b.c * (transformBound b.d n + 1)

theorem density_monotone : Monotone CachedExecutor.density :=
  OriginalStrictSquareRootMargin.powerProfile_monotone _ CenterCacheRate.exponents_pos_lt.1.le

private theorem density_le (k : ℕ) : CachedExecutor.density k ≤ k+1 := by
  apply Nat.ceil_le.mpr
  push_cast
  calc
    ((k:ℝ)+1)^CachedExecutor.exponent ≤ ((k:ℝ)+1)^(1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
        CenterCacheRate.exponents_pos_lt.2.le
    _ = _ := Real.rpow_one _

theorem compilerBill_le_fairwind (a b : Ration) (n : ℕ) :
    compilerBill a b n ≤ (a.c+b.c+1)*(transformBound (a.d+b.d) n+1) := by
  have ha : orderBound a.d n ≤ transformBound (a.d+b.d) n :=
    (OriginalAllLengthSubstitution.fairwind_left CachedExecutor.density n a.d).trans
      (OriginalAllLengthSubstitution.fairwind_deg n (Nat.le_add_right ..))
  have hb : transformBound b.d n ≤ transformBound (a.d+b.d) n :=
    OriginalAllLengthSubstitution.fairwind_deg n (Nat.le_add_left ..)
  unfold compilerBill
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  have h₁ := Nat.mul_le_mul_left a.c (Nat.add_le_add_right ha 1)
  have h₂ := Nat.mul_le_mul_left b.c (Nat.add_le_add_right hb 1)
  omega

private theorem transformBound_small (d : ℕ) : Small entry (fun i => transformBound d (entry i)) := by
  let N := entry
  have H := Small.self N
  have hX (i : Sizes) := barge_spec (N i) i.property
  have h4 := (Small.const _ 4).mul H
  have hu := h4.mono (fun i => stack_le (N i) i.property)
  have hk : Small N fun i => harvestN (N i) :=
    ((Small.const _ 16).mul (hu.add (Small.const _ 4))).pow 2
  have hh := ((Small.const _ 8).mul hk).mono
    (fun i => Nat.lt_two_pow_self.le.trans (orderE_small (N i)))
  have hi := (((Small.const _ 20000000).mul ((hh.add (Small.const _ 1)).pow 2)).add
    (Small.const _ 7)).mono (fun i => score_le (orderE (N i)))
  have hp : Small N fun i => CachedExecutor.density (barge (N i)).l :=
    (hu.add (Small.const _ 1)).mono fun i => (density_le _).trans
      (Nat.add_le_add_right (hX i).count _)
  have hj := (hi.add (Small.const _ 1)).mul
    ((h4.mono fun i => (hX i).upper.le).mul (hp.add (Small.const _ 1)))
  have hl := (H.add hj).add ((hu.add (Small.const _ 2)).pow d)
  exact hl.add (((H.add (Small.const _ 2)).pow d).mono fun i => by
    dsimp only [N]; split <;> omega)

/-- Both orientations of the compiled Fourier subroutines use the revised
tensor algorithm, including the scalar subroutine for chirp preparation. -/
theorem solve_exists : ∃ (solve : Prog false dftInKind dftOutKind) (b : Ration),
    ∀ (n : ℕ), 0<n → ∀ x : Vec n,
      (run solve (n,root (receipt n),(⟨n,x⟩ : Tape ℂ))).OK
        (⟨n,dft n x⟩ : Tape ℂ) (b.c*(transformBound b.d n+1)) ((n+2)^b.p) := by
  obtain ⟨s,d,c,p,H⟩ := OriginalAllLengthSubstitution.executeOne_supplied
    (OriginalSharedBlockCompletion.supplied_of_complete
      (CachedExecutor.complete_executor .left false) sc parentRoot)
    (OriginalSharedBlockCompletion.supplied_of_complete
      (CachedExecutor.complete_executor .scalar false) sc parentRoot)
    density_monotone
  exact ⟨s,⟨d,c,p⟩,H⟩

private theorem order_exists : ∃ (order : Prog false w w) (a : Ration),
    ∀ (n : ℕ), 0<n →
      (run order n).OK (receipt n) (a.c*(orderBound a.d n+1)) ((n+2)^a.p) := by
  obtain ⟨d,hd⟩ := onlyLength_num.planOrder (fun i => i.property)
  obtain ⟨s,c,p,h⟩ := Can.unfold_bound hd
  exact ⟨s,⟨d,c,p⟩,fun n hn => h ⟨n,hn⟩⟩

private theorem word_cap (a b : Ration) : ∃ p : ℕ, ∀ n : ℕ, 0<n →
    compilerBill a b n + 10*(n+2) ≤ (n+2)^p ∧
    (n+2)^a.p ≤ (n+2)^p ∧ (n+2)^b.p ≤ (n+2)^p ∧ receipt n ≤ (n+2)^p := by
  have hn := Small.self entry
  have hu := hn.add (Small.const _ 2)
  have hbill : Small entry (fun i => compilerBill a b (entry i)) :=
    ((Small.const entry (a.c+b.c+1)).mul
      ((transformBound_small (a.d+b.d)).add (Small.const _ 1))).mono
      (fun i => compilerBill_le_fairwind a b (entry i))
  have hrec := ((Small.const _ 8).mul (hn.pow 3)).mono
    (fun i => (receipt_bound (entry i) i.property).2.le)
  have htotal := hbill.add ((Small.const _ 10).mul hu)
  obtain ⟨p,hp⟩ := ((htotal.max (hu.pow a.p)).max (hu.pow b.p)).max hrec
  refine ⟨p, fun n h => ?_⟩
  have H : max (max (max (compilerBill a b n + 10*(n+2)) ((n+2)^a.p)) ((n+2)^b.p))
      (receipt n) ≤ (n+2)^p := hp ⟨n,h⟩
  simpa only [max_le_iff, and_assoc] using H

/-- One choice of the two native programs handles all positive Fourier
lengths and all complex input vectors. The supplied root has exactly the
order computed by the integer program, which is strictly below 8 n³. -/
theorem certificate : ∃ (order : Prog false w w) (solve : Prog false dftInKind dftOutKind)
    (a b : Ration), DFTProgram order solve (compilerBill a b) ∧
      ∀ n : ℕ, 0<n → (run order n).val = receipt n ∧ (run order n).val < 8*n^3 := by
  obtain ⟨order,a,ho⟩ := order_exists
  obtain ⟨solve,b,hs⟩ := solve_exists
  obtain ⟨p,cap⟩ := word_cap a b
  refine ⟨order,solve,a,b,⟨p,fun n hn => ?_⟩,fun n hn => ?_⟩
  · obtain ⟨hw,ha,hb,hr⟩ := cap n hn
    have H := ho n hn
    have R := receipt_bound n hn
    have he := H.result
    refine ⟨hw,H.bound.trans ha,H.valid,he.symm ▸ R.1,he.symm ▸ ?_,
      he.symm ▸ hr,fun x => ?_⟩
    · exact R.2.trans_le (by omega)
    · dsimp only
      rw [he]
      have S := hs n hn x
      exact ⟨S.valid,S.bound.trans hb,add_le_add (add_le_add_left H.time 1) S.time,S.result⟩
  · exact ⟨(ho n hn).result,(ho n hn).result.symm ▸ (receipt_bound n hn).2⟩

end
end FourierTensor.AllLengthProgram
