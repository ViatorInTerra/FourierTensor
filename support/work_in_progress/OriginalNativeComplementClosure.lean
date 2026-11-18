import work_in_progress.OriginalGroupedFrameFactorization

/-! Complementary requests reuse the existing native orthonormal basis.
There is no dense general quadratic adapter or extra kernel conversion.
-/
namespace FourierSchur.OriginalNativeComplementClosure
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem projection_partition (A : OBase α) (s : Finset α) (x : Space α) :
    A.proj s x+A.proj (univ\s) x=x := by
  have hs := Finset.sum_sdiff (Finset.subset_univ s)
    (f:=fun k => dot (A.v k) x • A.v k)
  change A.proj (univ\s) x+A.proj s x=A.proj univ x at hs
  rw [add_comm,hs,A.proj_univ]

theorem projection_orthogonal (A : OBase α) (s : Finset α) (x : Space α) :
    dot (A.proj s x) (A.proj (univ\s) x)=0 := by
  rw [dot_symm]
  change dot (A.proj (univ\s) x) (∑ k∈s,dot (A.v k) x • A.v k)=0
  rw [dot_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [dot_smul_right,dot_symm (A.proj (univ\s) x) (A.v k),
    A.dot_proj_omit x (by simp [hk]),mul_zero]

theorem frame_partition (A : OBase α) (s : Finset α) :
    frame A s*frame A (univ\s)=kernel α := by
  rw [frame,frame,wrap_mul,← wrap_lum]
  congr 1
  funext x
  have h := lum_add (A.proj s x) (A.proj (univ\s) x)
  rw [projection_partition,projection_orthogonal] at h
  simpa [sign] using h.symm

/-- A full-kernel crossing with the inverse partial action is emitted as
one request on the complementary mask, in the original native basis. -/
theorem kernel_unframe (A : OBase α) (s : Finset α) :
    kernel α*unframe A s=frame A (univ\s) := by
  have hc : frame A s*frame A (univ\s)=frame A (univ\s)*frame A s := by
    exact wrap_comm _ _
  rw [← frame_partition A s,hc,Matrix.mul_assoc,unframe_right,mul_one]

theorem kernel_unframe_amplified (A : OBase α) (s : Finset α) (f : ℕ)
    (x : Sky α f→ℂ) :
    matAct f (kernel α*unframe A s) x=matAct f (frame A (univ\s)) x := by
  rw [kernel_unframe]

end
end FourierSchur.OriginalNativeComplementClosure
