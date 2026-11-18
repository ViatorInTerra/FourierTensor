import work_in_progress.OriginalBinaryMatrixCertificates

/-! Native line/complement bases from short checked direction words.
Orthonormality follows from the proved transvection construction. No large
numeric Gram-matrix decision or general quadratic adapter is required.
-/
namespace FourierSchur.OriginalCheckedNativeDirection
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates
noncomputable section

theorem checked_self (n word : ℕ) (h : fastDot n word word=1) :
    dot (wordVector n word) (wordVector n word)=1 := by
  have hd := dotParity_cast n word word
  rw [← fastDot_eq,h] at hd
  exact hd.symm

theorem checked_zero (n word : ℕ) (pivot : Fin n)
    (h : bitValue word pivot.val=0) : wordVector n word pivot=0 := by
  simp only [wordVector,← bitValue_div,h,Nat.cast_zero]

def basis (n word : ℕ) (pivot : Fin n)
    (hself : fastDot n word word=1) (hzero : bitValue word pivot.val=0) : OBase (Fin n) :=
  OBase.adapt (OBase.canonical (Fin n)) pivot (wordVector n word)
    (checked_self n word hself)
    (by simpa [OBase.canonical] using checked_zero n word pivot hzero)

theorem basis_pivot (n word : ℕ) (pivot : Fin n)
    (hself : fastDot n word word=1) (hzero : bitValue word pivot.val=0) :
    (basis n word pivot hself hzero).v pivot=wordVector n word :=
  OBase.adapt_pivot _ _ _ _ _

theorem basis_singleton (n word : ℕ) (pivot : Fin n)
    (hself : fastDot n word word=1) (hzero : bitValue word pivot.val=0) :
    (basis n word pivot hself hzero).mat {pivot}=
      Matrix.vecMulVec (wordVector n word) (wordVector n word) := by
  ext i j
  simp [OBase.mat,basis_pivot,Matrix.vecMulVec]

theorem basis_complement (n word : ℕ) (pivot : Fin n)
    (hself : fastDot n word word=1) (hzero : bitValue word pivot.val=0) :
    (basis n word pivot hself hzero).mat (univ\{pivot})=
      1-Matrix.vecMulVec (wordVector n word) (wordVector n word) := by
  rw [OBase.mat_sub _ _ _ (Finset.subset_univ _),OBase.mat_univ,basis_singleton]

end
end FourierSchur.OriginalCheckedNativeDirection
