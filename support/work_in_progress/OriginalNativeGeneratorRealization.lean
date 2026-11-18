import work_in_progress.OriginalNativeGeneratorSymbols

/-! Physical realization of the small native-generator alphabet. The
full kernel and every orthonormal line frame satisfy exactly the square
relations used by the sparse global certificate.
-/
namespace FourierSchur.OriginalNativeGeneratorRealization
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeGeneratorSymbols OriginalBinaryMatrixCertificates
noncomputable section

theorem wordVector_full (n : ℕ) : wordVector n (2^n-1)=fun _ => 1 := by
  funext i
  simp [wordVector,← bitValue_div,bitValue,Nat.testBit_two_pow_sub_one,i.isLt]

theorem full_square (n : ℕ) (x : Space (Fin n)) :
    lum x*lum x=character n (2^n-1) x := by
  rw [lum_sq,character,wordVector_full]
  congr 1
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  rcases bit_cases (x i) with h|h <;> simp [h]

def lineSymbol {n : ℕ} (v : Space (Fin n)) (x : Space (Fin n)) : ℂ :=
  lum (dot v x • v)

theorem line_square {n : ℕ} (word : ℕ) (hv : dot (wordVector n word) (wordVector n word)=1)
    (x : Space (Fin n)) :
    lineSymbol (wordVector n word) x*lineSymbol (wordVector n word) x=
      character n word x := by
  unfold lineSymbol character
  rcases bit_cases (dot (wordVector n word) x) with h|h
  · simp [h,sign]
  · rw [h,one_smul,lum_sq,hv]

theorem value_generator {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (i : Fin k) (x : Space (Fin n)) :
    value generators ⟨2^i.val,0⟩ x=generators i x := by
  simp only [value,character_zero,one_mul]
  rw [Finset.prod_eq_single i]
  · simp [Nat.testBit_two_pow_self]
  · intro j _ hj
    have hn : i.val≠j.val := fun he => hj (Fin.ext he.symm)
    simp [Nat.testBit_two_pow_of_ne hn]
  · simp

theorem operator_generator {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (i : Fin k) : operator generators ⟨2^i.val,0⟩=wrap (generators i) := by
  apply congrArg wrap
  funext x
  exact value_generator generators i x

theorem operator_translation {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (z : ℕ) : operator generators ⟨0,z⟩=shift (wordVector n z) := by
  rw [operator,shift_phase]
  congr 1
  funext x
  simp [value,character]

theorem singleton_frame {n : ℕ} (A : OBase (Fin n)) (i : Fin n) :
    frame A {i}=wrap (lineSymbol (A.v i)) := by
  apply congrArg wrap
  funext x
  change lum (A.proj {i} x)=lum (dot (A.v i) x • A.v i)
  simp [OBase.proj]

end
end FourierSchur.OriginalNativeGeneratorRealization
