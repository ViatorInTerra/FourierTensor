import work_in_progress.OriginalQuadraticCharacterCertificates
import work_in_progress.OriginalPhysicalChirpRAM

/-! Computable finite binary matrix certificates with a kernel proof of
their matrix meaning. Integer checking is not an axiom or a runtime oracle.
The encoded rows/columns are fixed finite program metadata. -/
namespace FourierSchur.OriginalBinaryMatrixCertificates
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalPhysicalChirpRAM

def wordVector (n a : ℕ) : Space (Fin n) := fun j => ((a/2^j.val%2:ℕ):F)

def wordRows (n : ℕ) (rows : Fin n→ℕ) : Matrix (Fin n) (Fin n) F :=
  fun i j => wordVector n (rows i) j

def wordColumns (n : ℕ) (cols : Fin n→ℕ) : Matrix (Fin n) (Fin n) F :=
  (wordRows n cols).transpose

def bitValue (a j : ℕ) : ℕ := (a.testBit j).toNat

theorem bitValue_div (a j : ℕ) : bitValue a j=a/2^j%2 := by
  rcases Nat.mod_two_eq_zero_or_one (a/2^j) with h|h <;>
    simp [bitValue,Nat.testBit_eq_decide_div_mod_eq,h]

def fastDot (n a b : ℕ) : ℕ :=
  (∑ j∈range n,bitValue a j*bitValue b j)%2

theorem fastDot_eq (n a b : ℕ) : fastDot n a b=dotParity n a b := by
  simp [fastDot,dotParity,bitValue_div]

def ProductCheck (n : ℕ) (rowsA colsB colsC : Fin n→ℕ) : Prop :=
  ∀ i j, fastDot n (rowsA i) (colsB j)=bitValue (colsC j) i.val

instance (n : ℕ) (rowsA colsB colsC : Fin n→ℕ) :
    Decidable (ProductCheck n rowsA colsB colsC) := by
  unfold ProductCheck
  infer_instance

theorem dotParity_cast (n a b : ℕ) :
    (dotParity n a b:F)=dot (wordVector n a) (wordVector n b) := by
  unfold dotParity dot wordVector
  rw [ZMod.natCast_mod,← Fin.sum_univ_eq_sum_range]
  simp only [Nat.cast_sum,Nat.cast_mul]

/-- The checked integer products imply the actual binary matrix product. -/
theorem product_check_sound (n : ℕ) (rowsA colsB colsC : Fin n→ℕ)
    (h : ProductCheck n rowsA colsB colsC) :
    wordRows n rowsA*wordColumns n colsB=wordColumns n colsC := by
  ext i j
  change dot (wordVector n (rowsA i)) (wordVector n (colsB j))=
    ((colsC j/2^i.val%2:ℕ):F)
  rw [← dotParity_cast]
  have H := h i j
  rw [fastDot_eq,bitValue_div] at H
  exact congrArg (fun x : ℕ => (x:F)) H

/-- Natural-number evaluator for the exact encoded Z4 quadratic.
Its relation to the complex character is a separate proof obligation. -/
def wordQuadratic (n lo hi x : ℕ) : ℕ :=
  ((∑ i∈range n, (bitValue lo i+2*bitValue hi i)*bitValue x i)+
    2*∑ i∈range n,∑ j∈range n,
      if i<j then bitValue hi (n+i*(2*n-i-1)/2+(j-i-1))*bitValue x i*bitValue x j
      else 0)%4

def UnaryCheck (n lo hi rank shift : ℕ) (columns : Fin n→ℕ) : Prop :=
  ∀ i, wordQuadratic n lo hi (columns i)=
    (if i.val<rank then 1 else 0)+2*bitValue shift i.val

instance (n lo hi rank shift : ℕ) (columns : Fin n→ℕ) :
    Decidable (UnaryCheck n lo hi rank shift columns) := by
  unfold UnaryCheck
  infer_instance

end FourierSchur.OriginalBinaryMatrixCertificates
