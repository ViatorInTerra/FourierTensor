import work_in_progress.OriginalNativeCenterSharing

/-!
# Center observations before and after caching

The two equalities below compare the contents of the center banks at every
subsequent observer of a forward or inverse-transpose invocation. The linear
transfer may act on an entire complex physical bank. The incoming original
centers are arbitrary. Only the increment made by the actual incidence
matrix is reconstructed from the free rows.
-/

namespace FourierTensor.CenterCache

open OAI.PowerSaving.Cluster FourierSchur.OriginalNativeCenterSharing
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

private def rows {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (x : κ → V) (i : ι) : V :=
  ∑ j, A i j • x j

private theorem rows_mul {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (A : Matrix ι κ ℚ) (B : Matrix κ μ ℚ) (x : μ → V) :
    rows (A * B) x = rows A (rows B x) := by
  funext i
  simp only [rows, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem transfer_rows {ι κ : Type*} [Fintype κ]
    (Z : V ≃ₗ[ℚ] V) (E : Matrix ι κ ℚ) (x : κ → V) (i : ι) :
    rows E (fun j => Z (x j)) i = Z (rows E x i) := by
  simp only [rows, map_sum, map_smul]

/-- Contents after generation, on return, at the repeated crossing, and
after subtraction. Each component is the entire center array. -/
def forwardReads (Z : V ≃ₗ[ℚ] V) (v d : Center → V) :=
  let t := fun i => Z (v i) + d i
  let b := fun i => Z.symm (t i)
  let a := fun i => Z (b i)
  (t, b, a, fun i => a i - d i)

def cachedForwardReads (Z : V ≃ₗ[ℚ] V) (v : Center → V) (x : Trip → V) :=
  let free := rows freeRows x
  let d := rows (expandCenter (1/3)) free
  let t := fun i => Z (v i) + d i
  let b := fun i => v i + rows (expandCenter (1/3)) (fun j => Z.symm (free j)) i
  (t, b, t, fun i => t i - d i)

/-- Equality at all four forward observations for the actual generated rows. -/
theorem forward_all_centers (Z : V ≃ₗ[ℚ] V) (v : Center → V) (x : Trip → V) :
    cachedForwardReads Z v x = forwardReads Z v (rows glocal x) := by
  rw [glocal_factor, rows_mul]
  simp [cachedForwardReads, forwardReads, transfer_rows, map_add]

/-- The inverse-transpose invocation generates in the belt frame, returns
there before subtraction, and subsequently observes the transformed original. -/
def inverseReads (Z : V ≃ₗ[ℚ] V) (v d : Center → V) :=
  let b := fun i => v i + d i
  let a := fun i => Z (b i)
  let back := fun i => Z.symm (a i)
  (b, a, back, fun i => Z (back i - d i))

def cachedInverseReads (Z : V ≃ₗ[ℚ] V) (v : Center → V) (y : Trip → V) :=
  let free := rows ((1/2 : ℚ) • freeRows) y
  let d := rows (expandCenter (-1/3)) free
  let b := fun i => v i + d i
  let a := fun i => Z (b i)
  (b, a, b, fun i => a i - rows (expandCenter (-1/3)) (fun j => Z (free j)) i)

/-- Equality at all four inverse-transpose observations. The negative
distinguished-row coefficient belongs to the actual transpose producer. -/
theorem inverse_all_centers (Z : V ≃ₗ[ℚ] V) (v : Center → V) (y : Trip → V) :
    cachedInverseReads Z v y = inverseReads Z v (rows rmat.transpose y) := by
  rw [rmat_transpose_factor, rows_mul]
  simp [cachedInverseReads, inverseReads, transfer_rows, map_add]

end FourierTensor.CenterCache
