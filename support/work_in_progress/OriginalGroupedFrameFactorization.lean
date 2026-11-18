import vendor.OpenAIUniformFourierBundle
import Mathlib.Data.Finset.SymmDiff

/-! Full frame changes are a complete forward residual kernel followed by
one address translation. Fourier matrices occur only in the equality proof;
they are not emitted by the RAM compiler. Inverse factors are retained by
the explicit correction vector, on every complex input.
-/
namespace FourierSchur.OriginalGroupedFrameFactorization
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open scoped symmDiff
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def forwardPhase (A : OBase α) (s : Finset α) (x : Space α) : ℂ :=
  ∏ i ∈ s, tint (dot (A.v i) x)

def forwardMask (A : OBase α) (s : Finset α) : CMat α := wrap (forwardPhase A s)

def correctionSet (A : OBase α) (s t : Finset α) : Finset α :=
  ((t\s).filter fun i => lum (A.v i)=-Complex.I) ∪
    ((s\t).filter fun i => lum (A.v i)=Complex.I)

def correction (A : OBase α) (s t : Finset α) : Space α :=
  ∑ i ∈ correctionSet A s t, A.v i

theorem lum_proj_product (A : OBase α) (s : Finset α) (x : Space α) :
    lum (A.proj s x)=∏ i ∈ s, lum (dot (A.v i) x • A.v i) := by
  induction s using Finset.induction with
  | empty => simp [OBase.proj]
  | insert i s hi ih =>
    have he : A.proj (insert i s) x=dot (A.v i) x • A.v i+A.proj s x := by
      simp [OBase.proj,hi]
    rw [he,lum_add]
    simp [dot_smul_left,OBase.dot_proj_omit A x hi,sign,hi,ih]

theorem prod_subset (s : Finset α) (v : α → ℂ) :
    (∏ i ∈ s, v i)=∏ i : α, if i∈s then v i else 1 := by
  have h : univ.filter (fun i => i∈s)=s := by ext i; simp
  rw [← h,prod_filter]
  simp

theorem correction_phase (A : OBase α) (s t : Finset α) (x : Space α) :
    sign (dot (correction A s t) x)=
      ∏ i ∈ correctionSet A s t, sign (dot (A.v i) x) := by
  rw [correction,dot_symm,dot_sum,sign_sum]
  apply prod_congr rfl
  intro i hi
  rw [dot_symm]

theorem scalar_factor (A : OBase α) (s t : Finset α) (x : Space α) (i : α) :
    (if i∈t then lum (dot (A.v i) x • A.v i) else 1) *
      (if i∈s then lum (dot (A.v i) x • A.v i) else 1)⁻¹ =
    (if i∈correctionSet A s t then sign (dot (A.v i) x) else 1) *
      (if i∈s ∆ t then tint (dot (A.v i) x) else 1) := by
  have hneg : (-Complex.I : ℂ)≠Complex.I := by
    intro h
    have H := congrArg Complex.im h
    norm_num at H
  have hpos : (Complex.I : ℂ)≠-Complex.I := Ne.symm hneg
  obtain h|h := lum_of_unit (A.v i) (A.self i)
  all_goals
    rcases bit_cases (dot (A.v i) x) with hd|hd <;>
      by_cases hs : i∈s <;> by_cases ht : i∈t <;>
      simp [hd,hs,ht,correctionSet,h,hneg,hpos,sign,tint,Finset.mem_symmDiff] <;> norm_num

theorem phase_ratio (A : OBase α) (s t : Finset α) (x : Space α) :
    lum (A.proj t x)*(lum (A.proj s x))⁻¹ =
      sign (dot (correction A s t) x)*forwardPhase A (s ∆ t) x := by
  rw [lum_proj_product A t x,lum_proj_product A s x,correction_phase A s t x]
  unfold forwardPhase
  rw [prod_subset t (fun i => lum (dot (A.v i) x • A.v i)),
    prod_subset s (fun i => lum (dot (A.v i) x • A.v i)),
    prod_subset (correctionSet A s t) (fun i => sign (dot (A.v i) x)),
    prod_subset (s ∆ t) (fun i => tint (dot (A.v i) x)),
    ← Finset.prod_inv_distrib,← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  exact scalar_factor A s t x i

/-- Exact whole-block factorization. Every negative or inverse direction
is included in the one explicitly charged translation. -/
theorem frame_ratio (A : OBase α) (s t : Finset α) :
    frame A t * unframe A s = shift (correction A s t) * forwardMask A (s ∆ t) := by
  rw [frame,unframe,wrap_mul,shift_phase,forwardMask,wrap_mul]
  apply congrArg wrap
  funext x
  exact phase_ratio A s t x

theorem amplified_ratio (A : OBase α) (s t : Finset α) (f : ℕ)
    (v : Sky α f → ℂ) :
    matAct f (frame A t * unframe A s) v =
      matAct f (shift (correction A s t)) (matAct f (forwardMask A (s ∆ t)) v) := by
  rw [frame_ratio,matAct_mul]

end
end FourierSchur.OriginalGroupedFrameFactorization
