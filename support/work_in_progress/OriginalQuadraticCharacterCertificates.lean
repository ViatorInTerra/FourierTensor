import work_in_progress.OriginalAffineFourierConjugacy

/-!
Polynomial-size certificates for the whole quadratic Fourier symbol.
The equality proof uses its polar form and coordinate-basis values; it does
not test or enumerate the exponentially many Fourier frequencies.
These are finite algebraic facts needed to import the emitted adapters.
-/
namespace FourierSchur.OriginalQuadraticCharacterCertificates
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

structure Character (α : Type*) [Fintype α] [DecidableEq α] where
  value : Space α→ℂ
  polar : Matrix α α F
  at_zero : value 0=1
  add : ∀ x y,value (x+y)=value x*value y*sign (dot x (polar.mulVec y))

theorem outer_dot (v w x y : Space α) :
    dot x ((Matrix.vecMulVec v w).mulVec y)=dot x v*dot w y := by
  rw [Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul]
  change dot x ((dot w y) • v)=_
  rw [dot_smul_right]
  ring

theorem sign_pow (n : ℕ) (x : F) : sign x^n=sign ((n:F)*x) := by
  induction n with
  | zero => simp [sign]
  | succ n ih =>
    rw [pow_succ,ih]
    simp [Nat.cast_add,add_mul,sign_add]

def unary (v : Space α) (n : ℕ) : Character α where
  value x := tint (dot v x)^n
  polar := Matrix.vecMulVec ((n:F) • v) v
  at_zero := by simp [tint]
  add x y := by
    rw [dot_add_right,tint_add,mul_pow,mul_pow,sign_pow,outer_dot,dot_smul_right]
    rw [dot_symm x v]
    congr 1
    congr 1
    ring

def linear (k : Space α) : Character α where
  value x := sign (dot k x)
  polar := 0
  at_zero := by simp [sign]
  add x y := by
    rw [dot_add_right,sign_add]
    simp [sign]

def cross (v w : Space α) : Character α where
  value x := sign (dot v x*dot w x)
  polar := Matrix.vecMulVec v w+Matrix.vecMulVec w v
  at_zero := by simp [sign]
  add x y := by
    simp only [Matrix.add_mulVec,dot_add_right,outer_dot]
    have he : (dot v x+dot v y)*(dot w x+dot w y)=
        dot v x*dot w x+dot v y*dot w y+
          (dot x v*dot w y+dot x w*dot v y) := by
      rw [dot_symm x v,dot_symm x w]
      ring
    rw [he,sign_add,sign_add]

def one : Character α where
  value _ := 1
  polar := 0
  at_zero := rfl
  add x y := by simp [sign]

def mul (a b : Character α) : Character α where
  value x := a.value x*b.value x
  polar := a.polar+b.polar
  at_zero := by rw [a.at_zero,b.at_zero,mul_one]
  add x y := by
    rw [a.add,b.add,Matrix.add_mulVec,dot_add_right,sign_add]
    ring

def product {δ : Type*} (s : Finset δ) (c : δ→Character α) : Character α where
  value x := ∏ i∈s,(c i).value x
  polar := ∑ i∈s,(c i).polar
  at_zero := by simp only [(c _).at_zero,prod_const_one]
  add x y := by
    classical
    induction s using Finset.induction with
    | empty => simp [sign]
    | insert i s hi ih =>
      simp only [prod_insert hi,sum_insert hi]
      rw [(c i).add,ih,Matrix.add_mulVec,dot_add_right,sign_add]
      ring

theorem transpose_polar_dot (W B : Matrix α α F) (x y : Space α) :
    dot (W.mulVec x) (B.mulVec (W.mulVec y))=
      dot x ((W.transpose*B*W).mulVec y) := by
  change (W.mulVec x) ⬝ᵥ (B.mulVec (W.mulVec y))=
    x ⬝ᵥ ((W.transpose*B*W).mulVec y)
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,dotProduct_comm,
    ← Matrix.mulVec_transpose]
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]

def pull (c : Character α) (W : Matrix α α F) : Character α where
  value x := c.value (W.mulVec x)
  polar := W.transpose*c.polar*W
  at_zero := by simp [c.at_zero]
  add x y := by
    rw [Matrix.mulVec_add,c.add,transpose_polar_dot]

/-- Two quadratic refinements of the SAME polar form are equal on every
frequency once they agree at zero and on the coordinate basis. -/
theorem value_ext (a b : Character α) (hp : a.polar=b.polar)
    (he : ∀ i,a.value (eu i)=b.value (eu i)) : a.value=b.value := by
  have hs (i : α) (t : F) : a.value (t • eu i)=b.value (t • eu i) := by
    rcases bit_cases t with rfl|rfl
    · simp [a.at_zero,b.at_zero]
    · simpa using he i
  have hf (s : Finset α) (v : Space α) :
      a.value (∑ i∈s,v i • eu i)=b.value (∑ i∈s,v i • eu i) := by
    induction s using Finset.induction with
    | empty => simp [a.at_zero,b.at_zero]
    | insert i s hi ih =>
      rw [sum_insert hi,a.add,b.add,hs,ih,hp]
  funext v
  have hv : (∑ i : α,v i • eu i)=v := by
    funext j
    simp [eu,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simpa only [hv] using hf univ v

/-- The finite congruence and unary-value checks suffice to replace the
previous full-function symbol hypothesis in the adapter interface. -/
theorem pull_value_certificate (a b : Character α) (W : Matrix α α F)
    (hp : W.transpose*a.polar*W=b.polar)
    (he : ∀ i,a.value (W.mulVec (eu i))=b.value (eu i)) (v : Space α) :
    a.value (W.mulVec v)=b.value v :=
  congr_fun (value_ext (pull a W) b hp he) v

theorem value_nonzero (a : Character α) (x : Space α) : a.value x≠0 := by
  intro hz
  have H := a.add x x
  rw [binary_cancel,a.at_zero,hz,zero_mul,zero_mul] at H
  exact one_ne_zero H

end
end FourierSchur.OriginalQuadraticCharacterCertificates
