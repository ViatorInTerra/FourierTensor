import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Rat
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-! Replay a shared scalar preparation DAG at conjugate supplied roots.
Registers are retained and may be reused. Replay uses the same instructions
and preserves every nonzero denominator of the original preparation. -/
namespace FourierSchur.ConstantPreparation
noncomputable section

inductive Tape : Type → Type → Type 1 where
  | done {α β} (outputs : β → α) : Tape α β
  | rational {α β} (q : ℚ) (rest : Tape (Option α) β) : Tape α β
  | add {α β} (a b : α) (rest : Tape (Option α) β) : Tape α β
  | mul {α β} (a b : α) (rest : Tape (Option α) β) : Tape α β
  | inv {α β} (a : α) (rest : Tape (Option α) β) : Tape α β

def extend {α : Type} (x : α → ℂ) (v : ℂ) : Option α → ℂ := fun i => i.elim v x

def run {α β : Type} : Tape α β → (α → ℂ) → (β → ℂ)
  | .done f,x => x ∘ f
  | .rational q rest,x => run rest (extend x (q:ℂ))
  | .add a b rest,x => run rest (extend x (x a+x b))
  | .mul a b rest,x => run rest (extend x (x a*x b))
  | .inv a rest,x => run rest (extend x (x a)⁻¹)

def operations {α β : Type} : Tape α β → Nat
  | .done _ => 0
  | .rational _ rest => 1+operations rest
  | .add _ _ rest => 1+operations rest
  | .mul _ _ rest => 1+operations rest
  | .inv _ rest => 1+operations rest

def DenominatorsNonzero {α β : Type} : Tape α β → (α → ℂ) → Prop
  | .done _,_ => True
  | .rational q rest,x => DenominatorsNonzero rest (extend x (q:ℂ))
  | .add a b rest,x => DenominatorsNonzero rest (extend x (x a+x b))
  | .mul a b rest,x => DenominatorsNonzero rest (extend x (x a*x b))
  | .inv a rest,x => x a≠0 ∧ DenominatorsNonzero rest (extend x (x a)⁻¹)

theorem extend_star {α : Type} (x : α → ℂ) (v : ℂ) :
    extend (fun i => star (x i)) (star v)=fun i => star (extend x v i) := by
  funext i
  cases i <;> rfl

theorem conjugate_correct {α β : Type} (p : Tape α β) (x : α → ℂ) :
    run p (fun i => star (x i))=fun j => star (run p x j) := by
  induction p with
  | done f => rfl
  | rational q rest ih =>
    simp only [run]
    have he : extend (fun i => star (x i)) (q:ℂ)=fun i => star (extend x (q:ℂ) i) := by
      simpa only [star_ratCast] using extend_star x (q:ℂ)
    rw [he,ih]
  | add a b rest ih =>
    simp only [run]
    rw [← star_add,extend_star,ih]
  | mul a b rest ih =>
    simp only [run]
    have hm : star (x a)*star (x b)=star (x a*x b) := by rw [star_mul,mul_comm]
    rw [hm,extend_star,ih]
  | inv a rest ih =>
    simp only [run]
    rw [← star_inv₀,extend_star,ih]

theorem conjugate_denominators {α β : Type} (p : Tape α β) (x : α → ℂ)
    (h : DenominatorsNonzero p x) : DenominatorsNonzero p (fun i => star (x i)) := by
  induction p with
  | done f => trivial
  | rational q rest ih =>
    simp only [DenominatorsNonzero] at h ⊢
    have he : extend (fun i => star (x i)) (q:ℂ)=fun i => star (extend x (q:ℂ) i) := by
      simpa only [star_ratCast] using extend_star x (q:ℂ)
    rw [he]
    exact ih _ h
  | add a b rest ih =>
    simp only [DenominatorsNonzero] at h ⊢
    rw [← star_add,extend_star]
    exact ih _ h
  | mul a b rest ih =>
    simp only [DenominatorsNonzero] at h ⊢
    have hm : star (x a)*star (x b)=star (x a*x b) := by rw [star_mul,mul_comm]
    rw [hm,extend_star]
    exact ih _ h
  | inv a rest ih =>
    simp only [DenominatorsNonzero] at h ⊢
    constructor
    · simpa using h.1
    · rw [← star_inv₀,extend_star]
      exact ih _ h.2

theorem inverse_root_replay {α β : Type} (p : Tape α β) (roots : α → ℂ)
    (hroots : ∀ i,star (roots i)=(roots i)⁻¹) :
    run p (fun i => (roots i)⁻¹)=fun j => star (run p roots j) := by
  have he : (fun i => (roots i)⁻¹)=fun i => star (roots i) := by
    funext i
    exact (hroots i).symm
  rw [he,conjugate_correct]

theorem inverse_root_denominators {α β : Type} (p : Tape α β) (roots : α → ℂ)
    (hroots : ∀ i,star (roots i)=(roots i)⁻¹) (h : DenominatorsNonzero p roots) :
    DenominatorsNonzero p (fun i => (roots i)⁻¹) := by
  have he : (fun i => (roots i)⁻¹)=fun i => star (roots i) := by
    funext i
    exact (hroots i).symm
  rw [he]
  exact conjugate_denominators p roots h

theorem root_star_inverse (z : ℂ) (n : Nat) (hn : 0<n) (hroot : z^n=1) : star z=z⁻¹ := by
  have hs : Complex.normSq z^n=(1:ℝ)^n := by
    rw [← map_pow,hroot,map_one,one_pow]
  have hsq : Complex.normSq z=1 :=
    (pow_left_inj₀ (Complex.normSq_nonneg z) zero_le_one (Nat.ne_of_gt hn)).mp hs
  have hm : z*star z=1 := by
    rw [Complex.star_def,Complex.mul_conj,hsq]
    rfl
  have hz : z≠0 := by
    intro h
    rw [h,zero_mul] at hm
    exact zero_ne_one hm
  apply mul_left_cancel₀ hz
  rw [hm,mul_inv_cancel₀ hz]

theorem supplied_root_replay {α β : Type} (p : Tape α β) (roots : α → ℂ)
    (order : α → Nat) (horder : ∀ i,0<order i) (hroots : ∀ i,roots i^order i=1) :
    run p (fun i => (roots i)⁻¹)=fun j => star (run p roots j) :=
  inverse_root_replay p roots (fun i => root_star_inverse _ _ (horder i) (hroots i))

theorem supplied_root_denominators {α β : Type} (p : Tape α β) (roots : α → ℂ)
    (order : α → Nat) (horder : ∀ i,0<order i) (hroots : ∀ i,roots i^order i=1)
    (h : DenominatorsNonzero p roots) : DenominatorsNonzero p (fun i => (roots i)⁻¹) :=
  inverse_root_denominators p roots (fun i => root_star_inverse _ _ (horder i) (hroots i)) h

end
end FourierSchur.ConstantPreparation
