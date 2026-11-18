import work_in_progress.OriginalStandardTensorExecutor
import MyProject.SchurAssembly

/-!
The existing paid upstream tensor program, on the project's exact dense
arbitrary-complex tensor target. Binary coordinate conversion is a semantic
identification of its already materialized array, not a free execution step.
The backend carries the actual uniform closed RAM syntax, charged work,
integer high-water mark and valid-run certificate. Its density is the
upstream power profile `hills`, not a polylogarithmic profile.
-/

namespace FourierSchur.OriginalCertifiedTensorBackend

open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty OriginalCompilerRootBridge OriginalSectorSubstitution
open scoped BigOperators
noncomputable section

def binaryAddress (k : Nat) : Bits k ≃ Fin (2^k) := (bits k).index

def bitAddress : F ≃ Fin 2 := lbit.index

theorem bitIndex_binaryAddress (k : Nat) (x : Bits k) (t : Fin k) :
    bitIndex (binaryAddress k x) t = bitAddress (x t) := by
  apply Fin.ext
  change (((bits k).loc x / 2^t.val) % 2) = (x t).val
  exact bits_div k x t

/-- The two formalizations use the same kernel at every binary coordinate. -/
theorem littleC_project (x y : F) :
    littleC x y = fourierKernel (bitAddress x) (bitAddress y) := by
  by_cases h : x = y
  · simp [littleC, fourierKernel, h, ca]
  · have hn : bitAddress x ≠ bitAddress y := fun he => h (bitAddress.injective he)
    simp [littleC, fourierKernel, h, hn, cb]

/-- Complete all-input equality, retaining all dense tensor coordinates. -/
theorem ripple_project (k : Nat) (f : Fin (2^k) → ℂ) (x : Bits k) :
    ripple k (f ∘ binaryAddress k) x =
      tensorAction k fourierKernel f (binaryAddress k x) := by
  change (∑ y : Bits k, kernel (Fin k) x y * f (binaryAddress k y)) =
    ∑ j : Fin (2^k), (∏ t : Fin k,
      fourierKernel (bitIndex (binaryAddress k x) t) (bitIndex j t)) * f j
  rw [← Equiv.sum_comp (binaryAddress k)]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  change (∏ t : Fin k, littleC (x t) (y t)) = _
  apply Finset.prod_congr rfl
  intro t _
  rw [bitIndex_binaryAddress, bitIndex_binaryAddress, littleC_project]

/-- The binary layout is already the project's ordinary dense array. -/
theorem input_tape_project (k : Nat) (f : Fin (2^k) → ℂ) :
    (bits k).tape (f ∘ binaryAddress k) = (⟨2^k,f⟩ : OAI.PowerSaving.Tape ℂ) := by
  unfold Layout.tape
  congr 1
  funext j
  exact congrArg f ((binaryAddress k).apply_symm_apply j)

theorem output_tape_project (k : Nat) (f : Fin (2^k) → ℂ) :
    (bits k).tape (ripple k (f ∘ binaryAddress k)) =
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ) := by
  have he : ripple k (f ∘ binaryAddress k) =
      tensorAction k fourierKernel f ∘ binaryAddress k := funext (ripple_project k f)
  rw [he, input_tape_project]

def denseInput (cl : Paint) (k : Nat) (f : Fin (2^k) → ℂ) :
    T (suppliedIn sc cl) := (k,Complex.I,parentRoot k,(⟨2^k,f⟩ : OAI.PowerSaving.Tape ℂ))

theorem suppliedInput_project (cl : Paint) (k : Nat) (f : Fin (2^k) → ℂ) :
    suppliedBits sc cl parentRoot k (f ∘ binaryAddress k) = denseInput cl k f := by
  simp only [suppliedBits, denseInput, input_tape_project]

/-- A genuine finite uniform RAM program with all of its paid obligations. -/
structure Certified (cl : Paint) (m : Bool) where
  program : Prog m (suppliedIn sc cl) (bundle cl)
  costConstant : Nat
  wordDegree : Nat
  guarantee : ∀ (k : Nat) (f : Fin (2^k) → ℂ),
    (run program (denseInput cl k f)).OK
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ)
      (costConstant*(2^k*hills k+1)) ((2^k+2)^wordDegree)

/-- This is inhabited by the checked network/recursion algorithm, with no
new tensor-execution hypothesis. Preparation and routing remain in its bill. -/
theorem certified_exists (cl : Paint) (m : Bool) : Nonempty (Certified cl m) := by
  obtain ⟨program,C,d,h⟩ := Can.unfold_bound
    (OriginalStandardTensorExecutor.standard_supplied cl m)
  refine ⟨⟨program,C,d,?_⟩⟩
  intro k f
  have hx := h (⟨k,f ∘ binaryAddress k⟩ : TensorInput)
  change (run program (suppliedBits sc cl parentRoot k (f ∘ binaryAddress k))).OK
    ((bits k).tape (ripple k (f ∘ binaryAddress k)))
    (C*(2^k*hills k+1)) ((2^k+2)^d) at hx
  rw [suppliedInput_project, output_tape_project] at hx
  exact hx

def backend (cl : Paint) (m : Bool) : Certified cl m := Classical.choice (certified_exists cl m)

theorem backend_guarantee (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (backend cl m).program (denseInput cl k f)).OK
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ)
      ((backend cl m).costConstant*(2^k*hills k+1))
      ((2^k+2)^(backend cl m).wordDegree) := (backend cl m).guarantee k f

theorem backend_work_bound (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (backend cl m).program (denseInput cl k f)).work ≤
      (backend cl m).costConstant*(2^k*hills k+1) :=
  (backend_guarantee cl m k f).time

theorem backend_output (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (backend cl m).program (denseInput cl k f)).val =
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ) :=
  (backend_guarantee cl m k f).result

theorem backend_reads_project (cl : Paint) (m : Bool) (k : Nat)
    (f : Fin (2^k) → ℂ) (i : Fin (2^k)) :
    (run (backend cl m).program (denseInput cl k f)).val.look i.val 0 =
      tensorAction k fourierKernel f i := by
  rw [backend_output, OAI.PowerSaving.Tape.look_of_lt _ _ i.is_lt]

/-- The selected actual dense backend itself inhabits the compiler's
supplied executor contract, rather than only identifying its matrix. -/
theorem backend_supplied (cl : Paint) (m : Bool) :
    SuppliedTensorExecutor sc parentRoot cl m hills := by
  refine ⟨(backend cl m).program, (backend cl m).costConstant,
    (backend cl m).wordDegree, ?_⟩
  intro input
  let k := input.1
  let v := input.2
  let f : Fin (2^k) → ℂ := v ∘ (binaryAddress k).symm
  have hv : f ∘ binaryAddress k = v := by
    funext x
    exact congrArg v ((binaryAddress k).symm_apply_apply x)
  have ha := backend_guarantee cl m k f
  rw [← suppliedInput_project, ← output_tape_project, hv] at ha
  simpa [Bank.cap, Bank.closed] using ha

theorem backend_valid (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (backend cl m).program (denseInput cl k f)).valid :=
  (backend_guarantee cl m k f).valid

theorem wordCap_le_two_pow (k d : Nat) : (2^k+2)^d ≤ 2^((k+2)*d) := by
  have hk : 1 ≤ 2^k := Nat.one_le_pow k 2 (by omega)
  have hb : 2^k+2 ≤ 2^(k+2) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _ ≤ (2^(k+2))^d := Nat.pow_le_pow_left hb d
    _ = _ := by rw [pow_mul]

theorem backend_word_bound (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (backend cl m).program (denseInput cl k f)).peak ≤
      2^((k+2)*(backend cl m).wordDegree) :=
  (backend_guarantee cl m k f).bound.trans (wordCap_le_two_pow _ _)

/-- Honest quantitative improvement from the existing complex algorithm. -/
theorem paid_power_bound (C k : Nat) :
    (C*(2^k*hills k+1) : ℝ) ≤
      C*(2*2^k*((k : ℝ)+1)^alpha+1) := by
  have hh := hills_real k
  have hp : (0 : ℝ) ≤ (2 : ℝ)^k := by positivity
  have hc : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  have hm : (2 : ℝ)^k*(hills k : ℝ) ≤ (2 : ℝ)^k*(2*((k : ℝ)+1)^alpha) :=
    mul_le_mul_of_nonneg_left hh hp
  have hs : (2 : ℝ)^k*(hills k : ℝ)+1 ≤ (2 : ℝ)^k*(2*((k : ℝ)+1)^alpha)+1 := by
    linarith
  calc
    _ ≤ (C : ℝ)*((2 : ℝ)^k*(2*((k : ℝ)+1)^alpha)+1) :=
      mul_le_mul_of_nonneg_left hs hc
    _ = _ := by ring

/-- The original executor's only supplied scalar is the fixed value I.
There is no root register or coefficient table in this input type. -/
def rawInput (cl : Paint) (k : Nat) (f : Fin (2^k) → ℂ) : T (simIn cl) :=
  (k,Complex.I,(⟨2^k,f⟩ : OAI.PowerSaving.Tape ℂ))

theorem rawInput_project (cl : Paint) (k : Nat) (f : Fin (2^k) → ℂ) :
    givenBits cl k (f ∘ binaryAddress k) = rawInput cl k f := by
  simp only [givenBits, rawInput, input_tape_project]

/-- Profile-independent dense certificate. Both the historical backend and
the stronger census backend use this same conversion of the already
materialized binary tape; no additional execution or uncharged permutation
is inserted. The complete native RAM bill remains in `guarantee`. -/
structure RawCertifiedFor (profile : Nat → Nat) (cl : Paint) (m : Bool) where
  program : Prog m (simIn cl) (bundle cl)
  costConstant : Nat
  wordDegree : Nat
  guarantee : ∀ (k : Nat) (f : Fin (2^k) → ℂ),
    (run program (rawInput cl k f)).OK
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ)
      (costConstant*(2^k*profile k+1)) ((2^k+2)^wordDegree)

/-- The sole binary-to-dense certificate adapter, for any proved profile. -/
theorem rawCertified_of_complete {profile : Nat → Nat} {cl : Paint} {m : Bool}
    (executor : CompleteTensorExecutor cl m profile) :
    Nonempty (RawCertifiedFor profile cl m) := by
  obtain ⟨program,C,d,h⟩ := Can.unfold_bound executor
  refine ⟨⟨program,C,d,?_⟩⟩
  intro k f
  have hx := h (⟨k,f ∘ binaryAddress k⟩ : TensorInput)
  change (run program (givenBits cl k (f ∘ binaryAddress k))).OK
    ((bits k).tape (ripple k (f ∘ binaryAddress k)))
    (C*(2^k*profile k+1)) ((2^k+2)^d) at hx
  rw [rawInput_project, output_tape_project] at hx
  exact hx

/-- A dense certificate is the same compiler contract at the same cost. -/
theorem RawCertifiedFor.complete {profile : Nat → Nat} {cl : Paint} {m : Bool}
    (certificate : RawCertifiedFor profile cl m) :
    CompleteTensorExecutor cl m profile := by
  refine ⟨certificate.program, certificate.costConstant,
    certificate.wordDegree, ?_⟩
  intro input
  let k := input.1
  let v := input.2
  let f : Fin (2^k) → ℂ := v ∘ (binaryAddress k).symm
  have hv : f ∘ binaryAddress k = v := by
    funext x
    exact congrArg v ((binaryAddress k).symm_apply_apply x)
  have ha := certificate.guarantee k f
  rw [← rawInput_project, ← output_tape_project, hv] at ha
  simpa [Bank.cap, Bank.closed] using ha

/-- Compatibility structure for existing clients of the historical `hills`
backend. New backends use `RawCertifiedFor` instead of duplicating adapters. -/
structure RawCertified (cl : Paint) (m : Bool) where
  program : Prog m (simIn cl) (bundle cl)
  costConstant : Nat
  wordDegree : Nat
  guarantee : ∀ (k : Nat) (f : Fin (2^k) → ℂ),
    (run program (rawInput cl k f)).OK
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ)
      (costConstant*(2^k*hills k+1)) ((2^k+2)^wordDegree)

/-- All coefficient construction, network execution and full output copying
are inside this I-only program's billed execution. -/
theorem rawCertified_exists (cl : Paint) (m : Bool) : Nonempty (RawCertified cl m) := by
  obtain ⟨certificate⟩ := rawCertified_of_complete
    (OriginalStandardTensorExecutor.standard_complete cl m)
  exact ⟨⟨certificate.program, certificate.costConstant,
    certificate.wordDegree, certificate.guarantee⟩⟩

def rawBackend (cl : Paint) (m : Bool) : RawCertified cl m :=
  Classical.choice (rawCertified_exists cl m)

theorem rawBackend_guarantee (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (rawBackend cl m).program (rawInput cl k f)).OK
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ)
      ((rawBackend cl m).costConstant*(2^k*hills k+1))
      ((2^k+2)^(rawBackend cl m).wordDegree) := (rawBackend cl m).guarantee k f

theorem rawBackend_work_bound (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (rawBackend cl m).program (rawInput cl k f)).work ≤
      (rawBackend cl m).costConstant*(2^k*hills k+1) :=
  (rawBackend_guarantee cl m k f).time

theorem rawBackend_output (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (rawBackend cl m).program (rawInput cl k f)).val =
      (⟨2^k,tensorAction k fourierKernel f⟩ : OAI.PowerSaving.Tape ℂ) :=
  (rawBackend_guarantee cl m k f).result

theorem rawBackend_valid (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (rawBackend cl m).program (rawInput cl k f)).valid :=
  (rawBackend_guarantee cl m k f).valid

theorem rawBackend_word_bound (cl : Paint) (m : Bool) (k : Nat) (f : Fin (2^k) → ℂ) :
    (run (rawBackend cl m).program (rawInput cl k f)).peak ≤
      2^((k+2)*(rawBackend cl m).wordDegree) :=
  (rawBackend_guarantee cl m k f).bound.trans (wordCap_le_two_pow _ _)

theorem rawBackend_complete (cl : Paint) (m : Bool) :
    CompleteTensorExecutor cl m hills :=
  RawCertifiedFor.complete
    ⟨(rawBackend cl m).program, (rawBackend cl m).costConstant,
      (rawBackend cl m).wordDegree, rawBackend_guarantee cl m⟩

end
end FourierSchur.OriginalCertifiedTensorBackend
