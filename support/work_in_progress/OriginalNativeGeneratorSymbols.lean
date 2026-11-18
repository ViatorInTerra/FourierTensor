import work_in_progress.OriginalCheckedNativeDirection
import work_in_progress.OriginalNativeComplementClosure

/-! Small exact symbols for the actual native bank DAG. The only relations
are commutativity and a generator square equal to its direction translation.
The representation has no quadratic-matrix or sampled-frequency premise.
-/
namespace FourierSchur.OriginalNativeGeneratorSymbols
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalBinaryMatrixCertificates
noncomputable section

structure Tag where
  mask : ℕ
  offset : ℕ
  deriving DecidableEq, Repr

def unitTag : Tag := ⟨0,0⟩

def xorWords : List ℕ → ℕ
  | [] => 0
  | w::ws => w ^^^ xorWords ws

def carry {k : ℕ} (directions : Fin k → ℕ) (a b : ℕ) : ℕ :=
  xorWords (List.ofFn (fun i : Fin k =>
    if a.testBit i.val && b.testBit i.val then directions i else 0))

def compose {k : ℕ} (directions : Fin k → ℕ) (a b : Tag) : Tag :=
  ⟨a.mask ^^^ b.mask,a.offset ^^^ b.offset ^^^ carry directions a.mask b.mask⟩

def character (n z : ℕ) (x : Space (Fin n)) : ℂ :=
  sign (dot (wordVector n z) x)

theorem wordVector_xor (n a b : ℕ) :
    wordVector n (a ^^^ b)=wordVector n a+wordVector n b := by
  funext i
  simp only [wordVector,← bitValue_div,Pi.add_apply]
  cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;>
    norm_num [bitValue,Nat.testBit_xor,ha,hb]

theorem character_zero (n : ℕ) (x : Space (Fin n)) : character n 0 x=1 := by
  simp [character,wordVector,sign,dot]

theorem character_xor (n a b : ℕ) (x : Space (Fin n)) :
    character n (a ^^^ b) x=character n a x*character n b x := by
  simp only [character,wordVector_xor,dot,Pi.add_apply,add_mul,
    Finset.sum_add_distrib,sign_add]

theorem character_square (n z : ℕ) (x : Space (Fin n)) :
    character n z x*character n z x=1 := sign_sq _

theorem character_xorWords (n : ℕ) (ws : List ℕ) (x : Space (Fin n)) :
    character n (xorWords ws) x=(ws.map (fun w => character n w x)).prod := by
  induction ws with
  | nil => exact character_zero n x
  | cons w ws ih => simp only [xorWords,character_xor,ih,List.map_cons,List.prod_cons]

theorem character_carry {n k : ℕ} (directions : Fin k → ℕ) (a b : ℕ)
    (x : Space (Fin n)) :
    character n (carry directions a b) x=
      ∏ i : Fin k,if a.testBit i.val && b.testBit i.val then
        character n (directions i) x else 1 := by
  rw [carry,character_xorWords,List.map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;>
    simp [ha,hb,character_zero]

def value {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (a : Tag) (x : Space (Fin n)) : ℂ :=
  character n a.offset x * ∏ i : Fin k,if a.mask.testBit i.val then generators i x else 1

theorem value_unit {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (x : Space (Fin n)) : value generators unitTag x=1 := by
  simp [value,unitTag,character_zero]

/-- Exact multiplication for every frequency, using only the proved
square-to-translation law of each native generator. -/
theorem value_compose {n k : ℕ} (directions : Fin k → ℕ)
    (generators : Fin k → Space (Fin n) → ℂ)
    (hs : ∀ i x,generators i x*generators i x=character n (directions i) x)
    (a b : Tag) (x : Space (Fin n)) :
    value generators (compose directions a b) x=value generators a x*value generators b x := by
  have hpair (i : Fin k) :
      (if a.mask.testBit i.val then generators i x else 1)*
        (if b.mask.testBit i.val then generators i x else 1)=
      (if (a.mask ^^^ b.mask).testBit i.val then generators i x else 1)*
        (if a.mask.testBit i.val && b.mask.testBit i.val then
          character n (directions i) x else 1) := by
    cases ha : a.mask.testBit i.val <;> cases hb : b.mask.testBit i.val <;>
      simp [Nat.testBit_xor,ha,hb,hs]
  have hp : (∏ i : Fin k,if a.mask.testBit i.val then generators i x else 1)*
      (∏ i : Fin k,if b.mask.testBit i.val then generators i x else 1)=
      (∏ i : Fin k,if (a.mask ^^^ b.mask).testBit i.val then generators i x else 1)*
      (∏ i : Fin k,if a.mask.testBit i.val && b.mask.testBit i.val then
        character n (directions i) x else 1) := by
    rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hpair i)
  simp only [value,compose,character_xor,character_carry]
  rw [show character n a.offset x *
      (∏ i : Fin k,if a.mask.testBit i.val then generators i x else 1)*
      (character n b.offset x *
        ∏ i : Fin k,if b.mask.testBit i.val then generators i x else 1)=
      (character n a.offset x*character n b.offset x)*
      ((∏ i : Fin k,if a.mask.testBit i.val then generators i x else 1)*
        (∏ i : Fin k,if b.mask.testBit i.val then generators i x else 1)) by ring]
  rw [hp]
  ring

def operator {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ) (a : Tag) :
    CMat (Fin n) := wrap (value generators a)

theorem operator_compose {n k : ℕ} (directions : Fin k → ℕ)
    (generators : Fin k → Space (Fin n) → ℂ)
    (hs : ∀ i x,generators i x*generators i x=character n (directions i) x)
    (a b : Tag) :
    operator generators (compose directions a b)=operator generators a*operator generators b := by
  rw [operator,operator,operator,wrap_mul]
  congr 1
  funext x
  exact value_compose directions generators hs a b x

end
end FourierSchur.OriginalNativeGeneratorSymbols
